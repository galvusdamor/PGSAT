#include "partially_grounded_sat.h"
#include "sat_encoder.h"
#include "sat_termination.h"
#include "ipasir.h"
#include "../action.h"
#include "../search_engines/utils.h"
#include <unordered_set>
#include <cassert>
#include <chrono>
#include <iomanip>

#include "pddl/pddl.h"
#include "src/internal.h"

extern "C"
{
void pddl_bliss_new_digraph(){}
void pddl_bliss_release(){}
void pddl_bliss_add_vertex(){}
void pddl_bliss_add_edge(){}
void pddl_bliss_find_automorphisms(){}
}

static const char* root_type_cppdl = "__object_cpddl";

using namespace std;

#define timesplit(name) {clock_t _end=clock();timings[name]+=1000.0*(_end-_start)/CLOCKS_PER_SEC; _start=_end;}
#define PRECPROCESSING "preprocessing"
#define SATSOLVER "sat solver"

struct obj_key {
    int obj_id;
    const char *name;
    uint32_t hash;
    pddl_list_t htable;
};
typedef struct obj_key obj_key_t;

static pddl_htable_key_t objHash(const pddl_list_t *key, void *_)
{
    const obj_key_t *obj = pddl_container_of(key, obj_key_t, htable);
    return obj->hash;
}

static int objEq(const pddl_list_t *key1, const pddl_list_t *key2, void *_)
{
    const obj_key_t *obj1 = pddl_container_of(key1, obj_key_t, htable);
    const obj_key_t *obj2 = pddl_container_of(key2, obj_key_t, htable);
    return strcmp(obj1->name, obj2->name) == 0;
}

int increase(vector<int> lower, vector<int> upper, vector<int> &current, int index){
    if(index < 0){
        return 0;
    }
    if(current[index]+1 <= upper[index]){
        current[index] += 1;
        return 1;
    }else{
        current[index] = lower[index];
        return increase(lower, upper, current, index-1);
    }
}

void generateCombinations(const vector<vector<int>>& input, vector<int>& current, int depth, vector<vector<int>>& result) {
    // If the current combination has elements from all vectors, add it to the result
    if (depth == input.size()) {
        result.push_back(current);
        return;
    }

    // Iterate through each element in the current vector
    for (int i = 0; i < input[depth].size(); ++i) {
        current[depth] = input[depth][i]; // Choose an element from the current vector
        generateCombinations(input, current, depth + 1, result); // Move to the next vector
    }
}

// Wrapper function to call the recursive function and initiate the process
vector<vector<int>> getCombinations(const vector<vector<int>>& input) {
    vector<vector<int>> result;
    if (input.empty()) return result; // If input is empty, return an empty result

    vector<int> current(input.size()); // Placeholder for the current combination
    generateCombinations(input, current, 0, result); // Start recursive generation
    return result;
}

bool is_mutex_group_contained_in_assignement(pddl_lifted_mgroup_t * m1, pddl_lifted_mgroup_t *m2, std::vector<int> & m1VarTom2Var, std::vector<bool> & m2VarAssigned, pddl_t * pddl, int pos = 0){

	if (pos == m1VarTom2Var.size()){
		DEBUG(std::cout << "Assignment:";
		for (size_t m1V = 0; m1V < m1VarTom2Var.size(); m1V++)
			std::cout << " " << m1V << " -> " << m1VarTom2Var[m1V];
		std::cout << std::endl;);


		// we have to search for every condition in m1 a mirror partner in m2
		for (size_t m1i = 0; m1i < m1->cond.size; m1i++){
			bool matchFound = false;
			for (size_t m2i = 0; !matchFound && m2i < m2->cond.size; m2i++){
				// get both atoms
                const pddl_fm_atom_t *a1 = pddlFmToAtomConst(m1->cond.fm[m1i]);
                const pddl_fm_atom_t *a2 = pddlFmToAtomConst(m2->cond.fm[m2i]);

				// must have the same predicate
				if (a1->pred != a2->pred) continue;

				bool paramsMatch = true;
				// iterate through the parameters
				for (size_t param = 0; paramsMatch && param < a1->arg_size; param++){
					// get both parameters
					pddl_fm_atom_arg_t *p1 = a1->arg + param;
					pddl_fm_atom_arg_t *p2 = a2->arg + param;

					// cases
					if (p1->param < 0){
						// parameter p1 of a1 is a constant
						if (p2->param < 0) {
							// p2 is also a constant
							if (p1->obj != p2->obj){
								paramsMatch = false;
								break;
							} // else ok
						} else {
							// p2 is a variable
							const pddl_param_t *v2 = m2->param.param + p2->param;
							//pddl_type_t * t2 = pddl->type.type[v2->type];
							if (!pddlTypesObjHasType(&(pddl->type), v2->type,
										p1->obj)){
								paramsMatch = false;
								break;
							} // else object is in type, so ok
						}
					} else {
						// super mutex cannot have a constant here
						if (p2->param < 0){
							paramsMatch = false;
							break;
						}
						
						// test whether the variable of m1 is mapped to the one of m2
						if (m1VarTom2Var[p1->param] != p2->param){
							paramsMatch = false;
							break;
						}

						// mapped to the same variable so ok.
					}
				}
				if (paramsMatch) {
					matchFound = true;
					DEBUG(std::cout << "Match for " << m1i << " is " << m2i << std::endl);
				}
			}

			if (! matchFound) {
				DEBUG(std::cout << "Conjunct " << m1i << " has no match " << std::endl);
				return false;
			}
		
		}
	
		// here we have found a match for every condition	
		DEBUG(std::cout << "Given m1 is a sub-mutex of m2." << std::endl);
		return true;
	}

	// iterate through all possible remaining variables
	for (size_t m2Var = 0; m2Var < m2VarAssigned.size(); m2Var++){
		if (m2VarAssigned[m2Var]) continue;
						
		const pddl_param_t *v1 = m1->param.param + pos;
		const pddl_param_t *v2 = m2->param.param + m2Var;

		// we cannot map a counted var to an uncounted one ...
		if (v1->is_counted_var && !v2->is_counted_var)
			continue;

		// situation is either (C,C), (V,V) or (V,C)
		// in any case now m2 is at least as strong if the types are subtypes of each other (i.e. v1->type \subseteq v2->type)
		if (v1->type != v2->type)
			if (!pddlTypesIsParent(&(pddl->type),v1->type,v2->type))
				continue;


		// try is
		m1VarTom2Var[pos] = m2Var;
		m2VarAssigned[m2Var] = true;
		if (is_mutex_group_contained_in_assignement(m1,m2,m1VarTom2Var,m2VarAssigned,pddl,pos+1))
			return true;
		m2VarAssigned[m2Var] = false;
	}


	return false;
}



// tests whether the mgroup m1 is fully contained in m2
bool is_mutex_group_contained_in(pddl_lifted_mgroup_t * m1, pddl_lifted_mgroup_t *m2, pddl_t * pddl){
	// if m1 has *more* parameters it cannot be a subset of m2
	if (m1->param.param_size > m2->param.param_size)
		return false;

	std::vector<int>  m1VarTom2Var  (m1->param.param_size);
	std::vector<bool> m2VarAssigned (m2->param.param_size);

	return is_mutex_group_contained_in_assignement(m1,m2,m1VarTom2Var,m2VarAssigned,pddl);
} 



map<int,map<int,map<int,map<int,map<int, map<int, map<vector<int>,int>>>>>>> equals_var_map;
map<int,map<pair<int, int>, int>> countedOfType;

int PartiallyGroundedSAT::get_equals_var(void* solver, sat_capsule & capsule, int time_action, int time_state, int action_argument_position,
                    int FAM_group, int param_id, vector<int> free_variable_grounding, int counted_var,
                    const vector<int> & counted_var_objects, int counted_var_type, const vector<map<int,int>> & parameterVars){
    if (equals_var_map[time_action][time_state][action_argument_position][FAM_group][param_id][counted_var].count(free_variable_grounding))
        return equals_var_map[time_action][time_state][action_argument_position][FAM_group][param_id][counted_var][free_variable_grounding];

    int newVar = capsule.new_variable();
    // registering
    equals_var_map[time_action][time_state][action_argument_position][FAM_group][param_id][counted_var][free_variable_grounding] = newVar;

    for(int object = lowerTypeindex[typeOfArgument[action_argument_position]] ; object <= upperTypeindex[typeOfArgument[action_argument_position]] ; object++){
        if (object < lowerTypeindex[counted_var_type]) continue;
        if (object > upperTypeindex[counted_var_type]) continue;
        int parameterObject =  parameterVars[action_argument_position].at(object);
        andImplies(solver, newVar, parameterObject, counted_var_objects[object - lowerTypeindex[counted_var_type]]);
        andImplies(solver, newVar, counted_var_objects[object - lowerTypeindex[counted_var_type]], parameterObject);
        andImplies(solver, counted_var_objects[object - lowerTypeindex[counted_var_type]], parameterObject, newVar);
    }

    return newVar;
}

int PartiallyGroundedSAT::get_counted_of_type_var(void* solver, sat_capsule & capsule, int time_step, int action_argument_position, int type, const vector<map<int,int>> & parameterVars){
    if (countedOfType[time_step].count({action_argument_position,type}))
        return countedOfType[time_step][{action_argument_position,type}];

    int newVar = capsule.new_variable();
    // registering
    countedOfType[time_step][{action_argument_position,type}] = newVar;


    for(int object = lowerTypeindex[typeOfArgument[action_argument_position]] ; object <= upperTypeindex[typeOfArgument[action_argument_position]] ; object++){
        int parameterObject =  parameterVars[action_argument_position].at(object);
        if(object >= lowerTypeindex[type] && object <= upperTypeindex[type]){
            implies(solver, parameterObject, newVar);
            continue;
        }
        impliesNot(solver, parameterObject, newVar);
    }

    return newVar;
}


int PartiallyGroundedSAT::get_different_var(void* solver, sat_capsule & capsule, const vector<int> & previous, const vector<int> & next){
	assert(previous.size() == next.size());
    
	int newVar = capsule.new_variable();
	// TODO better naming for debug
	DEBUG(capsule.registerVariable(newVar,"different"));

	vector<int> _newVar; _newVar.push_back(newVar);
	for (size_t i = 0; i < previous.size(); i++){
		// if changed then is different
		impliesPosAndNegImpliesOr(solver, previous[i], next[i], _newVar);
		impliesPosAndNegImpliesOr(solver, next[i], previous[i], _newVar);
		// if both are true, then not changed, Note: this is not correct for binary representation
		andImpliesNot(solver, previous[i], next[i], newVar);
	}

	return newVar;
}


PartiallyGroundedSAT::PartiallyGroundedSAT(const Task & task) :
    BaseSATEncoding(task){
    _start=clock();
    
    cout << "Entering PG SAT" << endl;
	int numActions = task.actions.size();
#ifdef CMAKE_NO_CPDDL 
	cout << "Compiled without CPDDL support" << endl;
   	exit_with(utils::ExitCode::SEARCH_UNSUPPORTED);
#endif
	cout << "Extracting FAM groups using [Fiser, AAAI 2020] ...";

	pddl_t * pddl = new pddl_t;
    bzero(pddl,sizeof(pddl_t));
    std::string name = "dom";
    pddl->domain_name = const_cast<char*>(name.c_str());
    std::string name2 = "prob";
    pddl->problem_name = const_cast<char*>(name2.c_str());
    pddl->require.strips = 1;
    pddl->require.typing = 1;
    pddl->require.equality = 1;

	
	// adding all the types to CPDDL
	pddlTypesAdd(&pddl->type,root_type_cppdl,-1);
    for (int i = 0; i < task.type_names.size(); i++) {
		pddlTypesAdd(&pddl->type,task.type_names[i].c_str(),directparents[i]+1);

	}


	bzero(&pddl->obj, sizeof(pddl->obj));
	pddl->obj.htable = pddlHTableNew(objHash, objEq, NULL);

    vector<int> type_of_object;
	for (tSize obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
		int actType = -1;
		int typesize = 0x3f3f3f3f;
        for (tSize i = 0; i < oTypes.size(); i++) {
            int j = oTypes[i];
            if (types[j].size() < typesize){
				typesize = types[j].size();
				actType = j;
			}
        }

		pddl_obj_t *objP = pddlObjsAdd(&pddl->obj, task.objects[obj].getName().c_str());
		objP->type = actType + 1;
        type_of_object.push_back(actType);
		objP->is_constant = false;
	}

    pddlPredsInitEq(&pddl->pred);

    std::vector<int> powerLiftedPredicatesToCPDDLPredicates (task.predicates.size());
    std::vector<int> CPDDLPredicatesToPWLPredicates (task.predicates.size());
    for (tSize pred = 0; pred < task.predicates.size(); pred++) {
        cout << task.predicates[pred].getName() << endl;
        if (task.predicates[pred].getName() == "=") {
            powerLiftedPredicatesToCPDDLPredicates[pred] = 0;
            continue;
        }
        powerLiftedPredicatesToCPDDLPredicates[pred] = pddl->pred.pred_size;

        pddl_pred_t *predP = pddlPredsAdd(&pddl->pred);
        predP->name = STRDUP(task.predicates[pred].getName().c_str());
        pddlPredAllocParams(predP, task.predicates[pred].getArity());
        std::vector<int> predTypes = task.predicates[pred].getTypes();
        for(int i = 0 ; i < predP->param_size ; i++){
            pddlPredSetParamType(predP, i, predTypes[i]+1);
        }
    }
    for(size_t i = 0 ; i < powerLiftedPredicatesToCPDDLPredicates.size() ; i++){
        CPDDLPredicatesToPWLPredicates[powerLiftedPredicatesToCPDDLPredicates[i]] = i;
    }




	DEBUG(
    cout << endl << "Initial state (static):" << endl;
    for (tSize i = 0; i < task.get_static_info().get_relations().size(); i++) {
        auto rel = task.get_static_info().get_relations()[i];
        auto tuple = task.get_static_info().get_tuples_of_relation(i);
        for (vector<int> groundA: tuple) {
            cout << "(" << task.predicates[task.get_static_info().get_relations()[i].predicate_symbol].getName();
            for (int obj: groundA) {
                cout << " " << task.objects[obj].getName();
            }
            cout << ")" << endl;
        }
    }

    cout << endl << "Initial state (non-static):" << endl;
    for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
        auto rel = task.initial_state.get_relations()[i];
        auto tuple = task.initial_state.get_tuples_of_relation(i);
        for (vector<int> groundA: tuple) {
            cout << "(" << task.predicates[task.initial_state.get_relations()[i].predicate_symbol].getName();
            for (int obj: groundA) {
                cout << " " << task.objects[obj].getName();
            }
            cout << ")" << endl;
        }
    }
	);

    

    // for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
	// 		const AtomicGoal & goalAtom = task.goal.goal[goal];
    // }
    




    pddl->init = pddlFmToAnd(pddlFmNewEmptyAnd());
    for (tSize i = 0; i < task.get_static_info().get_relations().size(); i++) {
        auto rel = task.get_static_info().get_relations()[i];
        auto tuple = task.get_static_info().get_tuples_of_relation(i);
        for (vector<int> groundA: tuple) {
            pddl_fm_atom_t *a = pddlFmNewEmptyAtom(groundA.size());
            a->pred = powerLiftedPredicatesToCPDDLPredicates[task.get_static_info().get_relations()[i].predicate_symbol];
            for (tSize ai = 0; ai < groundA.size(); ++ai) {
                 a->arg[ai].obj = groundA[ai];
            }
            pddlFmJuncAdd(pddl->init, &(a->fm));
        }
    }
    

    for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
        auto rel = task.initial_state.get_relations()[i];
        auto tuple = task.initial_state.get_tuples_of_relation(i);
        for (vector<int> groundA: tuple) {
            pddl_fm_atom_t *a = pddlFmNewEmptyAtom(groundA.size());
            a->pred = powerLiftedPredicatesToCPDDLPredicates[task.initial_state.get_relations()[i].predicate_symbol];
            for (tSize ai = 0; ai < groundA.size(); ++ai) {
                 a->arg[ai].obj = groundA[ai];
            }
            pddlFmJuncAdd(pddl->init, &(a->fm));
        }
    }



    pddl->goal = pddlFmNewEmptyAnd();
    for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
			const AtomicGoal & goalAtom = task.goal.goal[goal];
            pddl_fm_atom_t *a = pddlFmNewEmptyAtom(goalAtom.args.size());
            a->pred = powerLiftedPredicatesToCPDDLPredicates[task.goal.goal[goal].predicate];
            for(tSize ai = 0 ; ai < goalAtom.args.size() ; ai++){
                a->arg[ai].obj = goalAtom.args[ai];
            }
            pddlFmJuncAdd(pddlFmToAnd(pddl->goal), &(a->fm));
    }



    for (size_t aid = 0; aid < task.actions.size() ; aid++){
        pddl_action_t *a;
    	a = pddlActionsAddEmpty(&pddl->action);
        a->name = strdup(task.actions[aid].get_name().c_str());

        for (size_t varid = 0; varid < task.actions[aid].get_parameters().size() ; varid++){
            pddl_param_t * p = pddlParamsAdd(&(a->param));
            std::string paramName = "?var" + std::to_string(varid);
            p->name = STRDUP(paramName.c_str());
            p->type = task.actions[aid].get_parameters()[varid].type+1;
            p->is_agent = 0;
        }

        if (task.actions[aid].get_precondition().size() /* + t.variableConstraints.size() */ == 0){
			a->pre = pddlFmNewEmptyAnd();
		} else {
            a->pre = pddlFmNewEmptyAnd();
            for(size_t precid = 0 ; precid < task.actions[aid].get_precondition().size() ; precid++){
                size_t argSize = task.actions[aid].get_precondition()[precid].arguments.size();
                pddl_fm_atom_t *atom = pddlFmNewEmptyAtom(argSize);
                atom->pred = powerLiftedPredicatesToCPDDLPredicates[task.actions[aid].get_precondition()[precid].predicate_symbol];
                for(tSize ai = 0 ; ai < argSize ; ai++){
                    if(task.actions[aid].get_precondition()[precid].arguments[ai].constant){
                        atom->arg[ai].obj = task.actions[aid].get_precondition()[precid].arguments[ai].index;
                        atom->arg[ai].param = -1;
                    }else{
                        atom->arg[ai].obj = -1;
                        atom->arg[ai].param = task.actions[aid].get_precondition()[precid].arguments[ai].index;
                    }

                }
                pddlFmJuncAdd(pddlFmToAnd(a->pre), &(atom->fm));
            }
        }

        a->eff = pddlFmNewEmptyAnd();
        for(size_t effid = 0 ; effid < task.actions[aid].get_effects().size() ; effid++){
            size_t argSize = task.actions[aid].get_effects()[effid].arguments.size();
            pddl_fm_atom_t *atom = pddlFmNewEmptyAtom(task.actions[aid].get_effects()[effid].arguments.size());
            atom->pred = powerLiftedPredicatesToCPDDLPredicates[task.actions[aid].get_effects()[effid].predicate_symbol];
            for(tSize ai = 0 ; ai < task.actions[aid].get_effects()[effid].arguments.size() ; ai++){
                if(task.actions[aid].get_effects()[effid].arguments[ai].constant){
                        atom->arg[ai].obj = task.actions[aid].get_effects()[effid].arguments[ai].index;
                        atom->arg[ai].param = -1;
                    }else{
                        atom->arg[ai].obj = -1;
                        atom->arg[ai].param = task.actions[aid].get_effects()[effid].arguments[ai].index;
                    }
            }
            atom->neg = task.actions[aid].get_effects()[effid].negated;
            pddlFmJuncAdd(pddlFmToAnd(a->eff), &(atom->fm));
        }

    }

    

    pddlObjsPropagateToTypes(&pddl->obj, &pddl->type);
    pddlResetPredInInit(pddl);
    pddlResetPredReadWrite(pddl);
	// Normalize pddl, i.e. remove stuff and so on
	pddlNormalize(pddl, NULL);
    /* for(int i = 0 ; i < pddl->pred.pred_size ; i++){
        pddl->pred.pred[i].write = pddl_true;
    } */


    pddl_lifted_mgroups_infer_limits_t limits = PDDL_LIFTED_MGROUPS_INFER_LIMITS_INIT;
	limits.max_candidates = 10000;
	limits.max_mgroups = 10000;
	pddl_lifted_mgroups_t lifted_mgroups;
	pddlLiftedMGroupsInit(&lifted_mgroups);
	pddl_err_t err = PDDL_ERR_INIT;
    err.log_out = stdout;
	//if (!config.quietMode)
		std::cout << "Computing Lifted FAM-Groups [Fiser, AAAI 2020]" << std::endl;
	pddlLiftedMGroupsInferFAMGroups(pddl, &limits, &lifted_mgroups, &err);
    

	//if (!config.quietMode)
		std::cout << "Found " << lifted_mgroups.mgroup_size << " Lifted FAM-Groups" << std::endl;

	/*DEBUG(*/for (int li = 0; li < lifted_mgroups.mgroup_size; ++li){
        fprintf(stdout, "M:%d: ", li);
        pddlLiftedMGroupPrint(pddl, lifted_mgroups.mgroup + li, stdout);}//);

	//for (size_t o = 0; o < domain.constants.size(); o++)
	//	cpddl_add_object_of_sort(pddl,domain.constants[o], ourTypeIDToCPDDL[objectType[o]]);


 	// pddl_lifted_mgroups_t ; pddl_t*, map<int,int>
	std::vector<bool> pruned (lifted_mgroups.mgroup_size);
    vector<int> FAM_group_indexes;
	for (int i = 0; i < lifted_mgroups.mgroup_size; ++i)
		for (int j = 0; j < lifted_mgroups.mgroup_size; ++j)
			if (i != j && !pruned[i] && !pruned[j]){
				DEBUG(std::cout << "Testing whether M" << i << " < M" << j << std::endl);

				if (is_mutex_group_contained_in(lifted_mgroups.mgroup + i, lifted_mgroups.mgroup + j, pddl)){
					DEBUG(std::cout << "Yes. So we prune m1." << std::endl);
					pruned[i] = true;
				}
			}



		std::cout << std::endl << std::endl << "FAM-Mutexes after reduction" << std::endl;
		for (int li = 0; li < lifted_mgroups.mgroup_size; ++li){
		    if (pruned[li]) continue;
            FAM_group_indexes.push_back(li);
            fprintf(stdout, "M:%d: ", li);
            pddlLiftedMGroupPrint(pddl, lifted_mgroups.mgroup + li, stdout);
        }
    

    int total_num_mutexes = 0;
    vector<vector<string>> mutex_predicates(lifted_mgroups.mgroup_size);
    for (int i = 0; i < lifted_mgroups.mgroup_size; i++){
        if (pruned[i]) continue;
        total_num_mutexes++;
        for (int j = 0; j < (lifted_mgroups.mgroup + i)->cond.size; j++){
            const pddl_fm_atom_t *atom = pddlFmToAtomConst((lifted_mgroups.mgroup + i)->cond.fm[j]);
            mutex_predicates[i].push_back(pddl->pred.pred[atom->pred].name);
            //cout << pddl->pred.pred[atom->pred].name << endl;
        }
    }

    
    clearer.clear();//{FAM -> {predicates -> [freeOrCounted][index, param_id, type]}}
    set<int> predicatesInFAM;
    for (int i = 0; i < lifted_mgroups.mgroup_size; i++){
        if (pruned[i]) continue;
        for (int j = 0; j < (lifted_mgroups.mgroup + i)->cond.size; j++){
            const pddl_fm_atom_t *atom = pddlFmToAtomConst((lifted_mgroups.mgroup + i)->cond.fm[j]);
            map<string, vector<vector<int>>> aux;
            for (int k = 0; k < atom->arg_size; k++){
                if (atom->arg[k].param >= 0){
                    int param_id = atom->arg[k].param;
                    const pddl_param_t *p = (lifted_mgroups.mgroup + i)->param.param + param_id;
                    if (p->is_counted_var){
                        vector<int> x = {k, param_id, p->type-1};
                        aux["counted"].push_back(x);
                    }else{
                        vector<int> x = {k, param_id, p->type-1};
                        aux["free"].push_back(x);
                    }
                }
            }
            clearer[i][CPDDLPredicatesToPWLPredicates[atom->pred]] = aux;
            predicatesInFAM.insert(CPDDLPredicatesToPWLPredicates[atom->pred]);
        }
    }

    DEBUG(
        for (auto const& [key, val] : clearer){
            cout << "FAM : " << key << endl;
            for (auto const& [key1, val1] : clearer[key]){
                cout << "\tPredicate : " << key1 << endl;
                for(auto const& [key2, val2] : clearer[key][key1]){
                    cout << "\t\tType of variable : " << key2 << endl;
                    for(size_t vars = 0 ; vars < clearer[key][key1][key2].size() ; vars++){
                        cout << "\t\t\tIndex : " << clearer[key][key1][key2][vars][0] << " ; ParamId : " << clearer[key][key1][key2][vars][1] << " ; Type : " << clearer[key][key1][key2][vars][2] << endl;
                    }
                }
            }
        }
    );


    vector<set<pair<int, int>>> mutex_fixed_variable;
    vector<map<int, set<pair<int, int>>>> mutex_counted_variable;
    for (int i = 0; i < lifted_mgroups.mgroup_size; i++){
        if (pruned[i]) continue;
        set<pair<int, int>> mutex_fixed_variable_aux;
        map<int, set<pair<int, int>>> mutex_counted_variable_aux;
        for (int j = 0; j < (lifted_mgroups.mgroup + i)->cond.size; j++){
            const pddl_fm_atom_t *atom = pddlFmToAtomConst((lifted_mgroups.mgroup + i)->cond.fm[j]);
            mutex_counted_variable_aux[CPDDLPredicatesToPWLPredicates[atom->pred]].size();
            for (int k = 0; k < atom->arg_size; k++){
                if (atom->arg[k].param >= 0){
                    int param_id = atom->arg[k].param;
                    const pddl_param_t *p = (lifted_mgroups.mgroup + i)->param.param + param_id;
                    if (p->is_counted_var){
                        mutex_counted_variable_aux[CPDDLPredicatesToPWLPredicates[atom->pred]].insert({param_id , p->type-1});
                    }else{
                        mutex_fixed_variable_aux.insert({param_id, p->type-1});
                    }
                }
            }
        }
        mutex_fixed_variable.push_back(mutex_fixed_variable_aux);
        mutex_counted_variable.push_back(mutex_counted_variable_aux);
    }

    vector<int> highestCountedVars(mutex_counted_variable.size(), 0);
    for(size_t FAM = 0 ; FAM < highestCountedVars.size() ; FAM++){
        for (auto const& [key, val] : mutex_counted_variable[FAM]){
            for(auto p : val){
                if(p.first > highestCountedVars[FAM]){
                    highestCountedVars[FAM] = p.first;
                }
            }
        }
    }


    //vector<pair<int, int>> FAM_size(mutex_fixed_variable.size());
    int total_groups = 0;
    for(int i = 0 ; i < mutex_counted_variable.size() ; i++){
        int num_groups = 1;
        for(const auto & parampair : mutex_fixed_variable[i]){
            num_groups *= types[parampair.second].size();
        } 

        int size_groups = 0;
        for(const auto & predicate : mutex_counted_variable[i]){
            int size_predicate = 1;
                for(const auto & parampair : predicate.second){
                    size_predicate *= types[parampair.second].size();
              }
            size_groups += size_predicate;
        }
        total_groups += num_groups;
        cout << num_groups << " " << size_groups << endl;
    }

    cout << "Total num mutexes : " << total_groups << endl;

    vector<pair<int, vector<int>>> fam_based_mutexes;
    for(int fam = 0 ; fam < mutex_fixed_variable.size() ; fam++){
        if(mutex_fixed_variable[fam].size() >= 2){
            auto it = mutex_fixed_variable[fam].begin();
            pair<int, int> p1 = *it;
            it++;
            pair<int, int> p2 = *it;
            vector<vector<int>> combinations;
            for(int i = 0 ; i < types[p1.second].size() ; i++){
                for(int j = 0 ; j < types[p2.second].size() ; j++){
                    combinations.push_back({lowerTypeindex[p1.second] + i,lowerTypeindex[p2.second] + j});
                }
            }
            it++;
            vector<vector<int>> new_combination;
            vector<int> aux;
            while(it != mutex_fixed_variable[fam].end()){
                pair<int, int> pn = *it;
                for(int i = 0 ; i < combinations.size() ; i++){
                    for(int j = 0 ; j < types[pn.second].size() ; j++){
                        aux = combinations[i];
                        aux.push_back(lowerTypeindex[pn.second] + j);
                        new_combination.push_back(aux);
                    }
                }
                swap(combinations,new_combination);
                new_combination.clear();
                it++;
            }
            for(int i = 0 ; i < combinations.size() ; i++){
                fam_based_mutexes.push_back({fam, combinations[i]});
            }
        }else if(mutex_fixed_variable[fam].size() == 1){
            pair<int, int> free_var = *(mutex_fixed_variable[fam].begin());
            for(int i = 0 ; i < types[free_var.second].size() ; i++){
                fam_based_mutexes.push_back({fam, {lowerTypeindex[free_var.second] + i}});
            }
        }else if(mutex_fixed_variable[fam].size() == 0){
            fam_based_mutexes.push_back({fam, {}});
        }
    }

    cout << fam_based_mutexes.size() << endl;

    DEBUG(for(size_t i = 0 ; i < fam_based_mutexes.size() ; i++){
        cout << i << " FAM Group : " << fam_based_mutexes[i].first << ", Variables :";
        for(size_t j = 0 ; j < fam_based_mutexes[i].second.size() ; j++){
            cout << " " << fam_based_mutexes[i].second[j] << "(" <<
                task.objects[satObjectToPWLObject[fam_based_mutexes[i].second[j]]].getName() << ")";
        }
        cout << endl;
    });


    /* map<pair<int, vector<int>>,int> all_facts_index; */
    for(size_t predicates = 0 ;  predicates < task.predicates.size() ; predicates++){
        if (task.predicates[predicates].getName().rfind("type@", 0) == 0) continue;
		if (task.predicates[predicates].getName().rfind("=", 0) == 0) continue;
        if (task.predicates[predicates].isStaticPredicate()) continue;
        cout << predicates << " : " << task.predicates[predicates].getName() << endl;
        vector<int> predicate_arguments = task.predicates[predicates].getTypes();
        if(task.predicates[predicates].getArity() >= 2){
            vector<vector<int>> combinations;
            for(int i = 0 ; i < types[predicate_arguments[0]].size() ; i++){
                for(int j = 0 ; j < types[predicate_arguments[1]].size() ; j++){
                    combinations.push_back({lowerTypeindex[predicate_arguments[0]] + i,lowerTypeindex[predicate_arguments[1]] + j});
                }
            }
            vector<vector<int>> new_combination;
            vector<int> aux;
            for(int arity = 2 ; arity < task.predicates[predicates].getArity() ; arity++){
                for(size_t i = 0 ; i < combinations.size() ; i++){
                    for(size_t j = 0 ; j < types[predicate_arguments[arity]].size() ; j++){
                        aux = combinations[i];
                        aux.push_back(lowerTypeindex[predicate_arguments[arity]] + j);
                        new_combination.push_back(aux);
                    }
                }
                swap(combinations,new_combination);
                new_combination.clear();
            }
            for(int i = 0 ; i < combinations.size() ; i++){
                all_facts.push_back({predicates, combinations[i]});
            }
        }else if(task.predicates[predicates].getArity() == 1){
            for(int i = 0 ; i < types[predicate_arguments[0]].size() ; i++){
                all_facts.push_back({predicates, {lowerTypeindex[predicate_arguments[0]] + i}});
            }
        }else if(task.predicates[predicates].getArity() == 0){
            all_facts.push_back({predicates, {}});
        }
    }

    for (size_t i =0 ; i < all_facts.size(); i++){
        all_facts_index[all_facts[i]] = i;
    }

    /* DEBUG(for(size_t i = 0 ; i < all_facts.size() ; i++){
        cout << "Predicate : " << all_facts[i].first << "; Objects :";
        for(size_t j = 0 ; j < all_facts[i].second.size() ; j++){
            cout << " " << all_facts[i].second[j];
        }
        cout << endl;
    }); */


    map<int, vector<int>> fact_to_mutexes;
    for(size_t facts = 0 ; facts < all_facts.size() ; facts++){
        vector<int> mutexes_with_fact;
        pair<int, vector<int>> fact = all_facts[facts];
        for(size_t mutexes = 0 ; mutexes < fam_based_mutexes.size() ; mutexes++){
            pair<int, vector<int>> mutex = fam_based_mutexes[mutexes];
            for (int j = 0; j < (lifted_mgroups.mgroup + FAM_group_indexes[mutex.first])->cond.size; j++){
                const pddl_fm_atom_t *atom = pddlFmToAtomConst((lifted_mgroups.mgroup + FAM_group_indexes[mutex.first])->cond.fm[j]);
                if(pddl->pred.pred[atom->pred].id == powerLiftedPredicatesToCPDDLPredicates[fact.first]){
                    bool add = true;
                    for (int k = 0; k < atom->arg_size; k++){
                        if (atom->arg[k].param >= 0){
                            int param_id = atom->arg[k].param;
                            const pddl_param_t *p = (lifted_mgroups.mgroup + FAM_group_indexes[mutex.first])->param.param + param_id;
                            if (!p->is_counted_var && fact.second[k] != mutex.second[param_id]){
                                add = false;
                                break;
                            }else if (p->is_counted_var && (fact.second[k] < lowerTypeindex[p->type-1] || fact.second[k] > upperTypeindex[p->type-1])){
                                add = false;
                                break;
                            }
                        }else if (atom->arg[k].param < 0 && atom->arg[k].obj != satObjectToPWLObject[fact.second[k]]){
                            add = false;
                            break;
                        }
                    }
                    if (add){
                        mutexes_with_fact.push_back(mutexes);
                    }
                }
            }
        }

        fact_to_mutexes[facts] = mutexes_with_fact;
        mutexes_with_fact.clear();
    }

    /* DEBUG(for(size_t facts = 0 ; facts < all_facts.size() ; facts++){
        cout << "Fact " << facts << " :";
        for(size_t i = 0 ; i < fact_to_mutexes[facts].size() ; i++){
            cout << " " << fact_to_mutexes[facts][i];
        }
        cout << endl;
    }); */

    map<int, vector<int>> mutex_to_facts;
    for(size_t i = 0 ; i < fact_to_mutexes.size() ; i++){
        for(size_t j = 0 ; j < fact_to_mutexes[i].size() ; j++){
            mutex_to_facts[fact_to_mutexes[i][j]].push_back(i);
        }
    }

    cout << "mutex_to_facts.size() : " << mutex_to_facts.size() << endl;

    for(size_t i = 0 ;  i < total_groups ; i++){
        if(!mutex_to_facts.count(i)){
            cout << "FAM based mutex number : " << FAM_group_indexes[fam_based_mutexes[i].first] << " ; " << i << endl;
        }  
    }
    
    vector<bool> decreased_fact(fact_to_mutexes.size(), false);
    vector<int> num_facts_in_mutex(total_groups, 0);
    map<int,set<int>> sizeToMutexes;
    vector<int> selected_mutexes;
    for(size_t i = 0 ; i < total_groups ; i++){
        num_facts_in_mutex[i] = mutex_to_facts[i].size();
        sizeToMutexes[mutex_to_facts[i].size()].insert(i);
    }
    
    if(sizeToMutexes.size() > 0){
        while( sizeToMutexes.rbegin()->first /*!= 0*/){
            if (sizeToMutexes.rbegin()->second.size() == 0){
                sizeToMutexes.erase(sizeToMutexes.rbegin()->first);
                continue;
            }

            int largestMutexGroup = *(sizeToMutexes.rbegin()->second.begin());

            selected_mutexes.push_back(largestMutexGroup);
            
            for (int fact : mutex_to_facts[largestMutexGroup]){
                if (!decreased_fact[fact]){
                    //cout << "Fact that is going to be decremented : " << fact << endl;
                    decreased_fact[fact] = true;
                    for (int mutex : fact_to_mutexes[fact]){
                        //cout << "Mutexes that contain the fact and will have their size decreased in 1 : " << mutex << endl;
                        int currentNum = num_facts_in_mutex[mutex];
                        //cout << "num_facts_in_mutex.size() : " << num_facts_in_mutex.size() << endl;
                        //cout << "Current size of said mutex : " << currentNum << endl;
                        num_facts_in_mutex[mutex]--;

                        /* cout << "Mutexes of same size :";
                        for(int a : sizeToMutexes[currentNum]){
                            cout << " " << a;
                        }
                        cout << "\nTrying to delete mutex : " << mutex << endl; */

                        sizeToMutexes[currentNum].erase(mutex);
                        sizeToMutexes[currentNum-1].insert(mutex);
                    }

                }
                
            }

        }
    }


    for(size_t selected_mutex = 0 ; selected_mutex < selected_mutexes.size() ; selected_mutex++){
        pair<int, vector<int>> mutex = fam_based_mutexes[selected_mutexes[selected_mutex]];
        mutexFDRVars[mutex.first][mutex.second].size();
        for(int filler_vecs = 0 ; filler_vecs <= highestCountedVars[mutex.first]+1 ; filler_vecs++){
            mutexFDRVars[mutex.first][mutex.second].push_back(vector<int>());
        }
        set<int> countedVarsAdded;
        for (auto const& [key, val] : mutex_counted_variable[mutex.first]){
            mutexFDRVars[mutex.first][mutex.second][highestCountedVars[mutex.first]+1].push_back(key);
            for(auto p : val){
                if(countedVarsAdded.find(p.first) != countedVarsAdded.end()){
                    continue;
                }else{
                    countedVarsAdded.insert(p.first);
                    for(int obj = lowerTypeindex[p.second] ; obj <= upperTypeindex[p.second] ; obj++){
                        mutexFDRVars[mutex.first][mutex.second][p.first].push_back(obj);
                    }
                }
            }
        }
        mutexFDRVars[mutex.first][mutex.second][highestCountedVars[mutex.first]+1].push_back(-1);
    }

     DEBUG(
        cout << "---------------FDR variables data structure : --------------------\n";
        for(size_t FAM = 0 ; FAM < mutexFDRVars.size() ; FAM++){
            cout << "FAM number : " << FAM << endl;
            for(auto const& [key, val] : mutexFDRVars[FAM]){
                cout << "\tGrounded Free Vars :";
                for(size_t gfv = 0 ; gfv < key.size() ; gfv++){
                    cout << " " << key[gfv];
                }
                cout << endl;
                cout << "\t\tGrounded Counted Vars :<";
                for(size_t num_cv = 0 ; num_cv < val.size() ; num_cv++){
                    cout << "<";
                    for(size_t gcv = 0 ; gcv < val[num_cv].size() ; gcv++){
                        cout << " " << val[num_cv][gcv];
                    }
                    cout << "> ";
                }
                cout << ">\n";
            }
        }
    );

    //map<int, map<int, vector<map<string, vector<vector<int>>>>>> clearer
    idek.clear();//pred -> {[typesOfArguments] -> {Fam -> {[[allFreeGroundings]]}}}
    for(size_t actions = 0 ; actions < task.actions.size() ; actions++){
        for(size_t preconditions = 0 ; preconditions < task.actions[actions].get_precondition().size() ; preconditions++){
            if(predicatesInFAM.find(task.actions[actions].get_precondition()[preconditions].predicate_symbol) == predicatesInFAM.end()) continue;
            vector<int> typesOfArguments;
            for(size_t argument = 0 ; argument < task.actions[actions].get_precondition()[preconditions].arguments.size() ; argument++){
                    int indexInAction = task.actions[actions].get_precondition()[preconditions].arguments[argument].index;
                    typesOfArguments.push_back(task.actions[actions].get_parameters()[indexInAction].type);
            }
            for (auto const& [FAM, mapOfPredicates] : clearer){
                for (auto const& [pred, v] : mapOfPredicates){
                    if (pred == task.actions[actions].get_precondition()[preconditions].predicate_symbol){
                        vector<vector<int>> objectsToCombine;
                        for(size_t freeVars = 0 ; freeVars < clearer[FAM][pred]["free"].size() ; freeVars++){
                            int indexInPred = clearer[FAM][pred]["free"][freeVars][0];
                            int famVariableType = clearer[FAM][pred]["free"][freeVars][2];
                            vector<int> objects;

                            int intersectionLower = max(lowerTypeindex[typesOfArguments[indexInPred]], lowerTypeindex[famVariableType]);
                            int intersectionUpper = min(upperTypeindex[typesOfArguments[indexInPred]], upperTypeindex[famVariableType]);

                            for(int lowerObj = intersectionLower ; lowerObj <= intersectionUpper ; lowerObj++){
                                objects.push_back(lowerObj);
                            }
                            objectsToCombine.push_back(objects);
                        }
                        vector<vector<int>> freeGroundings = getCombinations(objectsToCombine);
                        if (freeGroundings.size())
                            idek[pred][typesOfArguments][FAM] = freeGroundings;
                    }
                }
            }
        }
        for(size_t effects = 0 ; effects < task.actions[actions].get_effects().size() ; effects++){
            if(predicatesInFAM.find(task.actions[actions].get_effects()[effects].predicate_symbol) == predicatesInFAM.end()) continue;
            vector<int> typesOfArguments;
            for(size_t argument = 0 ; argument < task.actions[actions].get_effects()[effects].arguments.size() ; argument++){
                    int indexInAction = task.actions[actions].get_effects()[effects].arguments[argument].index;
                    typesOfArguments.push_back(task.actions[actions].get_parameters()[indexInAction].type);
            }
            for (auto const& [FAM, mapOfPredicates] : clearer){
                for (auto const& [pred, v] : mapOfPredicates){
                    if (pred == task.actions[actions].get_effects()[effects].predicate_symbol){
                        vector<vector<int>> objectsToCombine;
                        for(size_t freeVars = 0 ; freeVars < clearer[FAM][pred]["free"].size() ; freeVars++){
                            int indexInPred = clearer[FAM][pred]["free"][freeVars][0];
                            int famVariableType = clearer[FAM][pred]["free"][freeVars][2];
                            vector<int> objects;

                            int intersectionLower = max(lowerTypeindex[typesOfArguments[indexInPred]], lowerTypeindex[famVariableType]);
                            int intersectionUpper = min(upperTypeindex[typesOfArguments[indexInPred]], upperTypeindex[famVariableType]);

                            for(int lowerObj = intersectionLower ; lowerObj <= intersectionUpper ; lowerObj++){
                                objects.push_back(lowerObj);
                            }
                            objectsToCombine.push_back(objects);
                        }
                        vector<vector<int>> freeGroundings = getCombinations(objectsToCombine);
                        if (freeGroundings.size())
                            idek[pred][typesOfArguments][FAM] = freeGroundings;
                    }
                }
            }
        }
    }

    /* DEBUG(
        for (auto const& [pred, typesOfArgumentsMap] : idek){
            cout << "Predicate : " << pred << endl;
            for(auto const& [typesOfArguments, FAMMap] : idek[pred]){
                cout << "\tTypes of arguments :" << "length : ";
                for(size_t args = 0 ; args < typesOfArguments.size() ; args++){
                    cout << " " << typesOfArguments[args];
                }
                cout << endl;
                for(auto const& [FAM, freeGroundings] : idek[pred][typesOfArguments]){
                    cout << "\t\tFAM : " << FAM << endl;
                    for(size_t grounding = 0 ; grounding < freeGroundings.size() ; grounding++){
                        cout << "\t\t\t Grounding of Free Vars :";
                        for(size_t freeVarObject = 0 ; freeVarObject < freeGroundings[grounding].size() ; freeVarObject++){
                            cout << " " << freeGroundings[grounding][freeVarObject];
                        }
                        cout << endl;
                    }
                }
            }
        }
    ); */
    
    //exit(0);
    
    
    cout << "Selected mutexes :";
    for(size_t i = 0 ; i < selected_mutexes.size() ; i++){
        cout << " " << selected_mutexes[i];
    }
    cout<< endl;

    vector<int> uncovered_facts;
    for(size_t i = 0 ; i < decreased_fact.size() ; i++){
        if(!decreased_fact[i]){
            uncovered_facts.push_back(i);
        }
    }


    cout << "Uncovered facts (" << uncovered_facts.size() << " of " << all_facts.size() << "):" ;
    for(size_t i = 0 ; i < uncovered_facts.size() ; i++){
        cout << " " << uncovered_facts[i];

        pair<int, vector<int>> fact = all_facts[uncovered_facts[i]];

        cout << "Predicate : " << fact.first << "; Objects :";
        for(size_t j = 0 ; j < fact.second.size() ; j++){
            cout << " " << fact.second[j] << " " << task.objects[satObjectToPWLObject[fact.second[j]]].getName();
        }
        cout << endl;

    }
    cout<< endl;


	cout << endl;
    //pddlPrintPDDLDomain(pddl,stdout);
    //pddlPrintPDDLProblem(pddl,stdout);

    timesplit(PRECPROCESSING);
}


#define clauseNumber(name) clauseCounter[name]+=get_number_of_clauses()-beforeClause;beforeClause=get_number_of_clauses();timesplit(name);
#define atMostOneParameterValue "at most one parameter value"
#define actionAllowedArguments "action allowed arguments"
#define equalsPreconditions "equals preconditions"
#define staticPrecondition "static preconditions"
#define oneAction "one Action"
#define nullary "nullary"
#define preconditionImplications "precondition implications"
#define effectImplications "effect implications"
#define causeVariablesImplications "cause variables implications"
#define frameAxioms "frame axioms"


vector<int> PartiallyGroundedSAT::generateFactVars(sat_capsule & capsule, int timestep, vector<string> factToString){
	vector<int> mutexPredicateVarsTime;
	for (size_t predicate = 0; predicate < all_facts.size(); predicate++){
	    int grounded_mutex_predicate_var;
	    grounded_mutex_predicate_var = capsule.new_variable();
	    mutexPredicateVarsTime.push_back(grounded_mutex_predicate_var);
	    DEBUG(capsule.registerVariable(grounded_mutex_predicate_var,"predicate@" + to_string(timestep) + "-" + factToString[predicate]) );
	}

	return mutexPredicateVarsTime;
}
map<int, map<vector<int>, vector<vector<int>>>> PartiallyGroundedSAT::generateFAMVars(void* solver, sat_capsule & capsule, int timestep){
    map<int, map<vector<int>, vector<vector<int>>>> mutexFDRSATVarsTime;
	cout << "mutexFDRVars " << mutexFDRVars.size() << endl;
    for(size_t FAM = 0 ; FAM < mutexFDRVars.size() ; FAM++){
        for (auto const& [key, val] : mutexFDRVars[FAM]){
            mutexFDRSATVarsTime[FAM][key].size();
            for(size_t num_vec = 0 ; num_vec < mutexFDRVars[FAM][key].size() ; num_vec++){
                mutexFDRSATVarsTime[FAM][key].push_back(vector<int>());
                for(size_t objs = 0 ; objs < mutexFDRVars[FAM][key][num_vec].size() ; objs++){
                    int groundedCountedObjectVar = capsule.new_variable();
                    mutexFDRSATVarsTime[FAM][key][num_vec].push_back(groundedCountedObjectVar);
	    			DEBUG(
						string name = "";
						for (int x : key) name += " " + task.objects[satObjectToPWLObject[x]].getName();
	
						string value = "";
						int int_obj = mutexFDRVars[FAM][key][num_vec][objs];
						if (num_vec + 1 == mutexFDRVars[FAM][key].size()){
							if (int_obj == -1) value = "-1";
							else value = task.predicates[int_obj].getName();
						} else {
							value = task.objects[satObjectToPWLObject[int_obj]].getName();
						}
						capsule.registerVariable(groundedCountedObjectVar,"fam " + to_string(FAM) + " - " + name + " var " + to_string(num_vec) + " = " + value);
					);
                }
                atMostOne(solver, capsule, mutexFDRSATVarsTime[FAM][key][num_vec]);
            }
        }
    }
    return mutexFDRSATVarsTime;
}



utils::ExitCode PartiallyGroundedSAT::solve(const Task &task, int limit, bool optimal, bool incremental) {

    int lowerLength = 1;
    int upperLength = 1000;

    if (limit != -1){
        lowerLength = upperLength = limit;
    }

    for (int timesteps = lowerLength; timesteps <= upperLength; timesteps++){
        map<string,int> clauseCounter;

        void* solver = ipasir_init();
        reset_number_of_clauses();
        sat_capsule capsule;
        int beforeClause = get_number_of_clauses();

         for (size_t predicate = 0; predicate < all_facts.size(); predicate++){
            string groundedPredicate = task.predicates[all_facts[predicate].first].getName()+"("; 
            for(size_t object = 0 ; object < all_facts[predicate].second.size() ; object++){
                if (object) groundedPredicate += ", ";
                groundedPredicate += task.objects[satObjectToPWLObject[all_facts[predicate].second[object]]].getName();
            }
            groundedPredicate += ")";
            factToString.push_back(groundedPredicate);
        }

        vector<int> previousTimeMutexPredicateVars = generateFactVars(capsule,0, factToString);
        map<int, map<vector<int>, vector<vector<int>>>> mutexFDRSATVarsTime = generateFAMVars(solver, capsule,0);


	     DEBUG(
	        cout << "---------------FDR SAT variables data structure : --------------------\n";
	        for(size_t FAM = 0 ; FAM < mutexFDRSATVarsTime.size() ; FAM++){
	            cout << "FAM number : " << FAM << endl;
	            for(auto const& [key, val] : mutexFDRSATVarsTime[FAM]){
	                cout << "\tGrounded Free Vars :";
	                for(size_t gfv = 0 ; gfv < key.size() ; gfv++){
	                    cout << " " << key[gfv];
	                }
	                cout << endl;
	                cout << "\t\tGrounded Counted Vars :<";
	                for(size_t num_cv = 0 ; num_cv < val.size() ; num_cv++){
	                    cout << "<";
	                    for(size_t gcv = 0 ; gcv < val[num_cv].size() ; gcv++){
	                        cout << " " << val[num_cv][gcv];
	                    }
	                    cout << "> ";
	                }
	                cout << ">\n";
	            }
	        }
	    );


		// TODO: assert that the initial state is true.
        // one for every mutex should be true

        for (size_t i = 0; i < task.initial_state.get_relations().size(); i++) {
            auto rel = task.initial_state.get_relations()[i];
            auto tuple = task.initial_state.get_tuples_of_relation(i);
            for (vector<int> groundA: tuple) {
                int pred = rel.predicate_symbol;
                vector<int> satTuple;
                vector<int> satTupleTypes;
                for(int x : groundA){
                    satTuple.push_back(pwlObjToSATObject[x]);
                    satTupleTypes.push_back(types[pwlObjToSATObject[x]]);
                }
                if(all_facts_index[{pred, satTuple}].count(uncovered_facts)){
                    actsInInitialState.insert(all_facts_index[{pred, satTuple}]);
                }else{
                    map<int, vector<vector<int>>> smth = idek[pred][satTupleTypes];
                    for(auto const& [key, val] : smth){
                        for(vector<int> v : val){
                            mutexFDRSATVarsTime[key][v];
                        }
                    }
                }

            }
        }
        for(size_t fact = 0 ; fact < all_facts.size() ; fact++){
            if(factsInInitialState.count(fact)){
                //cout << fact << " " << previousTimeMutexPredicateVars[fact] << endl;
                assertYes(solver,previousTimeMutexPredicateVars[fact]);
            }else{
                assertNot(solver,previousTimeMutexPredicateVars[fact]);
            }
        }

        set<int> factsInInitialState;
        for (size_t i = 0; i < task.initial_state.get_relations().size(); i++) {
            auto rel = task.initial_state.get_relations()[i];
            auto tuple = task.initial_state.get_tuples_of_relation(i);
            for (vector<int> groundA: tuple) {
                int pred = rel.predicate_symbol;
                vector<int> satTuple;
                for(int x : groundA){
                    satTuple.push_back(pwlObjToSATObject[x]);
                }
                factsInInitialState.insert(all_facts_index[{pred, satTuple}]);
            }
        }
        for(size_t fact = 0 ; fact < all_facts.size() ; fact++){
            if(factsInInitialState.count(fact)){
                //cout << fact << " " << previousTimeMutexPredicateVars[fact] << endl;
                assertYes(solver,previousTimeMutexPredicateVars[fact]);
            }else{
                assertNot(solver,previousTimeMutexPredicateVars[fact]);
            }
        }

        // nullary predicates initial state
        std::unordered_map<int,int> lastNullary;
        for (int n : task.nullary_predicates){
            int nullaryInInit = capsule.new_variable();
            lastNullary[n] = nullaryInInit;
            DEBUG(capsule.registerVariable(nullaryInInit, "nullary#" + to_string(n) + "_" + to_string(0)));

            if (task.initial_state.get_nullary_atoms()[n])
                assertYes(solver,nullaryInInit);
            else
                assertNot(solver,nullaryInInit);
        }


        std::vector<vector<std::map<int,int>>> parameterVars;
        vector<vector<int>> actionVars;
        vector<map<int, map<vector<int>, vector<vector<int>>>>> mutexFDRSATVars;

        for (int timestep = 0; timestep < timesteps; timestep++){
            cout <<"TIMESTEP " << timestep << endl;

            std::vector<std::map<int,int>> parameterVarsTime(numberOfArgumentPositions);
            for (int paramter = 0; paramter < numberOfArgumentPositions; paramter++){
                int type = typeOfArgument[paramter];
                int lower = lowerTypeindex[type];
                int upper = upperTypeindex[type];
                vector<int> temp;

                for (int o = 0; o < upper - lower + 1; o++){
                    int objectVar = capsule.new_variable();
                    parameterVarsTime[paramter][lower + o] = objectVar;
                    temp.push_back(objectVar);
                    DEBUG(capsule.registerVariable(objectVar, "const@" + to_string(timestep) + "#" + to_string(paramter)
                        + "-" + task.objects[satObjectToPWLObject[o + lower]].getName()));
                }
                // each parameter can have at most one value
                atMostOne(solver,capsule,temp);
            }
            clauseNumber(atMostOneParameterValue);
            
            parameterVars.push_back(parameterVarsTime);

            std::vector<int> actionVarsTime;
            for (size_t action = 0; action < task.actions.size(); action++){
                DEBUG(cout << "\t" << task.actions[action].get_name() << endl);

                int actionVar;
                actionVar = capsule.new_variable();
                actionVarsTime.push_back(actionVar);
                DEBUG(capsule.registerVariable(actionVar,"action@" + to_string(timestep) + "-" + task.actions[action].get_name()));

                // typing implications!
                auto params = task.actions[action].get_parameters();
                for (size_t l = 0; l < params.size(); l++) {
                    int thisParameterIndex = actionArgumentPositions[action][l];
                    DEBUG(cout << "\t\t" << task.type_names[params[l].type] << ": ");
                    //if (!needToType[{action,l}]){
                    //	DEBUG(cout << "no need to type " << endl);
                    //	continue;
                    //}
                    
                    int lower = lowerTypeindex[params[l].type];
                    int upper = upperTypeindex[params[l].type];

                    DEBUG(for (int m = lower; m <= upper; m++) {
                        cout << task.objects[satObjectToPWLObject[m]].getName() << " ";
                    }
                    cout << endl);

                    //for (int i = 0; i < lower; i++){
                    //	int parameterConstantVar = parameterVarsTime[l][i];
                    //	impliesNot(solver,actionVar,parameterConstantVar);
                    //}

                    //for (int i = upper + 1; i < int(task.objects.size()); i++){
                    //	int parameterConstantVar = parameterVarsTime[l][i];
                    //	impliesNot(solver,actionVar,parameterConstantVar);
                    //}

                    std::vector<int> allowed;
                    for (int i = 0; i <= upper - lower; i++){
                        int parameterConstantVar = parameterVarsTime[thisParameterIndex][lower + i];
                        allowed.push_back(parameterConstantVar);
                    }
                    impliesOr(solver,actionVar,allowed);
                }
                clauseNumber(actionAllowedArguments);
            

                /////// SPECIAL PRECONDITIONS
                const auto precs = task.actions[action].get_precondition();
                for (size_t prec = 0; prec < precs.size(); prec++) {
                    //DEBUG(cout << "\t\tprecondition #" << prec << endl);
                    
                    const auto & precObjec = precs[prec];
                    int predicate = precObjec.predicate_symbol;
                    if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
                
                    //bef = get_number_of_clauses();
                
                    if (task.predicates[predicate].getName().rfind("=", 0) == 0){
                        int varA = precObjec.arguments[0].index;
                        int varB = precObjec.arguments[1].index;

                        if (precObjec.negated){
                            // not equals
                            if (precObjec.arguments[0].constant){
                                int myObjIndex = pwlObjToSATObject[varA];
                                varB = actionArgumentPositions[action][varB];
                                impliesNot(solver,actionVar, parameterVarsTime[varB][myObjIndex]);
                            } else if (precObjec.arguments[1].constant){
                                int myObjIndex = pwlObjToSATObject[varB];
                                varA = actionArgumentPositions[action][varA];
                                impliesNot(solver,actionVar, parameterVarsTime[varA][myObjIndex]);
                            } else {
                                varA = actionArgumentPositions[action][varA];
                                varB = actionArgumentPositions[action][varB];
                                for(int o = max(lowerTypeindex[typeOfArgument[varA]],lowerTypeindex[typeOfArgument[varB]]);
                                        o <= min(upperTypeindex[typeOfArgument[varA]],upperTypeindex[typeOfArgument[varB]]); o++){
                                    andImpliesNot(solver,actionVar,parameterVarsTime[varA][o], parameterVarsTime[varB][o]);
                                }
                            }
                        } else {
                            // equals
                            if (precObjec.arguments[0].constant){
                                int myObjIndex = pwlObjToSATObject[varA];
                                varB = actionArgumentPositions[action][varB];
                                implies(solver,actionVar, parameterVarsTime[varB][myObjIndex]);
                            } else if (precObjec.arguments[1].constant){
                                int myObjIndex = pwlObjToSATObject[varB];
                                varA = actionArgumentPositions[action][varA];
                                implies(solver,actionVar, parameterVarsTime[varA][myObjIndex]);
                            } else {
                                varA = actionArgumentPositions[action][varA];
                                varB = actionArgumentPositions[action][varB];
                                for(int o = max(lowerTypeindex[typeOfArgument[varA]],lowerTypeindex[typeOfArgument[varB]]);
                                        o <= min(upperTypeindex[typeOfArgument[varA]],upperTypeindex[typeOfArgument[varB]]); o++){
                                    andImplies(solver,actionVar,parameterVarsTime[varA][o], parameterVarsTime[varB][o]);
                                    andImplies(solver,actionVar,parameterVarsTime[varB][o], parameterVarsTime[varA][o]);
                                }
                            }
                        }
            
                        clauseNumber(equalsPreconditions);
                        continue;
                    }

                    // special handling for static precondition
                    if (task.predicates[predicate].isStaticPredicate()){
                        if (preconditionSupportingTuplesFromInit[action][prec].size() == 0){
                            //DEBUG(cout << "\t\tno init support for precondition #" << prec << " with pred " << predicate << " " << task.predicates[predicate].getName() << endl);
                            assertNot(solver,actionVar); // cannot be supported by init!
                        } else {
                            if (preconditionSupportingTuplesFromInit[action][prec].size() == 1){
                                // if this action is chosen, exactly this tuple has to be used as the precondition
                                vector<int> tuple = preconditionSupportingTuplesFromInit[action][prec][0].first;
                                for (size_t j = 0; j < tuple.size(); j++){
                                    int myObjIndex = pwlObjToSATObject[tuple[j]];
                                    if (precObjec.arguments[j].constant){
                                        if (precObjec.arguments[j].index != tuple[j])
                                            assertNot(solver,actionVar);
                                    } else {
                                        int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
                                        if (myObjIndex < lowerTypeindex[typeOfArgument[myParam]] || myObjIndex > upperTypeindex[typeOfArgument[myParam]]){
                                            assertNot(solver,actionVar);
                                        } else {
                                            implies(solver,actionVar, parameterVarsTime[myParam][myObjIndex]);
                                        }
                                    }
                                }
                            } else {
                                if (precObjec.arguments.size() == 1){
                                    vector<int> possibleValues;
                                    
                                    for (size_t i = 0; i < preconditionSupportingTuplesFromInit[action][prec].size(); i++){
                                        vector<int> tuple = preconditionSupportingTuplesFromInit[action][prec][i].first;
                                    
                                        int myObjIndex = pwlObjToSATObject[tuple[0]];
                                        int myParam = actionArgumentPositions[action][precObjec.arguments[0].index];
                                        int constantVar = parameterVarsTime[myParam][myObjIndex];
                                        
                                        possibleValues.push_back(constantVar);
                                    }

                                    impliesOr(solver,actionVar,possibleValues);
                                } else {
                                    bool firstWithNonConst = true;
                                    for (size_t lastPos = 0; lastPos < precObjec.arguments.size() - 1 ; lastPos++){
                                        // ignore all arguments until we find the first one with a non-constant
                                        if (precObjec.arguments[lastPos].constant && firstWithNonConst) continue;

                                        map<vector<int>,set<int>> possibleUpto;

                                        // build assignment tuple up to this point
                                        for (size_t i = 0; i < preconditionSupportingTuplesFromInit[action][prec].size(); i++){
                                            vector<int> tuple = preconditionSupportingTuplesFromInit[action][prec][i].first;
                                            vector<int> subTuple;
                                            subTuple.push_back(actionVar);
                                        
                                            for (size_t j = 0; j <= lastPos; j++){
                                                // push only the non-constants
                                                if (precObjec.arguments[j].constant) continue;
                                                int myObjIndex = pwlObjToSATObject[tuple[j]];
                                                int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
                                                int constantVar = parameterVarsTime[myParam][myObjIndex];
                                                
                                                subTuple.push_back(constantVar);
                                            }
                                            
                                            if (precObjec.arguments[lastPos + 1].constant) {
                                                possibleUpto[subTuple].insert(0);
                                                continue;
                                            }

                                            int myObjIndex = pwlObjToSATObject[tuple[lastPos + 1]];
                                            int myParam = actionArgumentPositions[action][precObjec.arguments[lastPos + 1].index];
                                            int constantVar = parameterVarsTime[myParam][myObjIndex];


                                            possibleUpto[subTuple].insert(constantVar);
                                        }


                                        if (!precObjec.arguments[lastPos + 1].constant)
                                            for (auto & x : possibleUpto){
                                                andImpliesOr(solver,x.first,x.second);
                                            }

                                        if (firstWithNonConst){
                                            vector<int> initial;
                                            for (auto & x : possibleUpto)
                                                initial.push_back(x.first[1]);

                                            impliesOr(solver,actionVar,initial);
                                            firstWithNonConst = false;
                                        }
                                    }
                                }
                            }
                        }
                        clauseNumber(staticPrecondition);
                    } 
                }
            }

            actionVars.push_back(actionVarsTime);

 
            // generate variables for successor state
            vector<int> currentTimeMutexPredicateVars = generateFactVars(capsule,timestep+1, factToString);
            map<int, map<vector<int>, vector<vector<int>>>> mutexFDRSATVarsNextTime = generateFAMVars(solver, capsule, timestep+1);
            std::unordered_map<int,int> currentNullary;
            for (int n : task.nullary_predicates){
                int nullVar = capsule.new_variable();
                currentNullary[n] = nullVar;
                DEBUG(capsule.registerVariable(nullVar,	"nullary#" + to_string(n) + "_" + to_string(timestep+1)));
            }

            //DEBUG(cout << "\tRegular Pre Eff" << endl);
            map<int,vector<int>> adders, deleters;
			
			// cause variables that can cause the change of a counted variable inside of a ground mutex group to a specific value
			// indexing is as for the mutexFDRVars
			// FAM-group -> value of free variables -> vector over counted + predicate -> !NEW! list of cause variables
            map<int, map<vector<int>, map<int, vector<int>>>> changers;

			// generate clauses for preconditions
            for (size_t action = 0; action < task.actions.size(); action++){
                //DEBUG(cout << "\t" << task.actions[action].get_name() << endl);
                int actionVar = actionVarsTime[action];

                /////// non-special PRECONDITIONS
                //std::map<int, std::map<int, int>> translatePreconditionToGlobalArguments;
                const auto precs = task.actions[action].get_precondition();
                for (size_t prec = 0; prec < precs.size(); prec++) {
                    //DEBUG(cout << "\t\tprecondition #" << prec << " " << precs.size() << endl);
                    const auto & precObjec = precs[prec];
                    int predicate = precObjec.predicate_symbol;
                    if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
                    if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue;
                    if (task.predicates[predicate].isStaticPredicate()) continue;

                    // the precondition is "normal"
                    //
                    // TODO action implies its preconditions
                    // for every assignment of the parameters of the precondition assert that the respective fact is true
                    // This should involve iterating over all groundings of the precondition ... so this might be expensive
                    // WORK HERE!!!!!!!!!!!!!

                    //vector<map<vector<int>, vector<vector<int>>>> mutexFDRVars(mutex_fixed_variable.size());[for each FAM : {<Free grounding> -> <COunted Grounding>}]
                    //map<int, map<int, vector<map<string, vector<vector<int>>>>>> clearer;//{FAM -> {predicates -> [freeOrCounted][index, param_id, type]}}
                    //map<int, map<vector<int>, map<int, map<int, vector<vector<int>>>>>> idek;//pred -> {[typesOfArguments] -> {Fam -> {[[allFreeGroundings]]}}}
                    std::vector<int> translatePreconditionToGlobalArguments;

                    for(size_t argument = 0 ; argument < precObjec.arguments.size() ; argument++){
                        if (precObjec.arguments[argument].constant){
                            translatePreconditionToGlobalArguments.push_back(-1);
                            continue;
                        }
                        int indexInActionSchema = precObjec.arguments[argument].index;
                        int actionSchemaToGlobalArguments = actionArgumentPositions[action][indexInActionSchema];
                        translatePreconditionToGlobalArguments.push_back(actionSchemaToGlobalArguments);
                    }

                    std::vector<int> lowerLimitPredicate;
                    std::vector<int> typesOfPredicate;

                    for(size_t argument = 0 ; argument < precObjec.arguments.size() ; argument++){
                        if(translatePreconditionToGlobalArguments[argument] == -1){
                            lowerLimitPredicate.push_back(pwlObjToSATObject[precObjec.arguments[argument].index]);
                            continue;
                        }
                        int type = typeOfArgument[translatePreconditionToGlobalArguments[argument]];
                        int lower = lowerTypeindex[type];
                        typesOfPredicate.push_back(type);
                        lowerLimitPredicate.push_back(lower);
                    }

                    
                    int lowerIndexGroundedPredicate = all_facts_index[{precObjec.predicate_symbol, lowerLimitPredicate}];

                    map<int, vector<vector<int>>> correspondingFAMs = idek[predicate][typesOfPredicate];
                    for(auto const& [key, val] : correspondingFAMs){
                        for(size_t grounding = 0 ; grounding < val.size() ; grounding++){
                            vector<int> leftImplication;
                            vector<int> rightImplication;
                            leftImplication.push_back(actionVar);
                            for(size_t freeVars = 0 ; freeVars < clearer[key][predicate]["free"].size() ; freeVars++){
                                int trltToGlobalIndex = translatePreconditionToGlobalArguments[clearer[key][predicate]["free"][freeVars][0]];
                                leftImplication.push_back(parameterVarsTime[trltToGlobalIndex][val[grounding][freeVars]]);
                            }
                            for(size_t countedVars = 0 ; countedVars < clearer[key][predicate]["counted"].size() ; countedVars++){
                                const vector<int> & counted_var_info = clearer[key][predicate]["counted"][countedVars];
                                int trltToGlobalIndex = translatePreconditionToGlobalArguments[counted_var_info[0]];
                                int countedVariableType = counted_var_info[2];

                                const vector<int> & counted_var_objects = mutexFDRSATVarsTime[key][val[grounding]][counted_var_info[1]];
								cout << "countedVariableType " << key;
							   	for (int x : val[grounding]) cout << " " << x;
								cout << " -> " << " " << countedVariableType << " "  << mutexFDRSATVarsTime[key][val[grounding]].size() << " " << counted_var_info[1] << endl;
								assert(counted_var_objects.size() == upperTypeindex[countedVariableType] - lowerTypeindex[countedVariableType] + 1);
								if(counted_var_objects.size() == size_t(upperTypeindex[countedVariableType] - lowerTypeindex[countedVariableType]) + 1){cout << "TEST" << endl;}
								else {cout << "NO" << endl;}
                                int cntOfType = get_counted_of_type_var(solver, capsule, timestep, trltToGlobalIndex, countedVariableType, parameterVarsTime);
                                int equals_var = get_equals_var(solver, capsule, timestep, timestep, trltToGlobalIndex, key, counted_var_info[1], val[grounding], countedVars,
                                    counted_var_objects, countedVariableType, parameterVarsTime);
                                leftImplication.push_back(cntOfType);
                                rightImplication.push_back(equals_var);
                            }
                            for(size_t p = 0 ; p < mutexFDRVars[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1].size() ; p++){
                                if(mutexFDRVars[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1][p] == predicate){
                                    rightImplication.push_back(mutexFDRSATVarsTime[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1][p]);
                                    break;
                                }
                            }

                            for (const int & l : rightImplication)
                                andImplies(solver,leftImplication,l);
                        }
                    }
                    
                    while(all_facts[lowerIndexGroundedPredicate].first == predicate){

                        std::vector<int> leftImplication;
                        bool invalidSupport =false;
                        leftImplication.push_back(actionVarsTime[action]);
                        for(size_t grounding = 0 ; grounding < all_facts[lowerIndexGroundedPredicate].second.size() ; grounding++){
                            if(translatePreconditionToGlobalArguments[grounding] == -1){
                                if (all_facts[lowerIndexGroundedPredicate].second[grounding] == pwlObjToSATObject[precObjec.arguments[grounding].index]) continue;
                                invalidSupport = true;
                                break;
                            }
                            if (parameterVarsTime[translatePreconditionToGlobalArguments[grounding]].count(all_facts[lowerIndexGroundedPredicate].second[grounding])){
                                leftImplication.push_back(parameterVarsTime[translatePreconditionToGlobalArguments[grounding]][all_facts[lowerIndexGroundedPredicate].second[grounding]]);
                            }else{
                                invalidSupport = true;
                                break;
                            }

                        }
                        if (!invalidSupport)
                            andImplies(solver, leftImplication, previousTimeMutexPredicateVars[lowerIndexGroundedPredicate]);
                        leftImplication.clear();
                        lowerIndexGroundedPredicate++;

                    }

                    translatePreconditionToGlobalArguments.clear();
                    lowerLimitPredicate.clear();

                }
                clauseNumber(preconditionImplications);

                const auto effs = task.actions[action].get_effects();
                for (size_t eff = 0; eff < effs.size(); eff++) {
                    //DEBUG(cout << "\t\teffect #" << eff  << " " << effs.size() << endl);
                    
                    const auto & effObjec = effs[eff];
                    int predicate = effObjec.predicate_symbol;
                    std::vector<int> translateEffectToGlobalArguments;

                    for(size_t argument = 0 ; argument < effObjec.arguments.size() ; argument++){
                        if (effObjec.arguments[argument].constant){
                            translateEffectToGlobalArguments.push_back(-1);
                            continue;
                        }
                        int indexInActionSchema = effObjec.arguments[argument].index;
                        int actionSchemaToGlobalArguments = actionArgumentPositions[action][indexInActionSchema];
                        translateEffectToGlobalArguments.push_back(actionSchemaToGlobalArguments);
                    }

                    std::vector<int> lowerLimitPredicate;
                    std::vector<int> typesOfPredicate;

                    for(size_t argument = 0 ; argument < effObjec.arguments.size() ; argument++){
                        if(translateEffectToGlobalArguments[argument] == -1){
                            lowerLimitPredicate.push_back(pwlObjToSATObject[effObjec.arguments[argument].index]);
                            continue;
                        }
                        int type = typeOfArgument[translateEffectToGlobalArguments[argument]];
                        int lower = lowerTypeindex[type];
                        typesOfPredicate.push_back(type);
                        lowerLimitPredicate.push_back(lower);
                    }

                    int lowerIndexGroundedPredicate = all_facts_index[{effObjec.predicate_symbol, lowerLimitPredicate}];

                    if (effObjec.negated){
                        // TODO deleting effect

                        map<int, vector<vector<int>>> correspondingFAMs = idek[predicate][typesOfPredicate];
                        for(auto const& [key, val] : correspondingFAMs){
                            for(size_t grounding = 0 ; grounding < val.size() ; grounding++){
                                vector<int> negation;
                                negation.push_back(actionVar);
                                for(size_t freeVars = 0 ; freeVars < clearer[key][predicate]["free"].size() ; freeVars++){
                                    int trltToGlobalIndex = translateEffectToGlobalArguments[clearer[key][predicate]["free"][freeVars][0]];
                                    negation.push_back(parameterVarsTime[trltToGlobalIndex][val[grounding][freeVars]]);
                                }
                                for(size_t countedVars = 0 ; countedVars < clearer[key][predicate]["counted"].size() ; countedVars++){
                                    const vector<int> & counted_var_info = clearer[key][predicate]["counted"][countedVars];
                                    int trltToGlobalIndex = translateEffectToGlobalArguments[counted_var_info[0]];
                                    int countedVariableType = counted_var_info[2];

                                    const vector<int> & counted_var_objects = mutexFDRSATVarsNextTime[key][val[grounding]][counted_var_info[1]];
                                    int cntOfType = get_counted_of_type_var(solver, capsule, timestep, trltToGlobalIndex, countedVariableType, parameterVarsTime);
                                    int equals_var = get_equals_var(solver, capsule, timestep, timestep+1, trltToGlobalIndex, key, counted_var_info[1], val[grounding], countedVars,
                                        counted_var_objects, countedVariableType, parameterVarsTime);
                                    negation.push_back(cntOfType);
                                    negation.push_back(equals_var);
                                }
                                for(size_t p = 0 ; p < mutexFDRVars[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1].size() ; p++){
                                    if(mutexFDRVars[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1][p] == predicate){
                                        negation.push_back(mutexFDRSATVarsNextTime[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1][p]);
                                        break;
                                    }
                                }

                                notAll(solver, negation);
                            }
                        }


                        while(all_facts[lowerIndexGroundedPredicate].first == effObjec.predicate_symbol){

                            std::vector<int> leftImplication;
                            bool invalidSupport =false;
                            int causeVariable = capsule.new_variable();
                            DEBUG(capsule.registerVariable(causeVariable, "deleter@" + to_string(timestep) + "-" + factToString[lowerIndexGroundedPredicate]));

                            deleters[lowerIndexGroundedPredicate].push_back(causeVariable);
                            implies(solver,causeVariable,actionVarsTime[action]);
                            clauseNumber(causeVariablesImplications);

                            leftImplication.push_back(actionVarsTime[action]);
                            for(size_t grounding = 0 ; grounding < all_facts[lowerIndexGroundedPredicate].second.size() ; grounding++){
                                if(translateEffectToGlobalArguments[grounding] == -1){
                                    if (all_facts[lowerIndexGroundedPredicate].second[grounding] == pwlObjToSATObject[effObjec.arguments[grounding].index]) continue;
                                    invalidSupport = true;
                                    break;
                                }
                                if (parameterVarsTime[translateEffectToGlobalArguments[grounding]].count(all_facts[lowerIndexGroundedPredicate].second[grounding])){
                                    leftImplication.push_back(parameterVarsTime[translateEffectToGlobalArguments[grounding]][all_facts[lowerIndexGroundedPredicate].second[grounding]]);
                                        implies(solver,causeVariable,parameterVarsTime[translateEffectToGlobalArguments[grounding]][all_facts[lowerIndexGroundedPredicate].second[grounding]]);
                                        clauseNumber(causeVariablesImplications);
                                }else{
                                    invalidSupport = true;
                                    break;
                                }

                            }
                            if (!invalidSupport)
                                andImpliesNot(solver, leftImplication, currentTimeMutexPredicateVars[lowerIndexGroundedPredicate]);
                            else assertNot(solver, causeVariable);
                            leftImplication.clear();

                            lowerIndexGroundedPredicate++;

                        }
                    } else {
                        // TODO adding effects
                        //

                        map<int, vector<vector<int>>> correspondingFAMs = idek[predicate][typesOfPredicate];
                        for(auto const& [key, val] : correspondingFAMs){
                            for(size_t grounding = 0 ; grounding < val.size() ; grounding++){
								// actual effect
                                vector<int> leftImplication;
                                vector<int> rightImplication;
                                vector<int> rightImplicationCauseVariables;
                                leftImplication.push_back(actionVar);
                            	

                                for(size_t freeVars = 0 ; freeVars < clearer[key][predicate]["free"].size() ; freeVars++){
                                    int trltToGlobalIndex = translateEffectToGlobalArguments[clearer[key][predicate]["free"][freeVars][0]];
                                    leftImplication.push_back(parameterVarsTime[trltToGlobalIndex][val[grounding][freeVars]]);
                                }
                                for(size_t countedVars = 0 ; countedVars < clearer[key][predicate]["counted"].size() ; countedVars++){
                                    const vector<int> & counted_var_info = clearer[key][predicate]["counted"][countedVars];
                                    int trltToGlobalIndex = translateEffectToGlobalArguments[counted_var_info[0]];
                                    int countedVariableType = counted_var_info[2];

                                    const vector<int> & counted_var_objects = mutexFDRSATVarsNextTime[key][val[grounding]][counted_var_info[1]];
                                    int cntOfType = get_counted_of_type_var(solver, capsule, timestep, trltToGlobalIndex, countedVariableType, parameterVarsTime);
                                    int equals_var = get_equals_var(solver, capsule, timestep, timestep+1, trltToGlobalIndex, key, counted_var_info[1], val[grounding], countedVars,
                                        counted_var_objects, countedVariableType, parameterVarsTime);
                                    leftImplication.push_back(cntOfType);
                                    rightImplication.push_back(equals_var);


									int causeVariable = capsule.new_variable();
									// TODO Add good debugging name
		                            DEBUG(capsule.registerVariable(causeVariable, "fdr-adder@" + to_string(timestep) + "-FAM"));
									changers[key][val[grounding]][counted_var_info[1]].push_back(causeVariable);
									rightImplicationCauseVariables.push_back(causeVariable);
                                }
                                for(size_t p = 0 ; p < mutexFDRVars[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1].size() ; p++){
                                    if(mutexFDRVars[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1][p] == predicate){
                                        rightImplication.push_back(mutexFDRSATVarsNextTime[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1][p]);
                                
										int causeVariable = capsule.new_variable();
										// TODO Add good debugging name
		                            	DEBUG(capsule.registerVariable(causeVariable, "fdr-adder@" + to_string(timestep) + "-FAM"));
										changers[key][val[grounding]][mutexFDRVars[key][val[grounding]].size()-1].push_back(causeVariable);
										rightImplicationCauseVariables.push_back(causeVariable);
										break;
                                    }
                                }

                                for (const int & l : rightImplication)
                                    andImplies(solver,leftImplication,l);

								// preparation for frame axioms: truth of the cause variables
                                for (size_t rightIndex = 0; rightIndex < rightImplication.size(); rightIndex++){
									int rightImplied = rightImplication[rightIndex];
									int causeVariable = rightImplicationCauseVariables[rightIndex]; 

									// if this cause happens all its conditions must be true
									implies(solver, causeVariable, rightImplied);
									for (const int & l : leftImplication)
										implies(solver, causeVariable, l);
								}
                            }
                        }

                        while(all_facts[lowerIndexGroundedPredicate].first == effObjec.predicate_symbol){

                            std::vector<int> leftImplication;
                            bool invalidSupport =false;
                            int causeVariable = capsule.new_variable();
                            DEBUG(capsule.registerVariable(causeVariable, "adder@" + to_string(timestep) + "-" + factToString[lowerIndexGroundedPredicate]));

                            adders[lowerIndexGroundedPredicate].push_back(causeVariable);
                            implies(solver,causeVariable,actionVarsTime[action]);

                            leftImplication.push_back(actionVarsTime[action]);
                            for(size_t grounding = 0 ; grounding < all_facts[lowerIndexGroundedPredicate].second.size() ; grounding++){
                               if(translateEffectToGlobalArguments[grounding] == -1){
                                    if (all_facts[lowerIndexGroundedPredicate].second[grounding] == pwlObjToSATObject[effObjec.arguments[grounding].index]) continue;
                                    invalidSupport = true;
                                    break;
                                }
                                if (parameterVarsTime[translateEffectToGlobalArguments[grounding]].count(all_facts[lowerIndexGroundedPredicate].second[grounding])){
                                    leftImplication.push_back(parameterVarsTime[translateEffectToGlobalArguments[grounding]][all_facts[lowerIndexGroundedPredicate].second[grounding]]);
                                    implies(solver,causeVariable,parameterVarsTime[translateEffectToGlobalArguments[grounding]][all_facts[lowerIndexGroundedPredicate].second[grounding]]);
                                    clauseNumber(causeVariablesImplications);
                                }else{
                                    invalidSupport = true;
                                    break;
                                }
                            }
                            if (!invalidSupport)
                                andImplies(solver, leftImplication, currentTimeMutexPredicateVars[lowerIndexGroundedPredicate]);
                            else assertNot(solver, causeVariable);
                            leftImplication.clear();

                            lowerIndexGroundedPredicate++;

                        }

                        //int fact = -1; // the number of the fact this action adds
                        //int causeVariable = capsule.new_variable();
                        // TODO register

                        //adders[fact].push_back(causeVariable);
                        //implies(solver,causeVariable,actionVar);
                        //implies(solver,causeVariable,parameterVar1);
                        //implies(solver,causeVariable,parameterVar2); // and so on
                    }

                    translateEffectToGlobalArguments.clear();
                    lowerLimitPredicate.clear();

                }

                clauseNumber(effectImplications);

                // nullary preconditions
                for (int p : *setPosNullaryPrec[action])
                    implies(solver,actionVar,lastNullary[p]);
                for (int p : *setNegNullaryPrec[action])
                    impliesNot(solver,actionVar,lastNullary[p]);

                // nullary effects
                for (int p : *setPosNullaryEff[action])
                    implies(solver,actionVar,currentNullary[p]);
                for (int p : *setNegNullaryEff[action])
                    impliesNot(solver,actionVar,currentNullary[p]);
                clauseNumber(nullary);
            }

            // TODO Frame axioms
            // Types: f@t and -f@t+1 -> disjunction over deleters
            // Types: -f@t and f@t+1 -> disjunction over adders
            // cause variable C  from the adder/deleter lists
            // c -> action
            // c -> parameters
            // f@t and -f@t+q -> c_1 v c_2 v c_3 v ...

            for(size_t fact = 0 ; fact < previousTimeMutexPredicateVars.size() ; fact++){
                impliesPosAndNegImpliesOr(solver, previousTimeMutexPredicateVars[fact], currentTimeMutexPredicateVars[fact], deleters[fact]);
                impliesPosAndNegImpliesOr(solver, currentTimeMutexPredicateVars[fact], previousTimeMutexPredicateVars[fact], adders[fact]);
            }
            
		
			for (const auto & [fam, _fam] : mutexFDRSATVarsNextTime){
				for (const auto & [free_grounding, counted_groundings] : _fam){
					for (size_t counted = 0; counted < counted_groundings.size(); counted++){
						const vector<int> & previousStateVars = mutexFDRSATVarsTime[fam][free_grounding][counted]; 
						const vector<int> & nextStateVars = counted_groundings[counted]; 

						int different = get_different_var(solver,capsule,previousStateVars, nextStateVars);

						impliesOr(solver, different, changers[fam][free_grounding][counted]);	
					}
				}
			}
			
			
			clauseNumber(frameAxioms);


            for (int n : task.nullary_predicates){
                vector<int> adder;
                for (int a : nullaryAchiever[n])
                adder.push_back(actionVarsTime[a]);
                impliesPosAndNegImpliesOr(solver,currentNullary[n], lastNullary[n], adder);

                vector<int> deleter;
                for (int d : nullaryDestroyer[n])
                deleter.push_back(actionVarsTime[d]);
                impliesPosAndNegImpliesOr(solver,lastNullary[n], currentNullary[n], deleter);
            }
            lastNullary = currentNullary;
            clauseNumber(nullary);
            



            atMostOne(solver,capsule,actionVarsTime);
             if (limit == -1) atLeastOne(solver,capsule,actionVarsTime);
            clauseNumber(oneAction);

            swap(previousTimeMutexPredicateVars,currentTimeMutexPredicateVars);
            swap(mutexFDRSATVarsNextTime,mutexFDRSATVarsTime);
        }

        // TODO: assert that the goal is true. This should reference the previousTimeMutexPredicateVars
        vector<int> factsInGoalState;
        for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
            const AtomicGoal & goalAtom = task.goal.goal[goal];
            //pddl_fm_atom_t *a = pddlFmNewEmptyAtom(goalAtom.args.size());
            int pred = goalAtom.predicate;
            int goalStateFact;
            vector<int> translatedArgs;
            for(size_t arg = 0; arg < goalAtom.args.size() ; arg++){
                translatedArgs.push_back(pwlObjToSATObject[goalAtom.args[arg]]);
            }
            for(size_t fact = 0 ; fact < all_facts.size() ; fact++){
                if(all_facts[fact].first == pred && all_facts[fact].second == translatedArgs){
                    factsInGoalState.push_back(fact);
                    break;
                }
            }
            
        }
        for(size_t fact = 0 ; fact < all_facts.size() ; fact++){
            if(std::find(factsInGoalState.begin(), factsInGoalState.end(), fact) != factsInGoalState.end()){
                assertYes(solver,previousTimeMutexPredicateVars[fact]);
            }
        }


        // nullary goals
        for (int g : task.goal.positive_nullary_goals)
            assertYes(solver,lastNullary[g]);	
        for (int g : task.goal.negative_nullary_goals)
            assertNot(solver,lastNullary[g]);	
        clauseNumber(nullary);


        //DEBUG(capsule.printVariables());

        int totalClauses = 0;
        for (auto [k,v] : clauseCounter){
            cout << setw(30) << setfill('-') << k << " " << setw(8) << v << endl;
            totalClauses += v;
        }
        cout << setw(30) << setfill('-') << "TOTAL CLAUSES" << " " << setw(8) << totalClauses << " not accounted for " << get_number_of_clauses() - totalClauses << endl;


        double totalTime = 0;
        for (auto [k,v] : timings){
            cout << setw(30) << setfill('-') << k << " " << setw(8) << v << endl;
            totalTime += v;
        }
        cout << setw(30) << setfill('-') << "TOTAL Time" << " " << setw(8) << totalTime << endl;

        int state = ipasir_solve(solver);
        timesplit(SATSOLVER);
        if (state == 10){
            DEBUG(capsule.printVariableTruth(solver));
        
            // extract the plan
            vector<LiftedOperatorId> plan;
            for (int time = 0; time < timesteps; time++){
                cout << "timestep " << time << endl;
                for (size_t action = 0; action < task.actions.size(); action++){
                    int var = actionVars[time][action];
                    if (ipasir_val(solver,var) > 0){

                        cout << "  " << task.actions[action].get_name();
                        auto params = task.actions[action].get_parameters();
                        vector<int> arguments;
                        for (size_t l = 0; l < params.size(); l++) {
                            int p = actionArgumentPositions[action][l];
                            cout << " " << l << ":";
                            for (int o = lowerTypeindex[typeOfArgument[p]] ; o <= upperTypeindex[typeOfArgument[p]] ; o++){
                                if (ipasir_val(solver,parameterVars[time][p][o]) > 0){
                                    cout << " " << task.objects[satObjectToPWLObject[o]].getName();
                                    arguments.push_back(satObjectToPWLObject[o]);
                                }
                            }
                        }
                        cout << endl;
                        
                        LiftedOperatorId op (action, move(arguments));
                        plan.push_back(op);
                    }
                }
            }

            print_plan(plan,task);
            cout << "Solution found." << endl;
            exit(0);
        
        
        } else {
            DEBUG(cout << "formula is UNSAT" << endl);
        }


    }


	return utils::ExitCode::SEARCH_UNSOLVED_INCOMPLETE;
}
