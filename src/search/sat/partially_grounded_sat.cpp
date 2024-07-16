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







PartiallyGroundedSAT::PartiallyGroundedSAT(const Task & task) :
    BaseSATEncoding(task){
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
                pddl_fm_atom_t *atom = pddlFmNewEmptyAtom(task.actions[aid].get_precondition()[precid].arguments.size());
                atom->pred = powerLiftedPredicatesToCPDDLPredicates[task.actions[aid].get_precondition()[precid].predicate_symbol];
                for(tSize ai = 0 ; ai < task.actions[aid].get_precondition()[precid].arguments.size() ; ai++){
                    atom->arg[ai].param = task.actions[aid].get_precondition()[precid].arguments[ai].index;
                }
                pddlFmJuncAdd(pddlFmToAnd(a->pre), &(atom->fm));
            }
        }

        a->eff = pddlFmNewEmptyAnd();
        for(size_t effid = 0 ; effid < task.actions[aid].get_effects().size() ; effid++){
            pddl_fm_atom_t *atom = pddlFmNewEmptyAtom(task.actions[aid].get_effects()[effid].arguments.size());
            atom->pred = powerLiftedPredicatesToCPDDLPredicates[task.actions[aid].get_effects()[effid].predicate_symbol];
            for(tSize ai = 0 ; ai < task.actions[aid].get_effects()[effid].arguments.size() ; ai++){
                atom->arg[ai].param = task.actions[aid].get_effects()[effid].arguments[ai].index;
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

    


    vector<set<pair<int, int>>> mutex_fixed_variable;
    vector<map<string, set<pair<int, int>>>> mutex_counted_variable;
    for (int i = 0; i < lifted_mgroups.mgroup_size; i++){
        if (pruned[i]) continue;
        set<pair<int, int>> mutex_fixed_variable_aux;
        map<string, set<pair<int, int>>> mutex_counted_variable_aux;
        for (int j = 0; j < (lifted_mgroups.mgroup + i)->cond.size; j++){
            const pddl_fm_atom_t *atom = pddlFmToAtomConst((lifted_mgroups.mgroup + i)->cond.fm[j]);
            mutex_counted_variable_aux[pddl->pred.pred[atom->pred].name].size();
            for (int k = 0; k < atom->arg_size; k++){
                if (atom->arg[k].param >= 0){
                    int param_id = atom->arg[k].param;
                    const pddl_param_t *p = (lifted_mgroups.mgroup + i)->param.param + param_id;
                    if (p->is_counted_var){
                        mutex_counted_variable_aux[pddl->pred.pred[atom->pred].name].insert({param_id , p->type-1});
                    }else{
                        mutex_fixed_variable_aux.insert({param_id, p->type-1});
                    }
                }
            }
        }
        mutex_fixed_variable.push_back(mutex_fixed_variable_aux);
        mutex_counted_variable.push_back(mutex_counted_variable_aux);
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


    //vector<pair<int, vector<int>>> all_facts;
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

    DEBUG(for(size_t i = 0 ; i < all_facts.size() ; i++){
        cout << "Predicate : " << all_facts[i].first << "; Objects :";
        for(size_t j = 0 ; j < all_facts[i].second.size() ; j++){
            cout << " " << all_facts[i].second[j];
        }
        cout << endl;
    });


    map<int, vector<int>> fact_to_mutexes;
    for(size_t facts = 0 ; facts < all_facts.size() ; facts++){
        vector<int> mutexes_with_fact;
        pair<int, vector<int>> fact = all_facts[facts];

        //cout << endl << endl << endl << "||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||" << endl;
        //cout << "Predicate : " << fact.first << "; Objects :";
        //for(size_t j = 0 ; j < fact.second.size() ; j++){
        //    cout << " " << fact.second[j] << " " << task.objects[satObjectToPWLObject[fact.second[j]]].getName();
        //}
        //cout << endl;

        //cout << endl << endl << fact.first << " " << task.predicates[fact.first].getName() << endl;
        for(size_t mutexes = 0 ; mutexes < fam_based_mutexes.size() ; mutexes++){
            pair<int, vector<int>> mutex = fam_based_mutexes[mutexes];
            //pddl_lifted_mgroup_t FAM_group = lifted_mgroups.mgroup[FAM_group_indexes[mutex.first]];
            for (int j = 0; j < (lifted_mgroups.mgroup + FAM_group_indexes[mutex.first])->cond.size; j++){
                const pddl_fm_atom_t *atom = pddlFmToAtomConst((lifted_mgroups.mgroup + FAM_group_indexes[mutex.first])->cond.fm[j]);
                if(pddl->pred.pred[atom->pred].id == powerLiftedPredicatesToCPDDLPredicates[fact.first]){
                    //cout << "entered the if checking if predicates are the same\n";
                    bool add = true;
                    //cout << "=============================================" << endl;
                    //cout << "Arg size " << atom->arg_size <<  " fam group " << FAM_group_indexes[mutex.first] << endl;
                    for (int k = 0; k < atom->arg_size; k++){
                        if (atom->arg[k].param >= 0){
                            int param_id = atom->arg[k].param;
                            const pddl_param_t *p = (lifted_mgroups.mgroup + FAM_group_indexes[mutex.first])->param.param + param_id;
                            //cout << "p->is_counted_var : " << p->is_counted_var << "; fact.second[k] : " << fact.second[k] << "; mutex.second[param_id] : " << mutex.second[param_id] << "; param_id : " << param_id << endl;
                            //cout << "p->is_counted_var : " << p->is_counted_var << "; type_of_object[fact.second[k]] : " << type_of_object[satObjectToPWLObject[fact.second[k]]] << "; p->type-1 : " << p->type-1 << endl;
                            if (!p->is_counted_var && fact.second[k] != mutex.second[param_id]){
                                add = false;
                                break;
                            }else if (p->is_counted_var && (fact.second[k] < lowerTypeindex[p->type-1] || fact.second[k] > upperTypeindex[p->type-1])){
                                add = false;
                                break;
                            }
                        }else if (atom->arg[k].param < 0 && atom->arg[k].obj != satObjectToPWLObject[fact.second[k]]){
                            //cout << "Arg pos " << k << " " << atom->arg[k].param << " " << task.objects[atom->arg[k].obj].getName() << " " 
                            //    <<  task.objects[satObjectToPWLObject[fact.second[k]]].getName() <<  " add " << add << endl;
                            add = false;
                            break;
                        }
                    }
                    //cout << add << endl;
                    if (add){
                        mutexes_with_fact.push_back(mutexes);
                    }
                }
            }
        }

        //fact_to_mutexes[facts].size();
        fact_to_mutexes[facts] = mutexes_with_fact;
        mutexes_with_fact.clear();
    }

    DEBUG(for(size_t facts = 0 ; facts < all_facts.size() ; facts++){
        cout << "Fact " << facts << " :";
        for(size_t i = 0 ; i < fact_to_mutexes[facts].size() ; i++){
            cout << " " << fact_to_mutexes[facts][i];
        }
        cout << endl;
    });

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


	cout << " done" << endl;
}


#define clauseNumber(name) clauseCounter[name]+=get_number_of_clauses()-beforeClause;beforeClause=get_number_of_clauses()
#define atMostOneParameterValue "at most one parameter value"
#define actionAllowedArguments "action allowed arguments"
#define equalsPreconditions "equals preconditions"
#define staticPrecondition "static preconditions"
#define oneAction "one Action"
#define nullary "nullary"


vector<vector<int>> PartiallyGroundedSAT::generateFactVars(sat_capsule & capsule, int timestep){
	vector<vector<int>> mutexPredicateVarsTime(all_facts.size());
	for (size_t predicate = 0; predicate < all_facts.size(); predicate++){
	    int grounded_mutex_predicate_var;
	    grounded_mutex_predicate_var = capsule.new_variable();
	    mutexPredicateVarsTime[predicate].push_back(grounded_mutex_predicate_var);
	    string arguments = "("; 
	    for(size_t object = 0 ; object < all_facts[predicate].second.size() ; object++){
			if (object) arguments += ", ";
	        arguments += task.objects[satObjectToPWLObject[all_facts[predicate].second[object]]].getName();
	    }
	    arguments += ")";
	    DEBUG(capsule.registerVariable(grounded_mutex_predicate_var,"predicate@" + to_string(timestep) + "-" + task.predicates[all_facts[predicate].first].getName() + arguments) );
	}

	


	return mutexPredicateVarsTime;
}



utils::ExitCode PartiallyGroundedSAT::solve(const Task &task, int limit, bool optimal, bool incremental) {
	cout << "Not yet implemented!" << endl;

	map<string,int> clauseCounter;

    int timesteps = 2;
    PartiallyGroundedSAT pgs = PartiallyGroundedSAT(task);
    void* solver = ipasir_init();
	sat_capsule capsule;
	int beforeClause = get_number_of_clauses();

	vector<vector<int>> previousTimeMutexPredicateVars = generateFactVars(capsule,0);
	// TODO: assert that the initial state is true.
	// one for every mutex should be true

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



	for (int timestep = 0; timestep < timesteps; timestep++){

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
		
        //parameterVars.push_back(parameterVarsTime);

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
            	DEBUG(cout << "\t\tprecondition #" << prec << endl);
            	
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
                        DEBUG(cout << "\t\tno init support for precondition #" << prec << " with pred " << predicate << " " << task.predicates[predicate].getName() << endl);
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


		// generate variables for successor state
		vector<vector<int>> currentTimeMutexPredicateVars = generateFactVars(capsule,timestep+1);
		std::unordered_map<int,int> currentNullary;
		for (int n : task.nullary_predicates){
			int nullVar = capsule.new_variable();
			currentNullary[n] = nullVar;
			DEBUG(capsule.registerVariable(nullVar,	"nullary#" + to_string(n) + "_" + to_string(timestep+1)));
		}


		// generate clauses for preconditions
        for (size_t action = 0; action < task.actions.size(); action++){
            int actionVar = actionVarsTime[action];

            /////// non-special PRECONDITIONS
            const auto precs = task.actions[action].get_precondition();
	        for (size_t prec = 0; prec < precs.size(); prec++) {
            	DEBUG(cout << "\t\tprecondition #" << prec << endl);
            	
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
			}

			map<int,vector<int>> adders, deleters;

			const auto effs = task.actions[action].get_effects();
	        for (size_t eff = 0; eff < effs.size(); eff++) {
            	DEBUG(cout << "\t\teffect #" << eff << endl);
            	
				const auto & effObjec = effs[eff];

				if (effObjec.negated){
					// TODO deleting effect
				} else {
					// TODO adding effects
					//
					int fact = -1; // the number of the fact this action adds
					int causeVariable = capsule.new_variable();
					// TODO register
					adders[fact].push_back(causeVariable);
					implies(solver,causeVariable,actionVar);
					implies(solver,causeVariable,parameterVar1);
					implies(solver,causeVariable,parameterVar2); // and so on
				}

			}

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
        atLeastOne(solver,capsule,actionVarsTime);
		clauseNumber(oneAction);

		swap(previousTimeMutexPredicateVars,currentTimeMutexPredicateVars);
    }

	// TODO: assert that the goal is true. This should reference the previousTimeMutexPredicateVars

	// nullary goals
	for (int g : task.goal.positive_nullary_goals)
		assertYes(solver,lastNullary[g]);	
    for (int g : task.goal.negative_nullary_goals)
		assertNot(solver,lastNullary[g]);	
	clauseNumber(nullary);


    DEBUG(capsule.printVariables());

	int totalClauses = 0;
	for (auto [k,v] : clauseCounter){
		cout << setw(30) << setfill('-') << k << " " << setw(8) << v << endl;
		totalClauses += v;
	}
	cout << setw(30) << setfill('-') << "TOTAL CLAUSES" << " " << setw(8) << totalClauses << " not accounted for " << get_number_of_clauses() - totalClauses << endl;

    int state = ipasir_solve(solver);
    if (state == 10){
		DEBUG(capsule.printVariableTruth(solver));
	}


	return utils::ExitCode::SEARCH_UNSOLVED_INCOMPLETE;
}
