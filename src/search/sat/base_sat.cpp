#include "base_sat.h"
#include "../utils/system.h"
#include "../search_engines/utils.h"
#include <iostream>

using namespace std;

BaseSATEncoding::BaseSATEncoding(const Task & _task): task(_task){
    numObjs = task.objects.size();
    numTypes = task.type_names.size();

    cout << "- re-inferring type hierarchy..." << endl;
    reinferTypeHierarchy();
    cout << "- compute direct parents..." << endl;
    computedirectParents();
    cout << "- PWL objects to types..." << endl;
    assignPWLObjectsToTypes();
    cout << "- make objects in type continuous..." << endl;
    makeObjectsContinuous();
	cout << "- computing action argument structure..." << endl;
	computeActionArgumentStructure();
	cout << "- compute supporting tuples from init for preconditions..." << endl;
	computeSupportingTuples();
	cout << "- create datastructures for nullary predicates..." << endl;
	createIterableNullaries();

    // Debug output
    for (int i = 0; i < numTypes; i++) {
        cout << task.type_names[i] << " -> {";
        bool first = true;
        for (auto p : parents[i]) {
            if (first) {
                first = false;
            } else {
                cout << ", ";
            }
            cout << task.type_names[p];
        }
        cout << "}" << " direct parent: " << (directparents[i] == -1?"none":task.type_names[directparents[i]]) << endl;
    }
    cout << "Getting here ... " << endl;
}

void BaseSATEncoding::assignPWLObjectsToTypes(){
	// looping over all objects
	types = new unordered_set<int>[task.type_names.size()];
    for (size_t obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (size_t i = 0; i < oTypes.size(); i++) {
            int j = oTypes[i];
            types[j].insert(obj);
        }
    }
}


    ////// Rearrange the objects to that types are continuous
void BaseSATEncoding::makeObjectsContinuous(){
    std::unordered_set<int>* children = new unordered_set<int>[numTypes];
    std::unordered_set<int>* toptypes = new unordered_set<int>;
    for (int i = 0; i < numTypes; i++) {
        if (parents[i].size() == 0) {
            toptypes->insert(i);
        } else {
            for (int p: parents[i]) {
                children[p].insert(i);
                //ps[i].insert(p);
            }
        }
    }

    // sort obj such that objects of same parent type are adjacent
    upperTypeindex = new int[numTypes];
    lowerTypeindex = new int[numTypes];
    pwlObjToSATObject = new int[numObjs];
    satObjectToPWLObject = new int[numObjs];

    int r = 0;
    unordered_set<int> done;
    for (int t: *toptypes) {
        r = sortObjs(r, t, children, done);
    }


	//DEBUG(
    for (size_t i = 0; i < task.objects.size(); i++) {
        cout << task.objects[i].getName() << " ";
    }
    cout << endl;

    for (int i = 0; i < numTypes; i++) {
        cout << task.type_names[i] << ":\t" << lowerTypeindex[i] << "-" << upperTypeindex[i] << " = {";
        for (int j = lowerTypeindex[i]; j <= upperTypeindex[i]; j++) {
            if (j > lowerTypeindex[i]) {
                cout << ", ";
            }
            int k = satObjectToPWLObject[j];
            cout << task.objects[k].getName();
        }
        cout << "}" << endl;
    }
	//);
}




void BaseSATEncoding::reinferTypeHierarchy(){
    int numTypes = task.type_names.size();
	std::unordered_set<int>* types = new unordered_set<int>[numTypes];
    for (size_t obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (size_t i = 0; i < oTypes.size(); i++) {
            int j = oTypes[i];
            types[j].insert(obj);
        }
    }
    parents.resize(numTypes); // todo: equal sets
    for (int child = 0; child < numTypes; child++) {
		if (types[child].size() == 0) continue;

        for (int parent = 0; parent < numTypes; parent++) {
            if (child == parent) continue;
            if (types[child].size() <= types[parent].size()) {
                bool isSubset = true;
                for (int elem: types[child]) {
                    if (types[parent].find(elem) == types[parent].end()) {
                        isSubset = false;
                        break;
                    }
                }
                if (isSubset) {
                    parents[child].insert(parent);
                }
            }
        }
    }
	delete[] types;
}



void BaseSATEncoding::computedirectParents(){
    // make directional if there are multiple identical types
    int numTypes = parents.size();
	for (int i = 0; i < numTypes; i++) {
        for (int j = 0; j < numTypes; j++) {
            if (i == j) continue;
                if ((parents[i].find(j) != parents[i].end())
                    && (parents[j].find(i) != parents[j].end())) {
                    parents[i].erase(parents[i].find(j));
                }
		}
	}
    
    // make sparse
	for (int j = 0; j < numTypes; j++) {
        for (int i = 0; i < numTypes; i++) {
            if (i == j) continue;
            for (int k = 0; k < numTypes; k++) {
                if ((i == k) || (j == k)) continue;
				//j is parent of i
				//k is parent of j
				//k is parent of i
				//then erase: k is parent of i
                if ((parents[i].find(j) != parents[i].end())
                    && (parents[j].find(k) != parents[j].end())
                    && (parents[i].find(k) != parents[i].end())) {
                    parents[i].erase(parents[i].find(k));
                }
            }
        }
    }

	directparents.resize(parents.size());

	for(unsigned int type = 0; type < parents.size(); type++)
		if (parents[type].size() == 0){
			directparents[type] = -1;
		} else if (parents[type].size() == 1){
			directparents[type] = *(parents[type].begin());
		} else {
			cout << "Type " << type << " has multiple direct parents ... this is impossbile." << endl;
   			exit_with(utils::ExitCode::SEARCH_UNSUPPORTED);
		}
}


int BaseSATEncoding::sortObjs(int index, int type, std::unordered_set<int>* children, std::unordered_set<int> & done) {
    lowerTypeindex[type] = index;
    for (int st : children[type]) {
        index = sortObjs(index, st, children, done);
    }
    for(int o : types[type]) {
        if (done.find(o) == done.end()) {
            pwlObjToSATObject[o] = index;
            satObjectToPWLObject[index] = o;
            index++;
            done.insert(o);
        }
    }
    upperTypeindex[type] = index - 1;
    return index;
}

void BaseSATEncoding::computeSupportingTuples(){
	preconditionSupportingTuplesFromInit.resize(task.actions.size());
	for (size_t action = 0; action < task.actions.size(); action++){
        const auto precs = task.actions[action].get_precondition();
		
		preconditionSupportingTuplesFromInit[action].resize(precs.size());
        for (size_t prec = 0; prec < precs.size(); prec++) {
        	
			const auto & precObjec = precs[prec];
			int predicate = precObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue;


			vector<pair<vector<int>,int>> & mySupportingTuples = preconditionSupportingTuplesFromInit[action][prec];

			// TODO: sind die nicht nach den predikaten sortiert????
			for (size_t i = 0; i < task.get_static_info().get_relations().size(); i++) {
			    auto rel = task.get_static_info().get_relations()[i];
			    auto tuple = task.get_static_info().get_tuples_of_relation(i);

				if (predicate != rel.predicate_symbol) continue;
				
				// this is the correct predicate
			    for (vector<int> groundA: tuple) {
					bool notApplicable = false;
					for (size_t j = 0; j < groundA.size(); j++){
						int myObjIndex = pwlObjToSATObject[groundA[j]];
						if (precObjec.arguments[j].constant){
							if (precObjec.arguments[j].index != groundA[j])
								notApplicable = true;
						} else {
							int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
							if (myObjIndex < lowerTypeindex[typeOfArgument[myParam]] ||
									myObjIndex > upperTypeindex[typeOfArgument[myParam]])
								notApplicable = true;
						}
					}
			    	
					if (notApplicable) continue;
					mySupportingTuples.push_back({groundA,-1}); // static ..
				}
			}

			int currentStartingPos = 0;
			for (size_t i = 0; i < task.initial_state.get_relations().size(); i++) {
			    auto rel = task.initial_state.get_relations()[i];
			    auto tuple = task.initial_state.get_tuples_of_relation(i);
				
				if (predicate != rel.predicate_symbol) {
					currentStartingPos += tuple.size();
					continue;
				}
			    
				for (vector<int> groundA: tuple) {
					bool notApplicable = false;
					for (size_t j = 0; j < groundA.size(); j++){
						int myObjIndex = pwlObjToSATObject[groundA[j]];
						if (precObjec.arguments[j].constant){
							if (precObjec.arguments[j].index != groundA[j])
								notApplicable = true;
						} else {
							int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
							if (myObjIndex < lowerTypeindex[typeOfArgument[myParam]] ||
									myObjIndex > upperTypeindex[typeOfArgument[myParam]])
								notApplicable = true;
						}
					}
			    	
					if (notApplicable) {
						currentStartingPos++;
						continue;
					}
			    	mySupportingTuples.push_back({groundA,currentStartingPos++});
			    }
			}
		}
	}
}

void BaseSATEncoding::computeActionArgumentStructure(){
	map<int,int> maxNum;
	map<int,int> objCount;

    for (auto a: task.actions) {
        maxArity = max(maxArity, (int) a.get_parameters().size());
        maxPrec = max(maxPrec, (int) a.get_precondition().size());
		
		map<int,int> thisCount;
		for (auto para : a.get_parameters())
			thisCount[para.type] += 1;

		for (auto p : thisCount)
			if (maxNum[p.first] < p.second)
				maxNum[p.first] = p.second;
    }

	for (auto p : maxNum){
		firstArgumentOfType[p.first] = numberOfArgumentPositions;
		for (int i = numberOfArgumentPositions; i < numberOfArgumentPositions + p.second; i++)
			typeOfArgument[i] = p.first;
		numberOfArgumentPositions += p.second;
	}


	for (auto a: task.actions) {
		map<int,int> thisCount;
		for (auto para : a.get_parameters()){
			actionArgumentPositions[a.get_index()][para.index] = firstArgumentOfType[para.type] + thisCount[para.type];
			thisCount[para.type] += 1;
		}

		
		cout << "Action #" << a.get_index() << " "  << a.get_name() << ":";
		for (auto [a,b] : actionArgumentPositions[a.get_index()])
			cout << " " << a << "->" << b;
		cout << endl;
	}
}


void BaseSATEncoding::createIterableNullaries() {
    for (size_t a = 0; a < task.actions.size(); a++) {
        setPosNullaryPrec.push_back(new unordered_set<int>);
        setNegNullaryPrec.push_back(new unordered_set<int>);
        setPosNullaryEff.push_back(new unordered_set<int>);
        setNegNullaryEff.push_back(new unordered_set<int>);

        auto posPrec = task.actions[a].get_positive_nullary_precond();
        for (size_t f = 0; f < posPrec.size(); f++) {
            if (posPrec[f]) {
                setPosNullaryPrec[a]->insert(f);
            }
        }
        auto negPrec = task.actions[a].get_negative_nullary_precond();
        for (size_t f = 0; f < negPrec.size(); f++) {
            if (negPrec[f]) {
                setNegNullaryPrec[a]->insert(f);
            }
        }
        auto posEff = task.actions[a].get_positive_nullary_effects();
        for (size_t f = 0; f < posEff.size(); f++) {
            if (posEff[f]) {
                setPosNullaryEff[a]->insert(f);
				nullaryAchiever[f].push_back(a);
            }
        }
        auto negEff = task.actions[a].get_negative_nullary_effects();
        for (size_t f = 0; f < negEff.size(); f++) {
            if (negEff[f]) {
                setNegNullaryEff[a]->insert(f);
				nullaryDestroyer[f].push_back(a);
            }
        }
    }
}
