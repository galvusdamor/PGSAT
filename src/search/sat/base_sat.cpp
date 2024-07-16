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