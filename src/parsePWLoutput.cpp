#include <iostream>
#include <fstream>
#include <string>
#include <bits/stdc++.h>

using namespace std;

//WARNING: THERE IS CURRENTLY NO SUPPORT FOR CONSTANTS
int main(int argc, char** argv) {

    int num_types;
    int num_predicates;
    int num_objects;
    int facts_init_state;
    int num_goals;
    int num_actions;

    string line;
    set<int> predShouldBeType;
    map<int, vector<int>> typesToObjects;
    vector<set<int>> typesOfEachObject;
    map<string, vector<int>> actionArgTypes;

    map<int, string> indexToPred;
    map<string, int> newTypesToIndex;
    vector<string> predNames;
    map<int, map<string, vector<vector<int>>>> predToActionToArgsIndex;
    map<int, vector<vector<int>>> typeOfArgsInPred;
    map<int, vector<int>> updatedPredicateTypes;
    map<set<int>, int> compositionOfNewSuperTypes;

    //ifstream PWLoutput("output.lifted.for_example");
    ifstream PWLoutput(argv[1]);
    cout << "Rewrting Translator Output to Contain Proper Types" << endl;
    cout << "Reading from file: " << argv[1] << endl;

    //Skip initial lines until finding information about types
    while(line.find("TYPES") == string::npos){
        getline(PWLoutput, line);
    }

    string _word;
    stringstream ss(line);

    ss >> _word;
    ss >> num_types;

    //Read and save all "native" types
    for(int i = 0 ; i < num_types ; i++){
        string name; int index;
        PWLoutput >> name >> index;
        newTypesToIndex[name] = index;
        predNames.push_back(name);
    }

    PWLoutput >> _word >> num_predicates;
    //Read and save all predicates. Also already select the ones that can potentially be converted to types
    for(int i = 0 ; i < num_predicates ; i++){
        string name; int number, isStatic, arguments;
        PWLoutput >> name >> number >> arguments >> isStatic;
        indexToPred[number] = name;
        if(isStatic == 1 && arguments == 1 && name.substr(0, 5) != "type@"){//is unary and is static
            predShouldBeType.insert(number);
            newTypesToIndex[name] = newTypesToIndex.size();
            predNames.push_back(name);
        }
        // reading the argument types
        for (int j = 0; j < arguments; j++)
            PWLoutput >> _word;
    }

    /* for(auto t : predShouldBeType){
        cout << indexToPred[t] << endl;
    }

    for(const auto& [key, value] : newTypesToIndex){
        cout << key << " -> " << value << endl;
    } */

    //If no predicate can be converted to a new type there is nothing to do
    //if(predShouldBeType.size() == 0){
    //    exit(0);
    //}

    //Read all the objects while saving the types they beling to
    PWLoutput >> _word >> num_objects;
    for(int i = 0 ; i < num_objects ; i++){
        string name; int number, arguments;
        PWLoutput >> name >> number >> arguments;
        // reading the argument types
        set<int> objTypes;
        for (int j = 0; j < arguments; j++){
            int type;
            PWLoutput >> type;
            objTypes.insert(type);
            typesToObjects[type].push_back(number);
        }
        typesOfEachObject.push_back(objTypes);
    }

    //Read facts in initial state and initialise data structures to help check if a predicate can be converted to a type
    PWLoutput >> _word >> facts_init_state;
    for(int i = 0 ; i < facts_init_state ; i++){
        string fact; int number, pred, negated, arguments, object;
        PWLoutput >> fact >> number >> pred >> negated >> arguments;
        for (int j = 0; j < arguments; j++){
            PWLoutput >> object;
            if(predShouldBeType.find(pred) != predShouldBeType.end()){
                int newPredType = newTypesToIndex[indexToPred[pred]];
                //cout << newPredType << " ";
                typesOfEachObject[object].insert(newPredType);
                typesToObjects[newPredType].push_back(object);
            }
        }
    }
    for(auto& [key, value] : typesToObjects){
        sort(value.begin(), value.end());
    }

    /* for(size_t i = 0 ; i < typesOfEachObject.size() ; i++){
        typesOfEachObject.sort();
    }
    cout << endl; */

    /* for(const auto&[key, value] : typesToObjects){
        cout << predNames[key] << " :";
        for(size_t objs = 0 ; objs < value.size() ; objs++){
            cout << " " << value[objs];
        }
        cout << endl;
    } */

    vector<int> t;
    for (auto const& [key, val] : typesToObjects){
        t.push_back(key);
    }

    set<int> predicatesCantBeTypes;
    for(size_t i = 0 ; i < t.size() ; i++){
        for(size_t j = i+1 ; j < t.size() ; j++){
            vector<int> intersection;
            vector<int> t1 = typesToObjects[t[i]];
            vector<int> t2 = typesToObjects[t[j]];
            set_intersection(t1.begin(), t1.end(), t2.begin(), t2.end(), back_inserter(intersection));
            if(intersection.size() != 0 && intersection.size() != t1.size() && intersection.size() != t2.size()){
                if(t1.size() > t2.size()){
                    predicatesCantBeTypes.insert(t[j]);
                }else{
                    predicatesCantBeTypes.insert(t[i]);
                }
            }
        }
    }

    cout << "Preds that cant' be types: " << predicatesCantBeTypes.size() << endl;


    PWLoutput >> _word;
    PWLoutput >> num_goals;
    while(_word != "ACTION-SCHEMAS"){
        PWLoutput >> _word;
    }

    PWLoutput >> num_actions;

    for(int i = 0 ; i < num_actions ; i++){
        string name, arg, pred, par_const; int cost, arguments, preconditions, effects, index, type, predNum, neg, num_args, index_in_action;
        PWLoutput >> name >> cost >> arguments >> preconditions >> effects;
        for(int j = 0 ; j < arguments ; j++){
            PWLoutput >> arg >> index >> type;
            actionArgTypes[name].push_back(type);
        }
        for(int j = 0 ; j < preconditions ; j++){
            PWLoutput >> pred >> predNum >> neg >> num_args;
            vector<int> indexesInAction;
            for(int k = 0 ; k < num_args ; k++){
                PWLoutput >> par_const >> index_in_action;
                if(predShouldBeType.find(predNum) != predShouldBeType.end() && typesToObjects[actionArgTypes[name][index_in_action]].size() > typesToObjects[newTypesToIndex[pred]].size() && predicatesCantBeTypes.find(predNum) == predicatesCantBeTypes.end()){
                    actionArgTypes[name][index_in_action] = newTypesToIndex[pred];
                }else if(predShouldBeType.find(predNum) == predShouldBeType.end() && pred.substr(0, 5) != "type@" && pred != "="){
                    indexesInAction.push_back(index_in_action);
                }
            }
            predToActionToArgsIndex[predNum][name].push_back(indexesInAction);
        }
        for(int j = 0 ; j < effects ; j++){
            PWLoutput >> pred >> predNum >> neg >> num_args;
            vector<int> indexesInAction;
            for(int k = 0 ; k < num_args ; k++){
                PWLoutput >> par_const >> index_in_action;
                if(predShouldBeType.find(predNum) == predShouldBeType.end() && pred.substr(0, 5) != "type@" && pred != "="){
                    indexesInAction.push_back(index_in_action);
                }
            }
            predToActionToArgsIndex[predNum][name].push_back(indexesInAction);
        }
    }

    for (auto const& [predNum, actionNameMap] : predToActionToArgsIndex){
        int pred = predNum;
        for (auto const& [actionName, vecOfVecs] : actionNameMap){
            for(size_t vec = 0 ; vec < vecOfVecs.size() ; vec++){
                vector<int> argTypes;
                for(size_t arg = 0 ; arg < vecOfVecs[vec].size() ; arg++){
                    argTypes.push_back(actionArgTypes.at(actionName)[vecOfVecs[vec][arg]]);
                }
                typeOfArgsInPred[pred].push_back(argTypes);
            }
        }
    }

    int finalTotalTypes = num_types + predShouldBeType.size() - predicatesCantBeTypes.size();

    for(int i = 0 ; i < num_predicates ; i++){
        if(predShouldBeType.find(i) == predShouldBeType.end() && indexToPred[i] != "=" && indexToPred[i].substr(0, 5) != "type@" && predicatesCantBeTypes.find(i) == predicatesCantBeTypes.end()){
            if (typeOfArgsInPred.count(i) == 0) continue;
            updatedPredicateTypes[i] = vector<int>(typeOfArgsInPred[i][0].size(), -1);
            for (size_t j = 0 ; j < updatedPredicateTypes[i].size() ; j++) {
                int currentType = typeOfArgsInPred[i][0][j];
                bool newType = false;
                set<int> allArgTypes;
                allArgTypes.insert(currentType);
                for (size_t k = 1 ; k < typeOfArgsInPred[i].size() ; k++) {
                    if(!newType){
                        const auto& vec1 = typesToObjects[currentType];
                        const auto& vec2 = typesToObjects[typeOfArgsInPred[i][k][j]];
                        vector<int> intersection;
                        set_intersection(vec1.begin(), vec1.end(), vec2.begin(), vec2.end(), back_inserter(intersection));
                        if(intersection.size() == vec1.size() && intersection.size() != vec2.size()){
                            currentType = typeOfArgsInPred[i][k][j];
                            updatedPredicateTypes[i][j] = currentType;
                        }else if(intersection.size() == 0){
                            newType = true;
                            currentType = finalTotalTypes;
                            finalTotalTypes++;
                        }
                    }
                    allArgTypes.insert(typeOfArgsInPred[i][k][j]);
                }
                updatedPredicateTypes[i][j] = currentType;
                if(newType && compositionOfNewSuperTypes.find(allArgTypes) == compositionOfNewSuperTypes.end()){
                    int nextBestTypeWhenCantCreateType = 0;
                    bool skip = false;
                    vector<int> allObjsOfNewType;
                    for(int argType : allArgTypes){
                        allObjsOfNewType.insert(allObjsOfNewType.end(), typesToObjects[argType].begin(), typesToObjects[argType].end());
                    }
                    sort(allObjsOfNewType.begin(), allObjsOfNewType.end());
                    for(size_t types = 0 ; types < typesToObjects.size() ; types++){
                        vector<int> vec2 = typesToObjects[types];
                        vector<int> intersection;
                        set_intersection(allObjsOfNewType.begin(), allObjsOfNewType.end(), vec2.begin(), vec2.end(), back_inserter(intersection));
                        if(intersection.size() != 0 && intersection.size() != allObjsOfNewType.size() && intersection.size() != vec2.size()){
                            skip = true;
                            finalTotalTypes--;
                            //break;
                        }else if(intersection.size() == allObjsOfNewType.size() && typesToObjects[nextBestTypeWhenCantCreateType].size() > typesToObjects[types].size()){
                            nextBestTypeWhenCantCreateType = types;
                        }
                    }
                    if(!skip){
                        updatedPredicateTypes[i][j] = currentType;
                        compositionOfNewSuperTypes[allArgTypes] = currentType;
                        vector<int> objectsOfNewType;
                        for(auto t : allArgTypes){
                            for(size_t objs = 0 ; objs < typesToObjects[t].size() ; objs++){
                                objectsOfNewType.push_back(typesToObjects[t][objs]);
                                typesOfEachObject[typesToObjects[t][objs]].insert(currentType);
                            }
                        }
                        typesToObjects[currentType] = objectsOfNewType;
                    }else{
                        updatedPredicateTypes[i][j] = nextBestTypeWhenCantCreateType;
                    }
                }else if(newType){
                    finalTotalTypes--;
                    updatedPredicateTypes[i][j] = compositionOfNewSuperTypes[allArgTypes];
                }
            }

        }
    }

    //cout << num_types << " " << predShouldBeType.size() << " " <<  predicatesCantBeTypes.size() << " " <<  finalTotalTypes << endl;
    cout << "Resetting input file." << endl;

    PWLoutput.clear();
    PWLoutput.seekg(0, PWLoutput.beg);

    //ofstream typed_output("output.lifted.2");
    ofstream typed_output(argv[2]);
    cout << "Writing to file: " << argv[2] << endl;
    
    getline(PWLoutput, line);
    while(line.find("TYPES") == string::npos){
        typed_output << line << endl;
        getline(PWLoutput, line);
    }

    typed_output << "TYPES " << finalTotalTypes << endl;
    for(int i = 0 ; i < num_types ; i++){
        getline(PWLoutput, line);
        typed_output << line << endl;
    }
    for(int i = num_types ; i < predNames.size() ; i++){
        typed_output << predNames[i] << " " << i << endl;
    }
    for(const auto& [key, value] : compositionOfNewSuperTypes){
        string typeName = "";
        for(auto t : key){
            typeName += predNames[t];
        }
        typed_output << typeName << " " << value << endl;
    }

    //PREDICATES
    getline(PWLoutput, line);
    typed_output << line << endl;
    for(int i = 0 ; i < num_predicates ; i++){
        string name; int number, isStatic, arguments;
        PWLoutput >> name >> number >> arguments >> isStatic;
        if(isStatic == 1 && arguments == 1 && name.substr(0, 5) != "type@" && predicatesCantBeTypes.find(number) == predicatesCantBeTypes.end()){//is unary and is static
            typed_output << "type@";
        }
        typed_output << name << " " << number << " " << arguments << " " << isStatic << endl;
        // reading the argument types
        getline(PWLoutput, line);
        if(updatedPredicateTypes.count(i) && arguments > 0){
            getline(PWLoutput, line);
            typed_output << updatedPredicateTypes[i][0];
            for(size_t argTypes = 1 ; argTypes < updatedPredicateTypes[i].size() ; argTypes++){
                typed_output << " " << updatedPredicateTypes[i][argTypes];
            }
            typed_output << endl;
        }else if( arguments > 0){
            getline(PWLoutput, line);
            typed_output << line << endl;
        }else if( arguments == 0){
            typed_output << endl;
        }
    }

    //OBJECTS
    //getline(PWLoutput, line);
    getline(PWLoutput, line);
    typed_output << line << endl;
    for(int i = 0 ; i < num_objects ; i++){
        string name; int number, arguments;
        PWLoutput >> name >> number >> arguments;
        typed_output << name << " " << number << " " << typesOfEachObject[i].size();
        for(int types : typesOfEachObject[i]){
            typed_output << " " << types;
        }
        typed_output << endl;
        // reading the argument types
        vector<int> objTypes;
        for (int j = 0; j < arguments; j++){
            int type;
            PWLoutput >> type;
            /* objTypes.push_back(type);
            typesToObjects[type].push_back(number); */
        }
        /* typesOfEachObject.push_back(objTypes); */
    }

    //INITIAL STATE
    getline(PWLoutput, line);
    getline(PWLoutput, line);
    typed_output << line << endl;
    for(int i = 0 ; i < facts_init_state ; i++){
        string fact; int number, pred, negated, arguments, object;
        PWLoutput >> fact >> number >> pred >> negated >> arguments;
        if(predShouldBeType.find(pred) != predShouldBeType.end() && predicatesCantBeTypes.find(pred) == predicatesCantBeTypes.end()){
            typed_output << "type@";
        }
        typed_output << fact << " " << number << " " << pred << " " << negated << " " << arguments;
        for (int j = 0; j < arguments; j++){
            PWLoutput >> object;
            typed_output << " " << object;
        }
        /* if(arguments == 0){
                typed_output << " ";
        } */
        typed_output << endl;
    }

    //GOAL STATE
    getline(PWLoutput, line);
    getline(PWLoutput, line);
    typed_output << line << endl;
    for(int i = 0 ; i < num_goals ; i++){
        getline(PWLoutput, line);
        typed_output << line << endl;
    }

    //ACTION SCHEMA
    getline(PWLoutput, line);
    typed_output << line << endl;

    for(int i = 0 ; i < num_actions ; i++){
        string name, arg, pred, par_const; int cost, arguments, preconditions, effects, index, type, predNum, neg, num_args, index_in_action;
        PWLoutput >> name >> cost >> arguments >> preconditions >> effects;
        typed_output << name << " " << cost << " " << arguments << " " << preconditions << " " << effects << endl;
        for(int j = 0 ; j < arguments ; j++){
            PWLoutput >> arg >> index >> type;
            typed_output << arg << " " << index << " " << actionArgTypes[name][index] << endl;
        }

        for(int j = 0 ; j < preconditions ; j++){
            PWLoutput >> pred >> predNum >> neg >> num_args;
            if(predShouldBeType.find(predNum) != predShouldBeType.end() && predicatesCantBeTypes.find(predNum) == predicatesCantBeTypes.end()){
                typed_output << "type@";
            }
            typed_output << pred << " " << predNum << " " << neg << " " << num_args;
            for(int k = 0 ; k < num_args ; k++){
                PWLoutput >> par_const >> index_in_action;
                typed_output << " " << par_const << " " << index_in_action;
            }
            /* if(num_args == 0){
                typed_output << ' ';
            } */
            typed_output << endl;
        }
        for(int j = 0 ; j < effects ; j++){
            PWLoutput >> pred >> predNum >> neg >> num_args;
            typed_output << pred << " " << predNum << " " << neg << " " << num_args;
            for(int k = 0 ; k < num_args ; k++){
                PWLoutput >> par_const >> index_in_action;
                typed_output << " " << par_const << " " << index_in_action;
            }
            typed_output << endl;
        }
    }

    typed_output.close();
}