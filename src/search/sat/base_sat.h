#ifndef SEARCH_BASE_SAT_H
#define SEARCH_BASE_SAT_H

#include <vector>
#include <set>
#include <map>
#include "../task.h"

class BaseSATEncoding{
    public:
        BaseSATEncoding(const Task & _task);
    protected:
        const Task & task;
        std::vector<std::unordered_set<int>> parents;
        std::vector<int> directparents;

        int numObjs;
        // for every type, the PWL ids of the objects that belong to it.
        // includes recursive objects
        std::unordered_set<int>* types;


        // SAT indicies for objects in types
        int* lowerTypeindex;
        int* upperTypeindex;
        // translate between PWL objects and SAT object IDs
        int* pwlObjToSATObject;
        int* satObjectToPWLObject;

		// action -> precondition -> list of facts that are true in the initial state.
		// each fact is a pair of (1) its arguments and (2) its index for the deleter in the lifted AC encoding
		std::vector<std::vector<std::vector<std::pair<std::vector<int>,int>>>> preconditionSupportingTuplesFromInit;
    
		std::map<int,std::map<int,int>> actionArgumentPositions;
		std::map<int,int> firstArgumentOfType;
		std::map<int,int> typeOfArgument;
	    int maxArity = 0;
	    int maxPrec = 0;
	    int numberOfArgumentPositions = 0;

    private:
        void makeObjectsContinuous();
        void reinferTypeHierarchy();
        void assignPWLObjectsToTypes();
        void computedirectParents();
		void computeSupportingTuples();
		void computeActionArgumentStructure();

        int numTypes;



        // recursive function calls; internal use only
        int sortObjs(int index, int type, std::unordered_set<int>* children, std::unordered_set<int> & done);

};

#endif
