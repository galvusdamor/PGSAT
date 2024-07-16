#ifndef SEARCH_BASE_SAT_H
#define SEARCH_BASE_SAT_H

#include <vector>
#include <set>
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

    private:
        void makeObjectsContinuous();
        void reinferTypeHierarchy();
        void assignPWLObjectsToTypes();
        void computedirectParents();

        int numTypes;



        // recursive function calls; internal use only
        int sortObjs(int index, int type, std::unordered_set<int>* children, std::unordered_set<int> & done);

};

#endif