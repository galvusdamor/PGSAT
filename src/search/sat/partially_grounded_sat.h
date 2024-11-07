#ifndef SEARCH_PARTIALLY_GROUNDED_SAT_H
#define SEARCH_PARTIALLY_GROUNDED_SAT_H

#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <ctime>
#include <chrono>
#include "base_sat.h"
#include "sat_encoder.h"
#include "../utils/system.h"
#include "../task.h"

class PartiallyGroundedSAT : public BaseSATEncoding{

    enum LFG_VAR_TYPES { 
        LFG_FREE,
        LFG_COUNTED,
        LFG_CONST
    }; 

    enum COUNTED_VAR_INFO { 
        INDEX,
        PARAM_ID,
        TYPE
    };

private:
    std::vector<std::pair<int, std::vector<int>>> all_facts;
    std::map<std::pair<int, std::vector<int>>,int> all_facts_index;
    
	std::vector<int> uncovered_facts;
	std::unordered_set<int> uncovered_facts_set;
	std::unordered_map<int,int> fact_index_to_uncovered;
	std::unordered_map<int,int> lower_predicate_index_in_uncovered;
	std::map<int, std::vector<std::pair<int,std::vector<int>>>> fact_to_mutexes_with_counted_info;
	std::vector<std::pair<int, std::vector<int>>> fam_based_mutexes;

    std::vector<std::string> factToString;
    std::map<int, std::map<int, std::map<LFG_VAR_TYPES, std::vector<std::vector<int>>>>> clearer;
    std::map<int,std::map<std::vector<int>, std::vector<std::vector<int>>>> mutexFDRVars;
    std::map<int, std::map<std::vector<int>, std::map<int, std::vector<std::vector<int>>>>> idek;
    void generatePredicateStrings();
	std::vector<int> generateFactVars(sat_capsule & capsule, int timestep, std::vector<std::string>);
    std::map<int, std::map<std::vector<int>, std::vector<std::vector<int>>>> generateFAMVars(void* solver, sat_capsule & capsule, int timestep);
    
    int get_equals_var(void* solver, sat_capsule & capsule, int time_action, int time_state, int action_argument_position,\
        int FAM_group, int param_id, std::vector<int> free_variable_grounding, int counted_var,
        const std::vector<int> & counted_var_objects, int counted_var_type, const std::vector<std::map<int,int>> & parameterVars);
    int get_counted_of_type_var(void* solver, sat_capsule & capsule, int time_step, int action_argument_position, int type,
        const std::vector<std::map<int,int>> & parameterVars);
	std::vector<int> get_vars_for_const(int time_state, int action_argument_position, int object, const std::vector<std::map<int,int>> & parameterVars);
	std::vector<int> get_counted_vars_for_const(int object, const std::vector<int> & counted_var_objects, int counted_var_type);


	int get_different_var(void* solver, sat_capsule & capsule, const std::vector<int> & previous, const std::vector<int> & next);
    
	std::map<std::string,double> timings;
    std::clock_t _start;
public:
    PartiallyGroundedSAT(const Task& task);
	utils::ExitCode solve(const Task& task, int limit, bool optimal, bool incremental);
};


typedef size_t tSize;

#endif //SEARCH_LIFTEDRP_H
