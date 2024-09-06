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
private:
    std::vector<std::pair<int, std::vector<int>>> all_facts;
    std::map<std::pair<int, std::vector<int>>,int> all_facts_index;
    std::vector<std::string> factToString;
    void generatePredicateStrings();
	std::vector<int> generateFactVars(sat_capsule & capsule, int timestep, std::vector<std::string>);

    std::map<std::string,double> timings;
    std::clock_t _start;
public:
    PartiallyGroundedSAT(const Task& task);
	utils::ExitCode solve(const Task& task, int limit, bool optimal, bool incremental);
};


typedef size_t tSize;

#endif //SEARCH_LIFTEDRP_H
