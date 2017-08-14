#include "proof_strategy.h"

#include <algorithm>

using namespace std;
using namespace strat;

bool Strategy::isFinal(const std::string& state) {
    return final.end() != find(final.begin(), final.end(), state);
}

void Strategy::next(const StateList& states, RuleTransitionMap& nextStatesMap) {
    for (const auto& state : states) {
        if(isFinal(state))
            continue;

        for(const auto& pair : transitions[state]) {
            if(nextStatesMap.find(pair.first) == nextStatesMap.end()) {
                vector<string> nextStates;
                nextStatesMap[pair.first] = nextStates;
            }

            auto& nextStates = nextStatesMap[pair.first];

            if(nextStates.end() == find(nextStates.begin(), nextStates.end(), pair.second)) {
                nextStates.emplace_back(pair.second);
            }
        }
    }
}