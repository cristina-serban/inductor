/**
 * \file proof_strategy.h
 * \brief Proof strategy.
 */

#ifndef PROOFSTRAT_STRATEGY_H
#define PROOFSTRAT_STRATEGY_H

#include "../proof/proof_rule.h"

#include <map>
#include <string>
#include <utility>
#include <vector>

namespace strat {
    typedef std::vector<std::pair<proof::Rule, std::string>> TransitionList;
    typedef std::map<std::string, TransitionList> TransitionMap;
    typedef std::vector<std::string> StateList;
    typedef std::unordered_map<proof::Rule, StateList, std::hash<int>> RuleTransitionMap;

    /** A proof strategy */
    class Strategy {
    public:
        /** States of the strategy automaton */
        std::vector<std::string> states;

        /** Inital state */
        std::string init;

        /** Final states */
        std::vector<std::string> final;

        /** Transitions */
        TransitionMap transitions;

        inline Strategy() { }

        inline Strategy(std::vector<std::string> states,
                        std::string init,
                        std::vector<std::string> final,
                        TransitionMap transitions) :
            states(states), init(init), final(final), transitions(transitions) { }

        bool isFinal(const std::string& state);

        void next(const StateList& states, RuleTransitionMap& nextStatesMap);
    };

    typedef std::shared_ptr<Strategy> StrategyPtr;
}

#endif //PROOFSTRAT_STRATEGY_H
