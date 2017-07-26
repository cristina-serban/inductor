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

typedef std::map<std::string, std::vector<std::pair<proof::Rule, std::string>>> StratTransitionMap;

namespace strat {
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
        StratTransitionMap transitions;

        inline Strategy() { }

        inline Strategy(std::vector<std::string> states,
                        std::string init,
                        std::vector<std::string> final,
                        StratTransitionMap transitions) :
            states(states), init(init), final(final), transitions(transitions) { }
    };
}

#endif //PROOFSTRAT_STRATEGY_H
