/**
 * \file proof_strategy.h
 * \brief Proof strategy.
 */

#ifndef PROOFSTRAT_STRATEGY_H
#define PROOFSTRAT_STRATEGY_H

#include "proof/proof_rule.h"
#include "strat/ast/ast_file.h"

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
    private:
        proof::Rule toRule(const std::string& rulename);
    public:
        /** States of the strategy automaton */
        std::vector<std::string> states;

        /** Inital state */
        std::string init;

        /** Final states */
        std::vector<std::string> final;

        /** Transitions */
        TransitionMap transitions;

        inline Strategy() = default;

        inline Strategy(std::vector<std::string> states,
                        std::string init,
                        std::vector<std::string> final,
                        TransitionMap transitions)
                : states(std::move(states))
                , init(std::move(init))
                , final(std::move(final))
                , transitions(std::move(transitions)) {}

        void load(const std::string& filename);

        void load(const ast::FilePtr& file);

        bool isFinal(const std::string& state);

        void next(const StateList& states, RuleTransitionMap& nextStatesMap);
    };

    typedef std::shared_ptr<Strategy> StrategyPtr;
}

#endif //PROOFSTRAT_STRATEGY_H
