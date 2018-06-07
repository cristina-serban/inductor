/**
 * \file ast_transition.h
 * \brief Proof strategy transition.
 */

#ifndef PROOFSTRAT_AST_TRANSITION_H
#define PROOFSTRAT_AST_TRANSITION_H

#include "ast_basic.h"

#include <vector>

namespace strat {
    namespace ast {
        /**
         * A proof strategy transition.
         * Node of the proof strategy abstract syntax tree.
         */
        class Transition : public virtual Node,
                           public std::enable_shared_from_this<Transition> {
        public:
            /** Transition rule */
            RulePtr rule;

            /** Start state */
            StatePtr start;

            /** End state */
            StatePtr end;

            inline Transition(StatePtr start,
                              RulePtr rule,
                              StatePtr end)
                    : start(std::move(start))
                    , rule(std::move(rule))
                    , end(std::move(end)) {}

            std::string toString() override;
        };

        typedef std::shared_ptr<Transition> TransitionPtr;
    }
}

#endif //PROOFSTRAT_AST_TRANSITION_H
