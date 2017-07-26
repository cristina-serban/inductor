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
            sptr_t<Rule> rule;

            /** Start state */
            sptr_t<State> start;

            /** End state */
            sptr_t<State> end;

            inline Transition(sptr_t<State> start,
                              sptr_t<Rule> rule,
                              sptr_t<State> end)
                : start(start), rule(rule), end(end) { }

            std::string toString();
        };
    }
}

#endif //PROOFSTRAT_AST_TRANSITION_H
