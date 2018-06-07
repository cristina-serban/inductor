/**
 * \file ast_automaton.h
 * \brief Proof strategy automaton.
 */

#ifndef PROOFSTRAT_AST_AUTOMATON_H
#define PROOFSTRAT_AST_AUTOMATON_H

#include "ast_transition.h"

#include <vector>

namespace strat {
    namespace ast {
        /**
         * A proof strategy automaton.
         * Node of the proof strategy abstract syntax tree.
         */
        class Automaton : public virtual Node,
                          public std::enable_shared_from_this<Automaton> {
        public:
            /** Strategy name */
            StringLiteralPtr name;

            /** States of the automaton */
            std::vector<StatePtr> states;

            /** Inital state */
            StatePtr initial;

            /** Final states */
            std::vector<StatePtr> final;

            /** Transitions */
            std::vector<TransitionPtr> transitions;

            Automaton(StringLiteralPtr name,
                      std::vector<StatePtr> states,
                      StatePtr initial,
                      std::vector<StatePtr> final,
                      std::vector<TransitionPtr> transitions);

            std::string toString() override;
        };

        typedef std::shared_ptr<Automaton> AutomatonPtr;
    }
}

#endif //PROOFSTRAT_AST_AUTOMATON_H
