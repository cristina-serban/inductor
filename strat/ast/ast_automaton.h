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
            sptr_t<StringLiteral> name;

            /** States of the automaton */
            std::vector<sptr_t<State>> states;

            /** Inital state */
            sptr_t<State> init;

            /** Final states */
            std::vector<sptr_t<State>> final;

            /** Transitions */
            std::vector<sptr_t<Transition>> transitions;

            Automaton(sptr_t<StringLiteral> name,
                      std::vector<sptr_t<State>> &states,
                      sptr_t<State> init,
                      std::vector<sptr_t<State>> &final,
                      std::vector<sptr_t<Transition>> &transitions);

            std::string toString();
        };
    }
}

#endif //PROOFSTRAT_AST_AUTOMATON_H
