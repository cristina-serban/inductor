/**
 * \file ast_basic.h
 * \brief Basic proof strategy data structures.
 */

#ifndef PROOFSTRAT_AST_BASIC_H
#define PROOFSTRAT_AST_BASIC_H

#include "ast_abstract.h"

#include <memory>

namespace strat {
    namespace ast {
        /**
         * A string literal.
         * Node of the proof strategy abstract syntax tree.
         */
        class StringLiteral : public virtual Node,
                              public std::enable_shared_from_this<StringLiteral> {
        public:
            std::string value;

            inline StringLiteral(std::string value) : value(value) { }

            std::string toString() override;
        };

        /**
         * A proof rule.
         * Node of the proof strategy abstract syntax tree.
         */
        class Rule : public virtual Node,
                     public std::enable_shared_from_this<Rule> {
        public:
            sptr_t<StringLiteral> name;

            inline Rule(sptr_t<StringLiteral> name) : name(name) { }

            virtual std::string toString();
        };

        /**
         * A state in the strategy automaton.
         * Node of the proof strategy abstract syntax tree.
         */
        class State : public virtual Node,
                      public std::enable_shared_from_this<State> {
        public:
            sptr_t<StringLiteral> name;

            inline State(sptr_t<StringLiteral> name) : name(name) { }

            virtual std::string toString();
        };
    }
}

#endif //PROOFSTRAT_AST_BASIC_H
