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

            inline explicit StringLiteral(std::string value)
                    : value(std::move(value)) {}

            std::string toString() override;
        };

        typedef std::shared_ptr<StringLiteral> StringLiteralPtr;

        /**
         * A proof rule.
         * Node of the proof strategy abstract syntax tree.
         */
        class Rule : public virtual Node,
                     public std::enable_shared_from_this<Rule> {
        public:
            StringLiteralPtr name;

            inline explicit Rule(StringLiteralPtr name)
                    : name(std::move(name)) {}

            std::string toString() override;
        };

        typedef std::shared_ptr<Rule> RulePtr;

        /**
         * A state in the strategy automaton.
         * Node of the proof strategy abstract syntax tree.
         */
        class State : public virtual Node,
                      public std::enable_shared_from_this<State> {
        public:
            StringLiteralPtr name;

            inline explicit State(StringLiteralPtr name)
                    : name(std::move(name)) {}

            std::string toString() override;
        };

        typedef std::shared_ptr<State> StatePtr;
    }
}

#endif //PROOFSTRAT_AST_BASIC_H
