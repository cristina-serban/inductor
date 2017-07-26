/**
 * \file ast_basic.h
 * \brief Basic SMT-LIB+SEPLOG concepts.
 */

#ifndef INDUCTOR_SEP_BASIC_H
#define INDUCTOR_SEP_BASIC_H

#include "sep_abstract.h"
#include "sep_interfaces.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace sep {
        /* ====================================== Symbol ====================================== */
        /**
         * An SMT-LIB+SEPLOG symbol (e.g. "plus", "+", "|quoted symbol|").
         * Can act as an S-expression, an index, an attribute value or a constructor.
         */
        class Symbol : public virtual Node,
                       public SExpression,
                       public Index,
                       public AttributeValue,
                       public Constructor,
                       public std::enable_shared_from_this<Symbol> {
        public:
            std::string value;

            /**
             * \param value     Textual value of the symbol
             */
            inline Symbol(std::string value) : value(value) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ====================================== Keyword ===================================== */
        /**
         * An SMT-LIB+SEPLOG keyword (e.g. ":date", ":<=").
         * Can act as an S-expression.
         */
        class Keyword : public virtual Node,
                        public SExpression,
                        public std::enable_shared_from_this<Keyword> {
        public:
            std::string value;

            /**
             * \param value     Textual value of the keyword
             */
            inline Keyword(std::string value) : value(value) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= MetaSpecConstant ================================= */
        /**
         * An SMT-LIB+SEPLOG meta specification constant ("NUMERAL", "DECIMAL" or "STRING").
         */
        class MetaSpecConstant : public Node,
                                 public std::enable_shared_from_this<MetaSpecConstant> {
        public:
            enum Type {
                NUMERAL = 0,
                DECIMAL,
                STRING
            };

            MetaSpecConstant::Type type;

            /**
             * \param type  Meta specification constant type
             */
            inline MetaSpecConstant(MetaSpecConstant::Type type) : type(type) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== BooleanValue =================================== */
        /**
         * A boolean value ('true' or 'false').
         * Can act as an attribute value.
         */
        class BooleanValue : public virtual Node,
                             public AttributeValue,
                             public std::enable_shared_from_this<BooleanValue> {
        public:
            bool value;

            /**
             * \param value Truth value ("true" or "false")
             */
            inline BooleanValue(bool value) : value(value) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== PropLiteral ==================================== */
        /** Propositional literal (used for check-sat-assuming commands). */
        class PropLiteral : public Node,
                            public std::enable_shared_from_this<PropLiteral> {
        public:
            std::string value;
            bool negated;

            /**
             * \param symbol    Symbol of the literal
             * \param negated   Whether the symbol is negated
             */
            inline PropLiteral(std::string value, bool negated)
                    : value(value), negated(negated) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_BASIC_H