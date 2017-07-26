/**
 * \file ast_attribute.h
 * \brief SMT-LIB+SEPLOG attributes.
 */

#ifndef INDUCTOR_SEP_ATTR_H
#define INDUCTOR_SEP_ATTR_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_interfaces.h"
#include "sep_literal.h"
#include "sep_symbol_decl.h"

#include "util/global_values.h"

#include <vector>

namespace smtlib {
    namespace sep {
        /* ==================================== Attribute ===================================== */
        /** An SMT-LIB+SEPLOG attribute */
        struct Attribute : public Node {
            std::string keyword;

            inline Attribute() { }

            inline Attribute(std::string keyword) : keyword(keyword) { }

            virtual void accept(Visitor0 *visitor) = 0;

            virtual std::string toString() = 0;
        };

        /* ================================= SimpleAttribute ================================== */
        /** An attribute without value */
        class SimpleAttribute : public Attribute,
                                public std::enable_shared_from_this<SimpleAttribute> {
        public:
            inline SimpleAttribute() { }

            inline SimpleAttribute(std::string keyword) {
                this->keyword = keyword;
            }

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* =============================== SExpressionAttribute =============================== */
        /** An attribute with a sep::SExpression value */
        class SExpressionAttribute : public Attribute,
                                     public std::enable_shared_from_this<SExpressionAttribute> {
        public:
            sptr_t<SExpression> value;

            inline SExpressionAttribute() { }

            inline SExpressionAttribute(std::string keyword,
                                        sptr_t<SExpression> value) : value(value) {
                this->keyword = keyword;
            }

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ================================= SymbolAttribute ================================== */
        /** An attribute with a sep::Symbol value */
        class SymbolAttribute : public Attribute,
                                public std::enable_shared_from_this<SymbolAttribute> {
        public:
            std::string value;

            inline SymbolAttribute() { }

            inline SymbolAttribute(std::string keyword, std::string value) : value(value) {
                this->keyword = keyword;
            }

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ================================= BooleanAttribute ================================= */
        /** An attribute with a boolean value */
        class BooleanAttribute : public Attribute,
                                 public std::enable_shared_from_this<BooleanAttribute> {
        public:
            bool value;

            inline BooleanAttribute() { }

            inline BooleanAttribute(std::string symbol, bool value) : value(value) {
                this->keyword = keyword;
            }

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ================================= NumeralAttribute ================================= */
        /** An attribute with a sep::NumeralLiteral value */
        class NumeralAttribute : public Attribute,
                                 public std::enable_shared_from_this<NumeralAttribute> {
        public:
            sptr_t<NumeralLiteral> value;

            inline NumeralAttribute() { }

            inline NumeralAttribute(std::string symbol,
                                    sptr_t<NumeralLiteral> value) : value(value) {
                this->keyword = keyword;
            }

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ================================= DecimalAttribute ================================= */
        /** An attribute with a sep::DecimalLiteal value */
        class DecimalAttribute : public Attribute,
                                 public std::enable_shared_from_this<DecimalAttribute> {
        public:
            sptr_t<DecimalLiteral> value;

            inline DecimalAttribute() { }

            inline DecimalAttribute(std::string symbol,
                                    sptr_t<DecimalLiteral> value) : value(value) {
                this->keyword = keyword;
            }

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ================================= StringAttribute ================================== */
        /** An attribute with a sep::StringLiteral value */
        class StringAttribute : public Attribute,
                                public std::enable_shared_from_this<StringAttribute> {
        public:
            sptr_t<StringLiteral> value;

            inline StringAttribute() { }

            inline StringAttribute(std::string symbol,
                                   sptr_t<StringLiteral> value) : value(value) {
                this->keyword = keyword;
            }

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ================================ TheoriesAttribute ================================= */
        /** An attribute with a list of theory names value */
        class TheoriesAttribute : public Attribute,
                                  public std::enable_shared_from_this<TheoriesAttribute> {
        public:
            std::vector<std::string> theories;

            inline TheoriesAttribute() { this->keyword = KW_THEORIES; }

            TheoriesAttribute(std::vector<std::string> &theories);

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ================================== SortsAttribute ================================== */
        /** An attribute with a list of sep::SortSymbolDeclaration value */
        class SortsAttribute : public Attribute,
                               public std::enable_shared_from_this<SortsAttribute> {
        public:
            sptr_v<SortSymbolDeclaration> declarations;

            inline SortsAttribute() { this->keyword = KW_SORTS; }

            SortsAttribute(sptr_v<SortSymbolDeclaration> &decls);

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ================================== FunsAttribute =================================== */
        /** An attribute with a list of sep::FunSymbolDeclaration value */
        class FunsAttribute : public Attribute,
                              public std::enable_shared_from_this<FunsAttribute> {
        public:
            sptr_v<FunSymbolDeclaration> declarations;

            inline FunsAttribute() { this->keyword = KW_FUNS; }

            FunsAttribute(sptr_v<FunSymbolDeclaration> &decls);

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_ATTR_H