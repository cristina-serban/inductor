/**
 * \file ast_datatype.h
 * \brief SMT-LIB datatype declarations and their components.
 */

#ifndef INDUCTOR_AST_DATATYPE_H
#define INDUCTOR_AST_DATATYPE_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_classes.h"
#include "ast_literal.h"
#include "ast_sort.h"

namespace smtlib {
    namespace ast {
        /* ================================= SortDeclaration ================================== */
        /** A sort declaration (used by the declare-datatypes command). */
        class SortDeclaration : public Node,
                                public std::enable_shared_from_this<SortDeclaration> {
        public:
            sptr_t<Symbol> symbol;
            sptr_t<NumeralLiteral> arity;

            /**
             * \param symbol    Datatype (sort) name
             * \param arity     Arity
             */
            inline SortDeclaration(sptr_t<Symbol> symbol, sptr_t<NumeralLiteral> arity)
                    : symbol(symbol), arity(arity) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== SelectorDeclaration ================================ */
        /** A selector declaration (used by constructor declarations). */
        class SelectorDeclaration : public Node,
                                    public std::enable_shared_from_this<SelectorDeclaration> {
        public:
            sptr_t<Symbol> symbol;
            sptr_t<Sort> sort;

            /**
             * \param symbol    Selector name
             * \param sort      Selector sort
             */
            inline SelectorDeclaration(sptr_t<Symbol> symbol,
                                       sptr_t<Sort> sort)
                    : symbol(symbol), sort(sort) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== ConstructorDeclaration ============================== */
        /** A sort declaration (used by the declare-datatypes command). */
        class ConstructorDeclaration : public Node,
                                       public std::enable_shared_from_this<ConstructorDeclaration> {
        public:
            sptr_t<Symbol> symbol;
            sptr_v<SelectorDeclaration> selectors;

            /**
             * \param symbol        Constructor name
             * \param selectors     Selectors for the constructor
             */
            ConstructorDeclaration(sptr_t<Symbol> symbol,
                                   sptr_v<SelectorDeclaration>& selectors);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DatatypeDeclaration =============================== */
        /** A datatype declaration (used by the declare-datatype and declare-datatypes commands). */
        class DatatypeDeclaration : public Node { };

        /* ============================= SimpleDatatypeDeclaration ============================ */
        /** A simple (non-parametric) datatype declaration. */
        class SimpleDatatypeDeclaration : public DatatypeDeclaration,
                                          public std::enable_shared_from_this<SimpleDatatypeDeclaration>  {
        public:
            sptr_v<ConstructorDeclaration> constructors;

            /**
             * \param constructors  Constructors for this datatype
             */
            SimpleDatatypeDeclaration(sptr_v<ConstructorDeclaration>& constructors);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =========================== ParametricDatatypeDeclaration ========================== */
        /** A parametric datatype declaration. */
        class ParametricDatatypeDeclaration : public DatatypeDeclaration,
                                              public std::enable_shared_from_this<ParametricDatatypeDeclaration> {
        public:
            sptr_v<Symbol> params;
            sptr_v<ConstructorDeclaration> constructors;

            /**
             * \param params        Parameters for the declaration
             * \param constructors  Constructors for this datatype
             */
            ParametricDatatypeDeclaration(sptr_v<Symbol>& params,
                                          sptr_v<ConstructorDeclaration>& constructors);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_DATATYPE_H
