/**
 * \file ast_datatype.h
 * \brief SMT-LIB datatype declarations and their components.
 */

#ifndef INDUCTOR_AST_DATATYPE_H
#define INDUCTOR_AST_DATATYPE_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_literal.h"
#include "ast_sort.h"

namespace smtlib {
    namespace ast {
        /* ================================= SortDeclaration ================================== */
        /** A sort declaration (used by the declare-datatypes command). */
        class SortDeclaration : public Node,
                                public std::enable_shared_from_this<SortDeclaration> {
        public:
            SymbolPtr symbol;
            NumeralLiteralPtr arity;

            /**
             * \param symbol    Datatype (sort) name
             * \param arity     Arity
             */
            inline SortDeclaration(const SymbolPtr& symbol, const NumeralLiteralPtr& arity)
                    : symbol(symbol), arity(arity) { }

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== SelectorDeclaration ================================ */
        /** A selector declaration (used by constructor declarations). */
        class SelectorDeclaration : public Node,
                                    public std::enable_shared_from_this<SelectorDeclaration> {
        public:
            SymbolPtr symbol;
            SortPtr sort;

            /**
             * \param symbol    Selector name
             * \param sort      Selector sort
             */
            inline SelectorDeclaration(const SymbolPtr& symbol, const SortPtr& sort)
                    : symbol(symbol), sort(sort) { }

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== ConstructorDeclaration ============================== */
        /** A sort declaration (used by the declare-datatypes command). */
        class ConstructorDeclaration : public Node,
                                       public std::enable_shared_from_this<ConstructorDeclaration> {
        public:
            SymbolPtr symbol;
            std::vector<SelectorDeclarationPtr> selectors;

            /**
             * \param symbol        Constructor name
             * \param selectors     Selectors for the constructor
             */
            ConstructorDeclaration(const SymbolPtr& symbol,
                                   const std::vector<SelectorDeclarationPtr>& selectors);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ DatatypeDeclaration =============================== */
        /** A datatype declaration (used by the declare-datatype and declare-datatypes commands). */
        class DatatypeDeclaration : public Node { };

        /* ============================= SimpleDatatypeDeclaration ============================ */
        /** A simple (non-parametric) datatype declaration. */
        class SimpleDatatypeDeclaration : public DatatypeDeclaration,
                                          public std::enable_shared_from_this<SimpleDatatypeDeclaration>  {
        public:
            std::vector<ConstructorDeclarationPtr> constructors;

            /**
             * \param constructors  Constructors for this datatype
             */
            explicit SimpleDatatypeDeclaration(const std::vector<ConstructorDeclarationPtr>& constructors);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =========================== ParametricDatatypeDeclaration ========================== */
        /** A parametric datatype declaration. */
        class ParametricDatatypeDeclaration : public DatatypeDeclaration,
                                              public std::enable_shared_from_this<ParametricDatatypeDeclaration> {
        public:
            std::vector<SymbolPtr> parameters;
            std::vector<ConstructorDeclarationPtr> constructors;

            /**
             * \param params        Parameters for the declaration
             * \param constructors  Constructors for this datatype
             */
            ParametricDatatypeDeclaration(const std::vector<SymbolPtr> parameters,
                                          const std::vector<ConstructorDeclarationPtr> constructors);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_DATATYPE_H
