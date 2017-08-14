/**
 * \file ast_symbol_decl.h
 * \brief Sort and function symbol declarations.
 */

#ifndef INDUCTOR_AST_SYMBOL_DECL_H
#define INDUCTOR_AST_SYMBOL_DECL_H

#include "ast_abstract.h"
#include "ast_attribute.h"
#include "ast_basic.h"
#include "ast_identifier.h"
#include "ast_interfaces.h"
#include "ast_literal.h"
#include "ast_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /* =============================== SortSymbolDeclaration ============================== */
        /**
         * Declaration of a sort symbol.
         * Can act as an attribute value.
         */
        class SortSymbolDeclaration : public virtual Node,
                                      public AttributeValue,
                                      public std::enable_shared_from_this<SortSymbolDeclaration> {
        public:
            SimpleIdentifierPtr identifier;
            NumeralLiteralPtr arity;
            std::vector<AttributePtr> attributes;

            /**
             * Constructs declaration without attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             */
            inline SortSymbolDeclaration(const SimpleIdentifierPtr& identifier,
                                         const NumeralLiteralPtr& arity)
                    : identifier(identifier), arity(arity) {}

            /**
             * Constructs declaration with attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             * \param attributes    Sort symbol declaration attributes
             */
            SortSymbolDeclaration(const SimpleIdentifierPtr& identifier,
                                  const NumeralLiteralPtr& arity,
                                  const std::vector<AttributePtr>& attributes);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== FunSymbolDeclaration =============================== */
        /**
         * A function symbol declaration.
         * Can act as an attribute value.
         */
        class FunSymbolDeclaration : public virtual Node,
                                     public AttributeValue {
        };

        /* ============================= SpecConstFunDeclaration ============================== */
        /**
         * Specification constant function symbol declaration.
         * Can act as an attribute value.
         */
        class SpecConstFunDeclaration : public FunSymbolDeclaration,
                                        public std::enable_shared_from_this<SpecConstFunDeclaration> {
        public:
            SpecConstantPtr constant;
            SortPtr sort;
            std::vector<AttributePtr> attributes;

            /**
            * Constructs declaration without attributes.
            * \param constant      Specification constant
            * \param sort          Function sort
            */
            inline SpecConstFunDeclaration(const SpecConstantPtr& constant, const SortPtr& sort)
                    : constant(constant), sort(sort) {}

            /**
             * Constructs declaration with attributes.
             * \param constant      Specification constant
             * \param sort          Function sort
             * \param attributes    Function symbol declaration attributes
             */
            SpecConstFunDeclaration(const SpecConstantPtr& constant,
                                    const SortPtr& sort,
                                    const std::vector<AttributePtr>& attributes);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ========================== MetaSpecConstFunDeclaration =========================== */

        /**
         * Meta specification constant function symbol declaration.
         * Can act as an attribute value.
         */
        class MetaSpecConstFunDeclaration : public FunSymbolDeclaration,
                                            public std::enable_shared_from_this<MetaSpecConstFunDeclaration> {
        public:
            MetaSpecConstantPtr constant;
            SortPtr sort;
            std::vector<AttributePtr> attributes;

            /**
            * Constructs declaration without attributes.
            * \param constant      Meta specification constant
            * \param sort          Function sort
            */
            inline MetaSpecConstFunDeclaration(const MetaSpecConstantPtr& constant, const SortPtr& sort)
                    : constant(constant), sort(sort) {}

            /**
             * Constructs declaration with attributes.
             * \param constant      Meta specification constant
             * \param sort          Function sort
             * \param attributes    Function symbol declaration attributes
             */
            MetaSpecConstFunDeclaration(const MetaSpecConstantPtr constant,
                                        const SortPtr& sort,
                                        const std::vector<AttributePtr>& attributes);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ============================== SimpleFunDeclaration =============================== */

        /**
         * Identifier function symbol declaration.
         * Can act as an attribute value.
         */
        class SimpleFunDeclaration : public FunSymbolDeclaration,
                                     public std::enable_shared_from_this<SimpleFunDeclaration> {
        public:
            SimpleIdentifierPtr identifier;
            std::vector<SortPtr> signature;
            std::vector<AttributePtr> attributes;

        protected:
            SimpleFunDeclaration() = default;

        public:
            /**
             * Constructs declaration without attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            SimpleFunDeclaration(const SimpleIdentifierPtr& identifier,
                                 const std::vector<SortPtr>& signature);

            /**
             * Constructs declaration with attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            SimpleFunDeclaration(const SimpleIdentifierPtr& identifier,
                                 const std::vector<SortPtr>& signature,
                                 const std::vector<AttributePtr>& attributes);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== ParametricFunDeclaration ================================ */

        /**
        * Parametric function symbol declaration.
        * Can act as an attribute value.
        */
        class ParametricFunDeclaration : public FunSymbolDeclaration,
                                         public std::enable_shared_from_this<ParametricFunDeclaration> {
        public:
            std::vector<SymbolPtr> parameters;
            SimpleIdentifierPtr identifier;
            std::vector<SortPtr> signature;
            std::vector<AttributePtr> attributes;

            /**
             * Constructs declaration without attributes.
             * \param parameters    Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            ParametricFunDeclaration(const std::vector<SymbolPtr>& parameters,
                                     const SimpleIdentifierPtr& identifier,
                                     const std::vector<SortPtr>& signature);

            /**
             * Constructs declaration with attributes.
             * \param parameters    Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            ParametricFunDeclaration(const std::vector<SymbolPtr>& parameters,
                                     const SimpleIdentifierPtr& identifier,
                                     const std::vector<SortPtr>& signature,
                                     const std::vector<AttributePtr>& attributes);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_SYMBOL_DECL_H
