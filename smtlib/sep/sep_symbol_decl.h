/**
 * \file sep_symbol_decl.h
 * \brief Sort and function symbol declarations.
 */

#ifndef INDUCTOR_SEP_SYMBOL_DECL_H
#define INDUCTOR_SEP_SYMBOL_DECL_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_identifier.h"
#include "sep_interfaces.h"
#include "sep_literal.h"
#include "sep_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        class Attribute;

        /* =============================== SortSymbolDeclaration ============================== */
        /**
         * Declaration of a sort symbol.
         * Can act as an attribute value.
         */
        class SortSymbolDeclaration : public virtual Node,
                                      public AttributeValue,
                                      public std::enable_shared_from_this<SortSymbolDeclaration> {
        public:
            sptr_t<SimpleIdentifier> identifier;
            long arity;
            sptr_v<Attribute> attributes;

            /**
             * Constructs declaration without attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             */
            inline SortSymbolDeclaration(sptr_t<SimpleIdentifier> identifier, long arity)
                : identifier(identifier), arity(arity) { }

            /**
             * Constructs declaration with attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             * \param attributes    Sort symbol declaration attributes
             */
            SortSymbolDeclaration(sptr_t<SimpleIdentifier> identifier,
                                  long arity,
                                  sptr_v<Attribute> &attributes);

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
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
            sptr_t<SpecConstant> constant;
            sptr_t<Sort> sort;
            sptr_v<Attribute> attributes;

            /**
            * Constructs declaration without attributes.
            * \param constant      Specification constant
            * \param sort          Function sort
            */
            inline SpecConstFunDeclaration(sptr_t<SpecConstant> constant,
                                           sptr_t<Sort> sort)
                : constant(constant), sort(sort) { }

            /**
             * Constructs declaration with attributes.
             * \param constant      Specification constant
             * \param sort          Function sort
             * \param attributes    Function symbol declaration attributes
             */
            SpecConstFunDeclaration(sptr_t<SpecConstant> constant,
                                    sptr_t<Sort> sort,
                                    sptr_v<Attribute> &attributes);

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ========================== MetaSpecConstFunDeclaration =========================== */
        /**
         * Meta specification constant function symbol declaration.
         * Can act as an attribute value.
         */
        class MetaSpecConstFunDeclaration : public FunSymbolDeclaration,
                                            public std::enable_shared_from_this<MetaSpecConstFunDeclaration> {
        public:
            sptr_t<MetaSpecConstant> constant;
            sptr_t<Sort> sort;
            sptr_v<Attribute> attributes;

            /**
            * Constructs declaration without attributes.
            * \param constant      Meta specification constant
            * \param sort          Function sort
            */
            inline MetaSpecConstFunDeclaration(sptr_t<MetaSpecConstant> constant,
                                               sptr_t<Sort> sort)
                : constant(constant), sort(sort) { }

            /**
             * Constructs declaration with attributes.
             * \param constant      Meta specification constant
             * \param sort          Function sort
             * \param attributes    Function symbol declaration attributes
             */
            MetaSpecConstFunDeclaration(sptr_t<MetaSpecConstant> constant,
                                               sptr_t<Sort> sort,
                                               sptr_v<Attribute> &attributes);

            inline sptr_t<MetaSpecConstant> getConstant() { return constant; }

            inline void setConstant(sptr_t<MetaSpecConstant> constant) {
                this->constant = constant;
            }

            inline void setSort(sptr_t<Sort> sort) { this->sort = sort; }

            inline sptr_v<Attribute> &getAttributes() {
                return attributes;
            }

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ============================== SimpleFunDeclaration =============================== */
        /**
         * Identifier function symbol declaration.
         * Can act as an attribute value.
         */
        class SimpleFunDeclaration : public FunSymbolDeclaration,
                                     public std::enable_shared_from_this<SimpleFunDeclaration> {
        public:
            sptr_t<SimpleIdentifier> identifier;
            sptr_v<Sort> signature;
            sptr_v<Attribute> attributes;

        protected:
            SimpleFunDeclaration() { }

        public:
            /**
             * Constructs declaration without attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            SimpleFunDeclaration(sptr_t<SimpleIdentifier> identifier,
                                 sptr_v<Sort> &signature);

            /**
             * Constructs declaration with attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            SimpleFunDeclaration(sptr_t<SimpleIdentifier> identifier,
                                 sptr_v<Sort> &signature,
                                 sptr_v<Attribute> &attributes);

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* =============================== ParametricFunDeclaration ================================ */
        /**
        * Parametric function symbol declaration.
        * Can act as an attribute value.
        */
        class ParametricFunDeclaration : public FunSymbolDeclaration,
                                         public std::enable_shared_from_this<ParametricFunDeclaration> {
        public:
            std::vector<std::string> params;
            sptr_t<SimpleIdentifier> identifier;
            sptr_v<Sort> signature;
            sptr_v<Attribute> attributes;

            /**
             * Constructs declaration without attributes.
             * \param params        Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            ParametricFunDeclaration(std::vector<std::string> &params,
                                     sptr_t<SimpleIdentifier> identifier,
                                     sptr_v<Sort> &signature);

            /**
             * Constructs declaration with attributes.
             * \param params        Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            ParametricFunDeclaration(std::vector<std::string> &params,
                                     sptr_t<SimpleIdentifier> identifier,
                                     sptr_v<Sort> &signature,
                                     sptr_v<Attribute> &attributes);

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_SYMBOL_DECL_H