/**
 * \file ast_identif.h
 * \brief SMT-LIB identifiers.
 */

#ifndef INDUCTOR_AST_IDENTIFIER_H
#define INDUCTOR_AST_IDENTIFIER_H

#include "ast_basic.h"
#include "ast_classes.h"
#include "ast_interfaces.h"
#include "ast_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        class Sort;

        /* ==================================== SimpleIdentifier ==================================== */
        /** Simple identifier (e.g. "Real", "|John Brown|", "_ BitVec 32"). */
        class SimpleIdentifier : public Identifier,
                                 public std::enable_shared_from_this<SimpleIdentifier> {
        public:
            sptr_t<Symbol> symbol;
            sptr_v<Index> indices;

            /**
             * Constuctor for unindexed identifier.
             * \param symbol    Identifier symbol
             */
            SimpleIdentifier(sptr_t<Symbol> symbol) : symbol(symbol) { }

            /**
             * Constuctor for indexed identifier.
             * \param symbol    Identifier symbol
             * \param indices   Identifier indices
             */
            SimpleIdentifier(sptr_t<Symbol> symbol,
                             sptr_v<Index>& indices);

            /**
             * Checks whether the identifier is indexed (i.e. the list of indices is not empty).
             */
            bool isIndexed();

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== QualifiedIdentifier ================================ */
        /** Qualified identifier (e.g. "(as f Sigma)"). */
        class QualifiedIdentifier : public Identifier,
                                    public std::enable_shared_from_this<QualifiedIdentifier> {
        public:
            sptr_t<SimpleIdentifier> identifier;
            sptr_t<Sort> sort;

            /**
             * \param identifier    SimpleIdentifier
             * \param sort          Result sort
             */
            inline QualifiedIdentifier(sptr_t<SimpleIdentifier> identifier,
                                       sptr_t<Sort> sort)
                    : identifier(identifier), sort(sort) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_IDENTIFIER_H