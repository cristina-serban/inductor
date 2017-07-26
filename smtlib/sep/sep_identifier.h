/**
 * \file sep_identif.h
 * \brief SMT-LIB+SEPLOG identifiers.
 */

#ifndef INDUCTOR_SEP_IDENTIFIER_H
#define INDUCTOR_SEP_IDENTIFIER_H

#include "sep_basic.h"
#include "sep_interfaces.h"
#include "sep_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        class Sort;

        /* ==================================== SimpleIdentifier ==================================== */
        /** Simple identifier (e.g. "Real", "|John Brown|", "_ BitVec 32"). */
        class SimpleIdentifier : public Identifier,
                                 public std::enable_shared_from_this<SimpleIdentifier> {
        public:
            std::string name;
            sptr_v<Index> indices;

            /**
             * Constuctor for unindexed identifier.
             * \param symbol    Identifier symbol
             */
            inline SimpleIdentifier(std::string name) : name(name) { }

            /**
             * Constuctor for indexed identifier.
             * \param symbol    Identifier symbol
             * \param indices   Identifier indices
             */
            SimpleIdentifier(std::string name, sptr_v<Index> &indices);

            inline bool isIndexed() { return !indices.empty(); }

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
            inline QualifiedIdentifier(sptr_t<SimpleIdentifier> identifier, sptr_t<Sort> sort)
                    : identifier(identifier), sort(sort) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_IDENTIFIER_H