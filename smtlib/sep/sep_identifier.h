/**
 * \file sep_identif.h
 * \brief SMT-LIB+SEPLOG identifiers.
 */

#ifndef INDUCTOR_SEP_IDENTIFIER_H
#define INDUCTOR_SEP_IDENTIFIER_H

#include "sep_abstract.h"
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
            std::vector<IndexPtr> indices;

            /**
             * Constuctor for unindexed identifier.
             * \param symbol    Identifier symbol
             */
            inline explicit SimpleIdentifier(const std::string& name) : name(name) {}

            /**
             * Constuctor for indexed identifier.
             * \param symbol    Identifier symbol
             * \param indices   Identifier indices
             */
            SimpleIdentifier(const std::string& name, const std::vector<IndexPtr>& indices);

            inline bool isIndexed() { return !indices.empty(); }

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== QualifiedIdentifier ================================ */
        /** Qualified identifier (e.g. "(as f Sigma)"). */
        class QualifiedIdentifier : public Identifier,
                                    public std::enable_shared_from_this<QualifiedIdentifier> {
        public:
            SimpleIdentifierPtr identifier;
            SortPtr sort;

            /**
             * \param identifier    SimpleIdentifier
             * \param sort          Result sort
             */
            inline QualifiedIdentifier(const SimpleIdentifierPtr& identifier, const SortPtr& sort)
                    : identifier(identifier), sort(sort) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_IDENTIFIER_H