/**
 * \file ast_sort.h
 * \brief SMT-LIB sort.
 */

#ifndef INDUCTOR_AST_SORT_H
#define INDUCTOR_AST_SORT_H

#include "ast_basic.h"
#include "ast_classes.h"
#include "ast_identifier.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        class SimpleIdentifier;
        /** An SMT-LIB sort. */
        class Sort : public Node,
                     public std::enable_shared_from_this<Sort> {
        public:
            sptr_t<SimpleIdentifier> identifier;
            sptr_v<Sort> args;

            /**
             * Constructor for a simple sort
             * \param identifier    Sort name
             */
            inline Sort(sptr_t<SimpleIdentifier> identifier) : identifier(identifier) { }

            /**
             * Constructor for a sort with arguments
             * \param identifier    Sort name
             * \param args          Sort arguments
             */
            Sort(sptr_t<SimpleIdentifier> identifier, sptr_v<Sort>& args);

            /** Checks whether the sort has arguments */
            bool hasArgs();

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_SORT_H