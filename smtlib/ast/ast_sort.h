/**
 * \file ast_sort.h
 * \brief SMT-LIB sort.
 */

#ifndef INDUCTOR_AST_SORT_H
#define INDUCTOR_AST_SORT_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_identifier.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /** An SMT-LIB sort. */
        class Sort : public Node,
                     public std::enable_shared_from_this<Sort> {
        public:
            SimpleIdentifierPtr identifier;
            std::vector<SortPtr> arguments;

            /**
             * Constructor for a simple sort
             * \param identifier    Sort name
             */
            inline explicit Sort(const SimpleIdentifierPtr& identifier)
                    : identifier(identifier) {}

            /**
             * Constructor for a sort with arguments
             * \param identifier    Sort name
             * \param arguments     Sort arguments
             */
            Sort(const SimpleIdentifierPtr& identifier, const std::vector<SortPtr>& arguments);

            /** Checks whether the sort has arguments */
            bool hasArgs();

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_SORT_H
