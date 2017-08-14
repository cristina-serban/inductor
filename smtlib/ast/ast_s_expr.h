/**
 * \file ast_s_expression.h
 * \brief Compound S-expression.
 */

#ifndef INDUCTOR_AST_S_EXPR_H
#define INDUCTOR_AST_S_EXPR_H

#include "ast_abstract.h"
#include "ast_interfaces.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /** Compound S-expression. */
        class CompSExpression : public SExpression,
                                public AttributeValue,
                                public std::enable_shared_from_this<CompSExpression> {
        public:
            std::vector<SExpressionPtr> expressions;

            /**
             * \param expressions     Subexpressions
             */
            explicit CompSExpression(const std::vector<SExpressionPtr>& expressions);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_S_EXPR_H
