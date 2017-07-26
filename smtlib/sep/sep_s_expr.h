/**
 * \file sep_s_expression.h
 * \brief Compound S-expression.
 */

#ifndef INDUCTOR_SEP_S_EXPR_H
#define INDUCTOR_SEP_S_EXPR_H

#include "sep_interfaces.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /** Compound S-expression. */
        class CompSExpression : public SExpression,
                                public AttributeValue,
                                public std::enable_shared_from_this<CompSExpression> {
        public:
            sptr_v<SExpression> exprs;

            /**
             * \param exprs     Subexpressions
             */
            inline CompSExpression(sptr_v<SExpression>& exprs) {
                this->exprs.insert(this->exprs.end(), exprs.begin(), exprs.end());
            }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_S_EXPR_H