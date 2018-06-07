/**
 * \file ast_attribute.h
 * \brief SMT-LIB attributes.
 */

#ifndef INDUCTOR_AST_ATTR_H
#define INDUCTOR_AST_ATTR_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"

#include "visitor/ast_visitor.h"

#include <vector>

namespace smtlib {
    namespace ast {
        /* ==================================== Attribute ===================================== */
        /** An SMT-LIB attribute */
        class Attribute : public Node,
                          public std::enable_shared_from_this<Attribute> {
        public:
            KeywordPtr keyword;
            AttributeValuePtr value;

            inline Attribute() = default;

            inline explicit Attribute(KeywordPtr keyword)
                    : keyword(std::move(keyword)) {}

            inline Attribute(KeywordPtr keyword, AttributeValuePtr value)
                    : keyword(std::move(keyword))
                    , value(std::move(value)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ CompAttributeValue ================================ */
        /** A compound value for an SMT-LIB attribute */
        class CompAttributeValue : public AttributeValue,
                                   public std::enable_shared_from_this<CompAttributeValue> {
        public:
            std::vector<AttributeValuePtr> values;

            explicit inline CompAttributeValue(std::vector<AttributeValuePtr> values)
                : values(std::move(values)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_ATTR_H
