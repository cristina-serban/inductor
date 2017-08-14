/**
 * \file ast_logic
 * \brief SMT-LIB logic.
 */

#ifndef INDUCTOR_AST_LOGIC_H
#define INDUCTOR_AST_LOGIC_H

#include "ast_abstract.h"
#include "ast_attribute.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /** Represents the contents of a logic file. */
        class Logic : public Root,
                      public std::enable_shared_from_this<Logic> {
        public:
            SymbolPtr name;
            std::vector<AttributePtr> attributes;
        
            /**
             * Constructs logic without attributes.
             * \param name          Logic name
             */
            inline explicit Logic(const SymbolPtr& name) : name(name) {}

            /**
             * Constructs logic with attributes.
             * \param name          Logic name
             * \param attributes    Logic attributes
             */
            Logic(const SymbolPtr& name, const std::vector<AttributePtr>& attributes);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_LOGIC_H
