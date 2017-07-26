/**
 * \file ast_logic
 * \brief SMT-LIB logic.
 */

#ifndef INDUCTOR_AST_LOGIC_H
#define INDUCTOR_AST_LOGIC_H

#include "ast_abstract.h"
#include "ast_attribute.h"
#include "ast_classes.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /** Represents the contents of a logic file. */
        class Logic : public Root,
                      public std::enable_shared_from_this<Logic> {
        public:
            sptr_t<Symbol> name;
            sptr_v<Attribute> attributes;
        
            /**
             * Constructs logic without attributes.
             * \param name          Logic name
             */
            inline Logic(sptr_t<Symbol> name) : name(name) { }

            /**
             * Constructs logic with attributes.
             * \param name          Logic name
             * \param attributes    Logic attributes
             */
            Logic(sptr_t<Symbol> name,
                  sptr_v<Attribute> &attributes);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_LOGIC_H