/**
 * \file ast_theory.h
 * \brief SMT-LIB theory.
 */

#ifndef INDUCTOR_AST_THEORY_H
#define INDUCTOR_AST_THEORY_H

#include "ast_abstract.h"
#include "ast_attribute.h"
#include "ast_classes.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {

        /**
         * SMT-LIB theory.
         * Represents the contents of a theory file.
         */
        class Theory : public Root,
                       public std::enable_shared_from_this<Theory> {
        public:
            sptr_t<Symbol> name;
            sptr_v<Attribute> attributes;

            /**
             * Constructs theory without attributes.
             * \param name  Theory name
             */
            inline Theory(sptr_t<Symbol> name) : name(name) { }

            /**
             * Constructs theory with attributes.
             * \param name          Theory name
             * \param attributes    Theory attributes
             */
            Theory(sptr_t<Symbol> name,
                   sptr_v<Attribute>& attributes);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_THEORY_H