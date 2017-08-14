/**
 * \file ast_theory.h
 * \brief SMT-LIB theory.
 */

#ifndef INDUCTOR_AST_THEORY_H
#define INDUCTOR_AST_THEORY_H

#include "ast_abstract.h"
#include "ast_attribute.h"

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
            SymbolPtr name;
            std::vector<AttributePtr> attributes;

            /**
             * Constructs theory without attributes.
             * \param name  Theory name
             */
            inline explicit Theory(const SymbolPtr& name) : name(name) {}

            /**
             * Constructs theory with attributes.
             * \param name          Theory name
             * \param attributes    Theory attributes
             */
            Theory(const SymbolPtr& name, const std::vector<AttributePtr>& attributes);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_THEORY_H
