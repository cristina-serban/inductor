/**
 * \file sep_theory.h
 * \brief SMT-LIB+SEPLOG theory.
 */

#ifndef INDUCTOR_SEP_THEORY_H
#define INDUCTOR_SEP_THEORY_H

#include "sep_abstract.h"
#include "sep_attribute.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /**
         * SMT-LIB+SEPLOG theory.
         * Represents the contents of a theory file.
         */
        class Theory : public Root,
                       public std::enable_shared_from_this<Theory> {
        public:
            std::string name;
            sptr_v<Attribute> attributes;

            /**
             * Constructs theory without attributes.
             * \param name  Theory name
             */
            inline Theory(std::string name) : name(name) { }

            /**
             * Constructs theory with attributes.
             * \param name          Theory name
             * \param attributes    Theory attributes
             */
            Theory(std::string name,
                   sptr_v<Attribute>& attributes);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_THEORY_H