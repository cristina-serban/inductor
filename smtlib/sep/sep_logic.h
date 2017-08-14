/**
 * \file sep_logic
 * \brief SMT-LIB+SEPLOG logic.
 */

#ifndef INDUCTOR_SEP_LOGIC_H
#define INDUCTOR_SEP_LOGIC_H

#include "sep_abstract.h"
#include "sep_attribute.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /**
         * SMT-LIB+SEPLOG logic.
         * Represents the contents of a logic file.
         */
        class Logic : public Root,
                      public std::enable_shared_from_this<Logic> {
        public:
            std::string name;
            std::vector<AttributePtr> attributes;

            /**
             * Constructs logic without attributes.
             * \param name          Logic name
             */
            inline explicit Logic(const std::string& name) : name(name) {}

            /**
             * Constructs logic with attributes.
             * \param name          Logic name
             * \param attributes    Logic attributes
             */
            Logic(const std::string& name, const std::vector<AttributePtr>& attributes);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_SEP_LOGIC_H
