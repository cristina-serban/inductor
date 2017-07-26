/**
 * \file sep_script
 * \brief SMT-LIB+SEPLOG script.
 */

#ifndef INDUCTOR_SEP_SCRIPT_H
#define INDUCTOR_SEP_SCRIPT_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_command.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /**
         * SMT-LIB+SEPLOG script.
         * Represents the contents of a query file.
         */
        class Script : public Root,
                       public std::enable_shared_from_this<Script> {
        public:
            sptr_v<Command> commands;

            /**
             * Default constructor
             */
            inline Script() { }

            /**
             * \param cmds    Command list
             */
            Script(sptr_v<Command>& commands);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_SCRIPT_H