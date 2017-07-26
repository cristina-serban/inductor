/**
 * \file ast_script
 * \brief SMT-LIB script.
 */

#ifndef INDUCTOR_AST_SCRIPT_H
#define INDUCTOR_AST_SCRIPT_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_classes.h"
#include "ast_command.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /**
         * SMT-LIB script.
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

#endif //INDUCTOR_AST_SCRIPT_H