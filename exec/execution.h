/**
 * \file execution.h
 * \brief Execution handling.
 */

#ifndef INDUCTOR_EXECUTION_H
#define INDUCTOR_EXECUTION_H

#include "execution_settings.h"

#include "parser/smtlib_parser.h"
#include "util/global_typedef.h"

#include <memory>

namespace inductor {
    /** Class handling the execution of the project */
    class Execution {
    private:
        ExecutionSettingsPtr settings;
        smtlib::ast::NodePtr ast;

        bool parseAttempted{false}, parseSuccessful{false};
        bool syntaxCheckAttempted{false}, syntaxCheckSuccessful{false};
        bool sortednessCheckAttempted{false}, sortednessCheckSuccessful{false};
        bool heapCheckAttempted{false}, heapCheckSuccessful{false};

    public:
        /** Execution instance with default settings */
        Execution();

        /** Execution instance with specific settings */
        explicit Execution(const ExecutionSettingsPtr& settings);

        /** Parse an input file */
        bool parse();

        /** Check the syntax of an input file */
        bool checkSyntax();

        /** Check the sortedness of an input file */
        bool checkSortedness();

        /** Check heap correctness */
        bool checkHeap();

        /** Check entailment(s) specified in an input file */
        bool checkEntailment();

        /** Unfold the inductive predicates defined in an input file */
        bool unfoldPredicates();

        /** Run the input file in CVC4 */
        bool run();
    };

    typedef std::shared_ptr<Execution> ExecutionPtr;
}

#endif //INDUCTOR_EXECUTION_H
