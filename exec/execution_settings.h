/**
 * \file execution_settings.h
 * \brief Settings for execution handling.
 */

#ifndef INDUCTOR_EXECUTION_SETTINGS_H
#define INDUCTOR_EXECUTION_SETTINGS_H

#include "ast/ast_abstract.h"
#include "stack/ast_symbol_stack.h"
#include "util/global_typedef.h"
#include "visitor/ast_sortedness_checker.h"
#include "visitor/sep_stack_loader.h"

#include <memory>

namespace inductor {
    class ExecutionSettings;
    typedef std::shared_ptr<ExecutionSettings> ExecutionSettingsPtr;

    /** Settings for execution handling. */
    class ExecutionSettings {
    public:
        enum InputMethod {
            INPUT_NONE = 0, INPUT_FILE, INPUT_AST
        };
    private:
        bool coreTheoryEnabled;
        bool unfoldExistential = true;
        bool cvcEmp = false;

        std::string filename;
        std::string unfoldOutputPath = "unfolding";

        smtlib::ast::NodePtr ast;
        smtlib::ast::ISortCheckContextPtr sortCheckContext;

        InputMethod inputMethod;
        int unfoldLevel = 0;
    public:
        /** Default constructor */
        ExecutionSettings();

        /** Copy constructor */
        explicit ExecutionSettings(const ExecutionSettingsPtr& settings);


        /** Whether the 'Core' theory is automatically loaded or not */
        inline bool isCoreTheoryEnabled() { return coreTheoryEnabled; }

        /** Set whether the 'Core' theory is automatically loaded or not */
        inline void setCoreTheoryEnabled(bool enabled) { coreTheoryEnabled = enabled; }


        /** Get the input method */
        inline InputMethod getInputMethod() { return inputMethod; }


        /** Get the input file */
        inline std::string getInputFile() { return filename; }

        /** Set a file as input */
        void setInputFromFile(std::string filename);


        /** Get the input AST */
        inline smtlib::ast::NodePtr getInputAst() { return ast; }

        /** Set an AST node as input */
        void setInputFromAst(smtlib::ast::NodePtr ast);


        /** Get the existing context for the sortedness check */
        inline smtlib::ast::ISortCheckContextPtr getSortCheckContext() {
            return sortCheckContext;
        }

        /** Set an existing context for the sortedness check */
        inline void setSortCheckContext(smtlib::ast::ISortCheckContextPtr ctx) {
            this->sortCheckContext = std::move(ctx);
        }


        /** Whether the unfold should be existential or not */
        inline bool isUnfoldExistential() { return unfoldExistential; }

        /** Set whether the unfold should be existential or not */
        inline void setUnfoldExistential(bool unfoldExistential) {
            this->unfoldExistential = unfoldExistential;
        };


        /** Get the depth level of unfolding */
        inline int getUnfoldLevel() { return unfoldLevel; }

        /** Set the depth level of unfolding */
        inline void setUnfoldLevel(int unfoldLevel) { this->unfoldLevel = unfoldLevel; }


        /** Get the output path for the unfolding results */
        inline std::string getUnfoldOutputPath() { return unfoldOutputPath; }

        /** Set the output path for the unfolding results */
        inline void setUnfoldOutputPath(std::string unfoldOutputPath) {
            this->unfoldOutputPath = std::move(unfoldOutputPath);
        }


        /** Whether the unfolding results should use a CVC4-style 'emp' predicate */
        inline bool isCvcEmp() { return cvcEmp; }

        /** Set whether the unfolding results should use a CVC4-style 'emp' predicate */
        inline void setCvcEmp(bool cvcEmp) { this->cvcEmp = cvcEmp; }
    };
}

#endif //INDUCTOR_EXECUTION_SETTINGS_H
