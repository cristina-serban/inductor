/**
 * \file ast_var_renamer.h
 * \brief Visitor that renames variables
 */

#ifndef INDUCTOR_AST_VAR_REPLACER_H
#define INDUCTOR_AST_VAR_REPLACER_H

#include "ast_visitor_extra.h"

#include "ast/ast_identifier.h"

#include <unordered_map>

namespace smtlib {
    namespace ast {
        typedef std::unordered_map<std::string, std::string> RenamingMap;

        /* ============================= IVariableRenamerContext ============================== */
        /** Context interface for variable renaming */
        class IVariableRenamerContext {
        public:
            virtual RenamingMap& getRenamingMap() = 0;
        };

        typedef std::shared_ptr<IVariableRenamerContext> IVariableRenamerContextPtr;

        /* ============================== VariableRenamerContext ============================== */
        /** Implementation for the context interface */
        class VariableRenamerContext : public IVariableRenamerContext {
        private:
            RenamingMap renamingMap;
        public:
            RenamingMap& getRenamingMap() override;
        };

        typedef std::shared_ptr<VariableRenamerContext> VariableRenamerContextPtr;

        /* ================================= VariableRenamer ================================== */
        /** Renames variables in the visited node based on a renaming map give by its context */
        class VariableRenamer : public DummyVisitor0,
                                public std::enable_shared_from_this<VariableRenamer> {
        private:
            IVariableRenamerContextPtr ctx;

        public:
            inline explicit VariableRenamer(IVariableRenamerContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const SimpleIdentifierPtr& node) override;
            void visit(const SortedVariablePtr& node) override;
            void visit(const VariableBindingPtr& node) override;
        };

        typedef std::shared_ptr<VariableRenamer> VariableRenamerPtr;
    }
}

#endif //INDUCTOR_AST_VAR_REPLACER_H
