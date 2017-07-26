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
        /* ============================= IVariableRenamerContext ============================== */
        /** Context interface for variable renaming */
        class IVariableRenamerContext {
        public:
            virtual umap<std::string, std::string>& getRenamingMap() = 0;
        };

        /* ============================== VariableRenamerContext ============================== */
        /** Implementation for the context interface */
        class VariableRenamerContext : public IVariableRenamerContext {
        private:
            umap<std::string, std::string> renamingMap;
        public:
            virtual umap<std::string, std::string>& getRenamingMap();
        };

        /* ================================= VariableRenamer ================================== */
        /** Renames variables in the visited node based on a renaming map give by its context */
        class VariableRenamer : public DummyVisitor0,
                                public std::enable_shared_from_this<VariableRenamer> {
        private:
            sptr_t<IVariableRenamerContext> ctx;

        public:
            inline VariableRenamer(sptr_t<IVariableRenamerContext> ctx) : ctx(ctx) {}

            virtual void visit(sptr_t<SimpleIdentifier> node);
            virtual void visit(sptr_t<SortedVariable> node);
            virtual void visit(sptr_t<VariableBinding> node);
        };
    }
}

#endif //INDUCTOR_AST_VAR_REPLACER_H
