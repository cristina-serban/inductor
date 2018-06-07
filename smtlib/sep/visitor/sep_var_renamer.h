/**
 * \file sep_var_renamer.h
 * \brief Visitor that renames variables
 */

#ifndef INDUCTOR_SEP_VAR_RENAMER_H
#define INDUCTOR_SEP_VAR_RENAMER_H

#include "sep_visitor_extra.h"

#include "sep/sep_identifier.h"

#include <unordered_map>

namespace smtlib {
    namespace sep {
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
            std::unordered_map<std::string, std::string> renamingMap;
        public:
            inline explicit VariableRenamerContext(RenamingMap renamingMap)
                    : renamingMap(std::move(renamingMap)) {}

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

#endif //INDUCTOR_SEP_VAR_RENAMER_H
