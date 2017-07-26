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
        /** Context interface for variable renaming */
        class IVariableRenamerContext {
        public:
            virtual umap<std::string, std::string>& getRenamingMap() = 0;
        };

        /** Implementation for the context interface */
        class VariableRenamerContext : public IVariableRenamerContext {
        private:
            umap<std::string, std::string> renamingMap;
        public:
            VariableRenamerContext(umap<std::string, std::string> &renamingMap) {
                this->renamingMap.insert(renamingMap.begin(), renamingMap.end());
            }

            virtual umap<std::string, std::string>& getRenamingMap();
        };

        /* ================================= VariableRenamer ================================== */
        /** Renames variables in the visited node based on a renaming map give by its context */
        class VariableRenamer : public DummyVisitor0,
                                 public std::enable_shared_from_this<VariableRenamer> {
        private:
            sptr_t<IVariableRenamerContext> ctx;

        public:
            inline VariableRenamer(sptr_t<IVariableRenamerContext> ctx) : ctx(ctx) { }

            virtual void visit(sptr_t<SimpleIdentifier> node);
            virtual void visit(sptr_t<SortedVariable> node);
            virtual void visit(sptr_t<VariableBinding> node);
        };
    }
}

#endif //INDUCTOR_SEP_VAR_RENAMER_H
