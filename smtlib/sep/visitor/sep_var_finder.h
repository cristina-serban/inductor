/**
 * \file sep_var_finder.h
 * \brief Visitor that finds variables occuring in a term based on a given symbol stack
 */

#ifndef INDUCTOR_SEP_VAR_FINDER_H
#define INDUCTOR_SEP_VAR_FINDER_H

#include "sep_visitor_extra.h"

#include "sep/sep_identifier.h"
#include "stack/sep_symbol_stack.h"

namespace smtlib {
    namespace sep {

        /* ============================== IVariableFinderContext ============================== */
        /** Context interface for finding and adding variables to a symbol stack */
        class IVariableFinderContext {
        public:
            virtual SymbolStackPtr getStack() = 0;
            virtual std::vector<SortedVariablePtr>& getVariables() = 0;
            virtual std::vector<SortedVariablePtr>& getBindings() = 0;
        };

        typedef std::shared_ptr<IVariableFinderContext> IVariableFinderContextPtr;

        /* ============================== VariableFinderContext =============================== */
        /** Implementation for the context interface */
        class VariableFinderContext : public IVariableFinderContext {
        private:
            SymbolStackPtr stack;
            std::vector<SortedVariablePtr> vars;
            std::vector<SortedVariablePtr> binds;

        public:
            inline explicit VariableFinderContext(SymbolStackPtr stack)
                    : stack(std::move(stack)) {}

            inline SymbolStackPtr getStack() override { return stack; }

            inline std::vector<SortedVariablePtr>& getVariables() override { return vars; }

            inline std::vector<SortedVariablePtr>& getBindings() override { return binds; }
        };

        typedef std::shared_ptr<VariableFinderContext> VariableFinderContextPtr;

        /* ================================== VariableFinder ================================== */
        /** Finds variables occuring in a term based on a given symbol stack */
        class VariableFinder : public DummyVisitor0,
                               public std::enable_shared_from_this<VariableFinder> {
        private:
            IVariableFinderContextPtr ctx;

            void addUniqueVariable(const SortedVariablePtr& var);
            void addUniqueBinding(const SortedVariablePtr& bind);

        public:
            inline explicit VariableFinder(IVariableFinderContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const SimpleIdentifierPtr& node) override;
            void visit(const QualifiedIdentifierPtr& node) override;
            void visit(const QualifiedTermPtr& node) override;

            void visit(const ExistsTermPtr& node) override;
        };

        typedef std::shared_ptr<VariableFinder> VariableFinderPtr;
    }
}

#endif //INDUCTOR_SEP_VAR_FINDER_H
