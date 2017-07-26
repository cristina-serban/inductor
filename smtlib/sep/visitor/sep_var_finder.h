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
            virtual sptr_t<SymbolStack> getStack() = 0;
            virtual sptr_v<SortedVariable> &getVariables() = 0;
            virtual sptr_v<SortedVariable> &getBindings() = 0;
        };

        /* ============================== VariableFinderContext =============================== */
        /** Implementation for the context interface */
        class VariableFinderContext : public IVariableFinderContext {
        private:
            sptr_t<SymbolStack> stack;
            sptr_v<SortedVariable> vars;
            sptr_v<SortedVariable> binds;

        public:
            inline VariableFinderContext(sptr_t<SymbolStack> stack) : stack(stack) { }

            inline virtual sptr_t<SymbolStack> getStack() { return stack; }

            inline virtual sptr_v<SortedVariable> &getVariables() { return vars; }

            inline virtual sptr_v<SortedVariable> &getBindings() { return binds; }
        };

        /* ================================== VariableFinder ================================== */
        /** Finds variables occuring in a term based on a given symbol stack */
        class VariableFinder : public DummyVisitor0,
                               public std::enable_shared_from_this<VariableFinder> {
        private:
            sptr_t<IVariableFinderContext> ctx;

            void addUniqueVariable(sptr_t<SortedVariable> var);
            void addUniqueBinding(sptr_t<SortedVariable> bind);

        public:
            inline VariableFinder(sptr_t<IVariableFinderContext> ctx) : ctx(ctx) {}

            virtual void visit(sptr_t<SimpleIdentifier> node);
            virtual void visit(sptr_t<QualifiedIdentifier> node);
            virtual void visit(sptr_t<QualifiedTerm> node);

            virtual void visit(sptr_t<ExistsTerm> node);
        };
    }
}

#endif //INDUCTOR_SEP_VAR_FINDER_H
