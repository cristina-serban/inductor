/**
 * \file ast_term_sorter.h
 * \brief Visitor that determines the sort of a term
 */

#ifndef INDUCTOR_AST_TERM_SORTER_H
#define INDUCTOR_AST_TERM_SORTER_H

#include "ast_visitor_extra.h"

#include "stack/ast_symbol_stack.h"
#include "util/configuration.h"

#include <algorithm>

namespace smtlib {
    namespace ast {
        class SortednessChecker;

        /** Context interface for term sorting */
        class ITermSorterContext {
        public:
            virtual sptr_t<SymbolStack> getStack() = 0;
            virtual sptr_t<SortednessChecker> getChecker() = 0;
            virtual sptr_t<Configuration> getConfiguration() = 0;
        };

        /** Determines the sort of a term */
        class TermSorter : public DummyVisitor1<sptr_t<Sort>> {
        private:
            sptr_t<ITermSorterContext> ctx;

            static sptr_v<Sort> extractReturnSorts(sptr_v<FunInfo> infos, size_t arity, bool parametric);
            static void extractReturnSorts(sptr_v<FunInfo> infos, size_t arity, bool parametric, sptr_v<Sort> &accum);

            static sptr_v<Sort> extractParamMatches(sptr_v<FunInfo> infos, size_t arity,
                                                    sptr_t<Sort> sort, sptr_t<SymbolStack> stack);

            static void extractParamMatches(sptr_v<FunInfo> infos, size_t arity, sptr_t<Sort> sort,
                                            sptr_t<SymbolStack> stack, sptr_v<Sort> &accum);

            static std::vector<std::string> extractParamNames(sptr_t<FunInfo> info);

            /**
             * Attempts to unify two sorts
             * \param sort1     Sort to unify
             * \param sort2     Sort onto which to unify
             * \param params    Sort parameters occurring in sort1 and sort2
             * \param mapping   Mapping of sort parameters to sorts
             */
            static bool unify(sptr_t<Sort> sort1, sptr_t<Sort> sort2,
                              std::vector<std::string> &params,
                              sptr_um2<std::string, Sort> &mapping);

        public:
            inline TermSorter(sptr_t<ITermSorterContext> ctx) : ctx(ctx) { }

            virtual void visit(sptr_t<SimpleIdentifier> node);
            virtual void visit(sptr_t<QualifiedIdentifier> node);
            virtual void visit(sptr_t<DecimalLiteral> node);
            virtual void visit(sptr_t<NumeralLiteral> node);
            virtual void visit(sptr_t<StringLiteral> node);

            virtual void visit(sptr_t<QualifiedTerm> node);
            virtual void visit(sptr_t<LetTerm> node);
            virtual void visit(sptr_t<ForallTerm> node);
            virtual void visit(sptr_t<ExistsTerm> node);
            virtual void visit(sptr_t<MatchTerm> node);

            virtual void visit(sptr_t<AnnotatedTerm> node);

            sptr_t<Sort> run(sptr_t<Node> node) {
                return wrappedVisit(node);
            }
        };
    }
}


#endif //INDUCTOR_AST_TERM_SORTER_H
