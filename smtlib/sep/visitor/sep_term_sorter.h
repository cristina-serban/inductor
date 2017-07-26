#ifndef INDUCTOR_SEP_TERM_SORTER_H
#define INDUCTOR_SEP_TERM_SORTER_H

#include "visitor/sep_visitor.h"
#include "visitor/sep_visitor_extra.h"

#include "stack/sep_symbol_stack.h"

namespace smtlib {
    namespace sep {
        class ITermSorterContext {
        public:
            virtual sptr_t<SymbolStack> getStack() = 0;
        };

        class TermSorterContext : public ITermSorterContext {
        private:
            sptr_t<SymbolStack> stack;
        public:
            inline TermSorterContext(sptr_t<SymbolStack> stack) : stack(stack) { }

            inline virtual sptr_t<SymbolStack> getStack() { return stack; }

            inline void setStack(sptr_t<SymbolStack> stack) { this->stack = stack; }
        };

        class TermSorter : public DummyVisitor1<sptr_t<Sort>> {
        private:
            sptr_t<ITermSorterContext> ctx;

            bool getParamMapping(std::vector<std::string> &params,
                                 sptr_um2<std::string, Sort> &mapping,
                                 sptr_t<Sort> sort1, sptr_t<Sort> sort2);

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

            virtual void visit(sptr_t<TrueTerm> node);
            virtual void visit(sptr_t<FalseTerm> node);
            virtual void visit(sptr_t<NotTerm> node);
            virtual void visit(sptr_t<ImpliesTerm> node);
            virtual void visit(sptr_t<AndTerm> node);
            virtual void visit(sptr_t<OrTerm> node);
            virtual void visit(sptr_t<XorTerm> node);
            virtual void visit(sptr_t<EqualsTerm> node);
            virtual void visit(sptr_t<DistinctTerm> node);
            virtual void visit(sptr_t<IteTerm> node);

            virtual void visit(sptr_t<EmpTerm> node);
            virtual void visit(sptr_t<SepTerm> node);
            virtual void visit(sptr_t<WandTerm> node);
            virtual void visit(sptr_t<PtoTerm> node);
            virtual void visit(sptr_t<NilTerm> node);

            sptr_t<Sort> run(sptr_t<Node> node) {
                return wrappedVisit(node);
            }
        };
    }
}

#endif //INDUCTOR_SEP_TERM_SORTER_H
