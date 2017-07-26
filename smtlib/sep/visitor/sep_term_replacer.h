/**
 * \file sep_term_replacer.h
 * \brief Visitor that replaces a subterm of the input with another term
 */

#ifndef INDUCTOR_SEP_TERM_REPLACER_H
#define INDUCTOR_SEP_TERM_REPLACER_H

#include "sep_visitor_extra.h"

#include "sep/sep_interfaces.h"
#include "sep/sep_term.h"
#include "util/global_typedef.h"

#include <fstream>

namespace smtlib {
    namespace sep {
        /* =============================== ITermReplacerContext =============================== */
        /** Context interface for term replacement */
        class ITermReplacerContext {
        public:
            virtual sptr_t<Term> getTerm() = 0;
            virtual void setTerm(sptr_t<Term> term) = 0;

            virtual sptr_t<Term> getReplacement() = 0;
            virtual void setReplacement(sptr_t<Term> expr) = 0;
        };

        /* =============================== TermReplacerContext ================================ */
        /** Implementation for the context interface */
        class TermReplacerContext: public ITermReplacerContext {
        private:
            sptr_t<Term> term;
            sptr_t<Term> repl;
        public:
            TermReplacerContext(sptr_t<Term> term, sptr_t<Term> repl)
                    : term(term), repl(repl) {}

            virtual sptr_t<Term> getTerm() { return term; }
            virtual void setTerm(sptr_t<Term> term) { this->term = term; }

            virtual sptr_t<Term> getReplacement() { return repl; }
            virtual void setReplacement(sptr_t<Term> repl) { this->repl = repl; }
        };

        /* =================================== TermReplacer =================================== */
        /** Replaces a subterm of the input with another term given by its context */
        class TermReplacer : public DummyVisitor1<sptr_t<Term>>,
                             public std::enable_shared_from_this<TermReplacer> {
        private:
            sptr_t<ITermReplacerContext> ctx;
            sptr_t<Term> term;
        public:
            inline TermReplacer(sptr_t<ITermReplacerContext> ctx) : ctx(ctx) { }

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

            inline sptr_t<Term> run(sptr_t<Term> term) {
                return wrappedVisit(term);
            }
        };
    }
}

#endif //INDUCTOR_SEP_TERM_REPLACER_H
