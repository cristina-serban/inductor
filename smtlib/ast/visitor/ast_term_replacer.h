/**
 * \file ast_term_replacer.h
 * \brief Visitor that replaces a subterm of the input with another term
 */

#ifndef INDUCTOR_AST_TERM_REPLACER_H
#define INDUCTOR_AST_TERM_REPLACER_H

#include "ast_visitor_extra.h"

#include "ast/ast_interfaces.h"

#include <fstream>

namespace smtlib {
    namespace ast {
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
        public:
            inline TermReplacer(sptr_t<ITermReplacerContext> ctx) : ctx(ctx) { }

            virtual void visit(sptr_t<QualifiedTerm> node);
            virtual void visit(sptr_t<LetTerm> node);
            virtual void visit(sptr_t<ForallTerm> node);
            virtual void visit(sptr_t<ExistsTerm> node);
            virtual void visit(sptr_t<MatchTerm> node);
            virtual void visit(sptr_t<AnnotatedTerm> node);
        };
    }
}

#endif //INDUCTOR_AST_TERM_REPLACER_H
