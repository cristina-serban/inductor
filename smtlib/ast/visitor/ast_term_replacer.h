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
            virtual TermPtr getTerm() = 0;
            virtual void setTerm(const TermPtr& term) = 0;

            virtual TermPtr getReplacement() = 0;
            virtual void setReplacement(const TermPtr& expr) = 0;
        };

        typedef std::shared_ptr<ITermReplacerContext> ITermReplacerContextPtr;

        /* =============================== TermReplacerContext ================================ */
        /** Implementation for the context interface */
        class TermReplacerContext: public ITermReplacerContext {
        private:
            TermPtr term;
            TermPtr repl;

        public:
            TermReplacerContext(TermPtr term, TermPtr repl)
                    : term(std::move(term))
                    , repl(std::move(repl)) {}

            TermPtr getTerm() override { return term; }
            void setTerm(const TermPtr& term) override { this->term = term; }

            TermPtr getReplacement() override { return repl; }
            void setReplacement(const TermPtr& repl) override { this->repl = repl; }
        };

        typedef std::shared_ptr<TermReplacerContext> TermReplacerContextPtr;

        /* =================================== TermReplacer =================================== */
        /** Replaces a subterm of the input with another term given by its context */
        class TermReplacer : public DummyVisitor1<TermPtr>,
                             public std::enable_shared_from_this<TermReplacer> {
        private:
            ITermReplacerContextPtr ctx;
        public:
            inline explicit TermReplacer(ITermReplacerContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const QualifiedTermPtr& node) override;
            void visit(const LetTermPtr& node) override;
            void visit(const ForallTermPtr& node) override;
            void visit(const ExistsTermPtr& node) override;
            void visit(const MatchTermPtr& node) override;
            void visit(const AnnotatedTermPtr& node) override;
        };

        typedef std::shared_ptr<TermReplacer> TermReplacerPtr;
    }
}

#endif //INDUCTOR_AST_TERM_REPLACER_H
