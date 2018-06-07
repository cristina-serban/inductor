/**
 * \file sep_term_replacer.h
 * \brief Visitor that replaces a subterm of the input with another term
 */

#ifndef INDUCTOR_SEP_TERM_REPLACER_H
#define INDUCTOR_SEP_TERM_REPLACER_H

#include "sep_visitor_extra.h"

#include "sep/sep_interfaces.h"
#include "sep/sep_term.h"

#include <fstream>

namespace smtlib {
    namespace sep {
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
            TermPtr term;
        public:
            inline explicit TermReplacer(ITermReplacerContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const SimpleIdentifierPtr& node) override;
            void visit(const QualifiedIdentifierPtr& node) override;
            void visit(const DecimalLiteralPtr& node) override;
            void visit(const NumeralLiteralPtr& node) override;
            void visit(const StringLiteralPtr& node) override;

            void visit(const QualifiedTermPtr& node) override;
            void visit(const LetTermPtr& node) override;
            void visit(const ForallTermPtr& node) override;
            void visit(const ExistsTermPtr& node) override;
            void visit(const MatchTermPtr& node) override;
            void visit(const AnnotatedTermPtr& node) override;

            void visit(const TrueTermPtr& node) override;
            void visit(const FalseTermPtr& node) override;
            void visit(const NotTermPtr& node) override;
            void visit(const ImpliesTermPtr& node) override;
            void visit(const AndTermPtr& node) override;
            void visit(const OrTermPtr& node) override;
            void visit(const XorTermPtr& node) override;
            void visit(const EqualsTermPtr& node) override;
            void visit(const DistinctTermPtr& node) override;
            void visit(const IteTermPtr& node) override;

            void visit(const EmpTermPtr& node) override;
            void visit(const SepTermPtr& node) override;
            void visit(const WandTermPtr& node) override;
            void visit(const PtoTermPtr& node) override;
            void visit(const NilTermPtr& node) override;

            inline TermPtr run(const TermPtr& term) {
                return wrappedVisit(term);
            }
        };

        typedef std::shared_ptr<TermReplacer> TermReplacerPtr;
    }
}

#endif //INDUCTOR_SEP_TERM_REPLACER_H
