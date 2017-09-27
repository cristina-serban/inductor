/**
 * \file cvc_translator.h
 * \brief Translation into CVC4 expressions.
 */

#ifndef INDUCTOR_CVC_TERM_TRANSLATOR_H
#define INDUCTOR_CVC_TERM_TRANSLATOR_H

#include "sep/sep_classes.h"
#include "sep/sep_literal.h"
#include "stack/sep_symbol_stack.h"
#include "util/global_typedef.h"
#include "visitor/sep_visitor_extra.h"

// CVC4 with `make install` (both standard and non-standard prefix)
#include <cvc4/cvc4.h>

// CVC4 without `make install`
// #include "smt/smt_engine.h"

#include <memory>

namespace smtlib {
    namespace cvc {
        class ITermTranslatorContext {
        public:
            virtual CVC4::Expr getEmpLocArg() = 0;
            virtual CVC4::Expr getEmpDataArg() = 0;

            virtual sptr_t<sep::SymbolStack> getStack() = 0;

            virtual umap<std::string, umap<std::string, CVC4::Expr>> &getSymbols() = 0;
            virtual umap<std::string, CVC4::Type> &getSorts() = 0;

            virtual CVC4::Type translateSort(sptr_t<sep::Sort> sort) = 0;
            virtual std::vector<CVC4::Type> translateSorts(sptr_v<sep::Sort> sorts) =0;

            virtual CVC4::Expr translateBind(sptr_t<sep::SortedVariable> var) = 0;
            virtual CVC4::Expr translateBinds(sptr_v<sep::SortedVariable> vars) = 0;

            virtual bool isDatatypeConstructor(std::string name) = 0;
            virtual bool isDatatypeSelector(std::string name) = 0;

            virtual CVC4::DatatypeType getDatatypeForConstructor(std::string name) = 0;
            virtual CVC4::DatatypeType getDatatypeForSelector(std::string name) = 0;

            virtual void addPtoType(std::pair<CVC4::Type, CVC4::Type> ptoType) = 0;
        };

        /** Translates sep::Term instances into CVC4 expressions */
        class TermTranslator: public sep::DummyVisitor2<CVC4::Expr, CVC4::ExprManager*> {
        private:
            sptr_t<ITermTranslatorContext> ctx;

            void removeBindings(sptr_t<sep::SortedVariable> var);
            void removeBindings(sptr_v<sep::SortedVariable> vars);
        public:
            TermTranslator(sptr_t<ITermTranslatorContext> ctx) : ctx(ctx) { }

            virtual void visit(sptr_t<sep::SimpleIdentifier> node);
            virtual void visit(sptr_t<sep::QualifiedIdentifier> node);
            virtual void visit(sptr_t<sep::DecimalLiteral> node);
            virtual void visit(sptr_t<sep::NumeralLiteral> node);
            virtual void visit(sptr_t<sep::StringLiteral> node);

            virtual void visit(sptr_t<sep::QualifiedTerm> node);
            virtual void visit(sptr_t<sep::LetTerm> node);
            virtual void visit(sptr_t<sep::ForallTerm> node);
            virtual void visit(sptr_t<sep::ExistsTerm> node);
            virtual void visit(sptr_t<sep::MatchTerm> node);
            virtual void visit(sptr_t<sep::AnnotatedTerm> node);

            virtual void visit(sptr_t<sep::TrueTerm> node);
            virtual void visit(sptr_t<sep::FalseTerm> node);
            virtual void visit(sptr_t<sep::NotTerm> node);
            virtual void visit(sptr_t<sep::ImpliesTerm> node);
            virtual void visit(sptr_t<sep::AndTerm> node);
            virtual void visit(sptr_t<sep::OrTerm> node);
            virtual void visit(sptr_t<sep::XorTerm> node);
            virtual void visit(sptr_t<sep::EqualsTerm> node);
            virtual void visit(sptr_t<sep::DistinctTerm> node);
            virtual void visit(sptr_t<sep::IteTerm> node);

            virtual void visit(sptr_t<sep::EmpTerm> node);
            virtual void visit(sptr_t<sep::SepTerm> node);
            virtual void visit(sptr_t<sep::WandTerm> node);
            virtual void visit(sptr_t<sep::PtoTerm> node);
            virtual void visit(sptr_t<sep::NilTerm> node);

            friend class CVC4Interface;
        };
    }
}

#endif //INDUCTOR_CVC_TERM_TRANSLATOR_H
