/**
 * \file cvc_translator.h
 * \brief Translation into CVC4 expressions.
 */

#ifndef INDUCTOR_CVC_TERM_TRANSLATOR_H
#define INDUCTOR_CVC_TERM_TRANSLATOR_H

#include "sep/sep_classes.h"
#include "sep/sep_literal.h"
#include "stack/sep_symbol_stack.h"
#include "visitor/sep_visitor_extra.h"

// CVC4 with `make install` (both standard and non-standard prefix)
#include <cvc4/cvc4.h>

// CVC4 without `make install`
// #include "smt/smt_engine.h"

#include <memory>
#include <unordered_map>

namespace smtlib {
    namespace cvc {
        typedef std::unordered_map<std::string, std::unordered_map<std::string, CVC4::Expr>> CVCSymbolMap;
        typedef std::unordered_map<std::string, CVC4::Type> CVCSortMap;

        class ITermTranslatorContext {
        public:
            virtual CVC4::Expr getEmpLocArg() = 0;
            virtual CVC4::Expr getEmpDataArg() = 0;

            virtual sep::SymbolStackPtr getStack() = 0;

            virtual CVCSymbolMap& getSymbols() = 0;
            virtual CVCSortMap& getSorts() = 0;

            virtual CVC4::Type translateSort(const sep::SortPtr& sort) = 0;
            virtual std::vector<CVC4::Type> translateSorts(const std::vector<sep::SortPtr>& sorts) = 0;

            virtual CVC4::Expr translateBind(const sep::SortedVariablePtr& var) = 0;
            virtual CVC4::Expr translateBinds(const std::vector<sep::SortedVariablePtr>& vars) = 0;

            virtual bool isDatatypeConstructor(const std::string& name) = 0;
            virtual bool isDatatypeSelector(const std::string& name) = 0;

            virtual CVC4::DatatypeType getDatatypeForConstructor(const std::string& name) = 0;
            virtual CVC4::DatatypeType getDatatypeForSelector(const std::string& name) = 0;

            virtual void addPtoType(const std::pair<CVC4::Type, CVC4::Type>& ptoType) = 0;
        };

        typedef std::shared_ptr<ITermTranslatorContext> ITermTranslatorContextPtr;

        /** Translates sep::Term instances into CVC4 expressions */
        class TermTranslator: public sep::DummyVisitor2<CVC4::Expr, CVC4::ExprManager*> {
        private:
            ITermTranslatorContextPtr ctx;

            void removeBindings(const sep::SortedVariablePtr& var);
            void removeBindings(const std::vector<sep::SortedVariablePtr>& vars);
        public:
            explicit TermTranslator(ITermTranslatorContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const sep::SimpleIdentifierPtr& node) override;
            void visit(const sep::QualifiedIdentifierPtr& node) override;
            void visit(const sep::DecimalLiteralPtr& node) override;
            void visit(const sep::NumeralLiteralPtr& node) override;
            void visit(const sep::StringLiteralPtr& node) override;

            void visit(const sep::QualifiedTermPtr& node) override;
            void visit(const sep::LetTermPtr& node) override;
            void visit(const sep::ForallTermPtr& node) override;
            void visit(const sep::ExistsTermPtr& node) override;
            void visit(const sep::MatchTermPtr& node) override;
            void visit(const sep::AnnotatedTermPtr& node) override;

            void visit(const sep::TrueTermPtr& node) override;
            void visit(const sep::FalseTermPtr& node) override;
            void visit(const sep::NotTermPtr& node) override;
            void visit(const sep::ImpliesTermPtr& node) override;
            void visit(const sep::AndTermPtr& node) override;
            void visit(const sep::OrTermPtr& node) override;
            void visit(const sep::XorTermPtr& node) override;
            void visit(const sep::EqualsTermPtr& node) override;
            void visit(const sep::DistinctTermPtr& node) override;
            void visit(const sep::IteTermPtr& node) override;

            void visit(const sep::EmpTermPtr& node) override;
            void visit(const sep::SepTermPtr& node) override;
            void visit(const sep::WandTermPtr& node) override;
            void visit(const sep::PtoTermPtr& node) override;
            void visit(const sep::NilTermPtr& node) override;

            friend class CVC4Interface;
        };

        typedef std::shared_ptr<TermTranslator> TermTranslatorPtr;
    }
}

#endif //INDUCTOR_CVC_TERM_TRANSLATOR_H
