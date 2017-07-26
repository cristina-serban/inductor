/**
 * \file ast_visitor.h
 * \brief Abstract visitor classes the smtlib::ast hierarchy.
 */

#ifndef INDUCTOR_AST_VISITOR_H
#define INDUCTOR_AST_VISITOR_H

#include "ast/ast_abstract.h"
#include "ast/ast_classes.h"
#include "util/global_typedef.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        class Visitor0 {
        protected:
            virtual void visit0(sptr_t<Node> node);
            template<class T>
            void visit0(sptr_v<T>& arr) {
                for (auto item = arr.begin(); item != arr.end(); item++) {
                    visit0(*item);
                }
            }
        public:
            virtual void visit(sptr_t<Attribute> node) = 0;
            virtual void visit(sptr_t<CompAttributeValue> node) = 0;

            virtual void visit(sptr_t<Symbol> node) = 0;
            virtual void visit(sptr_t<Keyword> node) = 0;
            virtual void visit(sptr_t<MetaSpecConstant> node) = 0;
            virtual void visit(sptr_t<BooleanValue> node) = 0;
            virtual void visit(sptr_t<PropLiteral> node) = 0;

            virtual void visit(sptr_t<AssertCommand> node) = 0;
            virtual void visit(sptr_t<CheckSatCommand> node) = 0;
            virtual void visit(sptr_t<CheckSatAssumCommand> node) = 0;
            virtual void visit(sptr_t<DeclareConstCommand> node) = 0;
            virtual void visit(sptr_t<DeclareDatatypeCommand> node) = 0;
            virtual void visit(sptr_t<DeclareDatatypesCommand> node) = 0;
            virtual void visit(sptr_t<DeclareFunCommand> node) = 0;
            virtual void visit(sptr_t<DeclareSortCommand> node) = 0;
            virtual void visit(sptr_t<DefineFunCommand> node) = 0;
            virtual void visit(sptr_t<DefineFunRecCommand> node) = 0;
            virtual void visit(sptr_t<DefineFunsRecCommand> node) = 0;
            virtual void visit(sptr_t<DefineSortCommand> node) = 0;
            virtual void visit(sptr_t<EchoCommand> node) = 0;
            virtual void visit(sptr_t<ExitCommand> node) = 0;
            virtual void visit(sptr_t<GetAssertsCommand> node) = 0;
            virtual void visit(sptr_t<GetAssignsCommand> node) = 0;
            virtual void visit(sptr_t<GetInfoCommand> node) = 0;
            virtual void visit(sptr_t<GetModelCommand> node) = 0;
            virtual void visit(sptr_t<GetOptionCommand> node) = 0;
            virtual void visit(sptr_t<GetProofCommand> node) = 0;
            virtual void visit(sptr_t<GetUnsatAssumsCommand> node) = 0;
            virtual void visit(sptr_t<GetUnsatCoreCommand> node) = 0;
            virtual void visit(sptr_t<GetValueCommand> node) = 0;
            virtual void visit(sptr_t<PopCommand> node) = 0;
            virtual void visit(sptr_t<PushCommand> node) = 0;
            virtual void visit(sptr_t<ResetCommand> node) = 0;
            virtual void visit(sptr_t<ResetAssertsCommand> node) = 0;
            virtual void visit(sptr_t<SetInfoCommand> node) = 0;
            virtual void visit(sptr_t<SetLogicCommand> node) = 0;
            virtual void visit(sptr_t<SetOptionCommand> node) = 0;

            virtual void visit(sptr_t<FunctionDeclaration> node) = 0;
            virtual void visit(sptr_t<FunctionDefinition> node) = 0;

            virtual void visit(sptr_t<SimpleIdentifier> node) = 0;
            virtual void visit(sptr_t<QualifiedIdentifier> node) = 0;

            virtual void visit(sptr_t<DecimalLiteral> node) = 0;
            virtual void visit(sptr_t<NumeralLiteral> node) = 0;
            virtual void visit(sptr_t<StringLiteral> node) = 0;

            virtual void visit(sptr_t<Logic> node) = 0;
            virtual void visit(sptr_t<Theory> node) = 0;
            virtual void visit(sptr_t<Script> node) = 0;

            virtual void visit(sptr_t<Sort> node) = 0;

            virtual void visit(sptr_t<CompSExpression> node) = 0;

            virtual void visit(sptr_t<SortSymbolDeclaration> node) = 0;
            virtual void visit(sptr_t<SpecConstFunDeclaration> node) = 0;
            virtual void visit(sptr_t<MetaSpecConstFunDeclaration> node) = 0;
            virtual void visit(sptr_t<SimpleFunDeclaration> node) = 0;
            virtual void visit(sptr_t<ParametricFunDeclaration> node) = 0;

            virtual void visit(sptr_t<SortDeclaration> node) = 0;
            virtual void visit(sptr_t<SelectorDeclaration> node) = 0;
            virtual void visit(sptr_t<ConstructorDeclaration> node) = 0;
            virtual void visit(sptr_t<SimpleDatatypeDeclaration> node) = 0;
            virtual void visit(sptr_t<ParametricDatatypeDeclaration> node) = 0;

            virtual void visit(sptr_t<QualifiedConstructor> node) = 0;
            virtual void visit(sptr_t<QualifiedPattern> node) = 0;
            virtual void visit(sptr_t<MatchCase> node) = 0;

            virtual void visit(sptr_t<QualifiedTerm> node) = 0;
            virtual void visit(sptr_t<LetTerm> node) = 0;
            virtual void visit(sptr_t<ForallTerm> node) = 0;
            virtual void visit(sptr_t<ExistsTerm> node) = 0;
            virtual void visit(sptr_t<MatchTerm> node) = 0;
            virtual void visit(sptr_t<AnnotatedTerm> node) = 0;

            virtual void visit(sptr_t<SortedVariable> node) = 0;
            virtual void visit(sptr_t<VariableBinding> node) = 0;
        };

        class DummyVisitor0 : public virtual Visitor0 {
        public:
            virtual void visit(sptr_t<Attribute> node);
            virtual void visit(sptr_t<CompAttributeValue> node);

            virtual void visit(sptr_t<Symbol> node);
            virtual void visit(sptr_t<Keyword> node);
            virtual void visit(sptr_t<MetaSpecConstant> node);
            virtual void visit(sptr_t<BooleanValue> node);
            virtual void visit(sptr_t<PropLiteral> node);

            virtual void visit(sptr_t<AssertCommand> node);
            virtual void visit(sptr_t<CheckSatCommand> node);
            virtual void visit(sptr_t<CheckSatAssumCommand> node);
            virtual void visit(sptr_t<DeclareConstCommand> node);
            virtual void visit(sptr_t<DeclareDatatypeCommand> node);
            virtual void visit(sptr_t<DeclareDatatypesCommand> node);
            virtual void visit(sptr_t<DeclareFunCommand> node);
            virtual void visit(sptr_t<DeclareSortCommand> node);
            virtual void visit(sptr_t<DefineFunCommand> node);
            virtual void visit(sptr_t<DefineFunRecCommand> node);
            virtual void visit(sptr_t<DefineFunsRecCommand> node);
            virtual void visit(sptr_t<DefineSortCommand> node);
            virtual void visit(sptr_t<EchoCommand> node);
            virtual void visit(sptr_t<ExitCommand> node);
            virtual void visit(sptr_t<GetAssertsCommand> node);
            virtual void visit(sptr_t<GetAssignsCommand> node);
            virtual void visit(sptr_t<GetInfoCommand> node);
            virtual void visit(sptr_t<GetModelCommand> node);
            virtual void visit(sptr_t<GetOptionCommand> node);
            virtual void visit(sptr_t<GetProofCommand> node);
            virtual void visit(sptr_t<GetUnsatAssumsCommand> node);
            virtual void visit(sptr_t<GetUnsatCoreCommand> node);
            virtual void visit(sptr_t<GetValueCommand> node);
            virtual void visit(sptr_t<PopCommand> node);
            virtual void visit(sptr_t<PushCommand> node);
            virtual void visit(sptr_t<ResetCommand> node);
            virtual void visit(sptr_t<ResetAssertsCommand> node);
            virtual void visit(sptr_t<SetInfoCommand> node);
            virtual void visit(sptr_t<SetLogicCommand> node);
            virtual void visit(sptr_t<SetOptionCommand> node);

            virtual void visit(sptr_t<FunctionDeclaration> node);
            virtual void visit(sptr_t<FunctionDefinition> node);

            virtual void visit(sptr_t<SimpleIdentifier> node);
            virtual void visit(sptr_t<QualifiedIdentifier> node);

            virtual void visit(sptr_t<DecimalLiteral> node);
            virtual void visit(sptr_t<NumeralLiteral> node);
            virtual void visit(sptr_t<StringLiteral> node);

            virtual void visit(sptr_t<Logic> node);
            virtual void visit(sptr_t<Theory> node);
            virtual void visit(sptr_t<Script> node);

            virtual void visit(sptr_t<Sort> node);

            virtual void visit(sptr_t<CompSExpression> node);

            virtual void visit(sptr_t<SortSymbolDeclaration> node);
            virtual void visit(sptr_t<SortDeclaration> node);
            virtual void visit(sptr_t<SelectorDeclaration> node);
            virtual void visit(sptr_t<ConstructorDeclaration> node);
            virtual void visit(sptr_t<SimpleDatatypeDeclaration> node);
            virtual void visit(sptr_t<ParametricDatatypeDeclaration> node);

            virtual void visit(sptr_t<QualifiedConstructor> node);
            virtual void visit(sptr_t<QualifiedPattern> node);
            virtual void visit(sptr_t<MatchCase> node);

            virtual void visit(sptr_t<SpecConstFunDeclaration> node);
            virtual void visit(sptr_t<MetaSpecConstFunDeclaration> node);
            virtual void visit(sptr_t<SimpleFunDeclaration> node);
            virtual void visit(sptr_t<ParametricFunDeclaration> node);

            virtual void visit(sptr_t<QualifiedTerm> node);
            virtual void visit(sptr_t<LetTerm> node);
            virtual void visit(sptr_t<ForallTerm> node);
            virtual void visit(sptr_t<ExistsTerm> node);
            virtual void visit(sptr_t<MatchTerm> node);
            virtual void visit(sptr_t<AnnotatedTerm> node);

            virtual void visit(sptr_t<SortedVariable> node);
            virtual void visit(sptr_t<VariableBinding> node);
        };
    }
}

#endif //INDUCTOR_AST_VISITOR_H