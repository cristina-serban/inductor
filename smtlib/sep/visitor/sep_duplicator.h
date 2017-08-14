/**
 * \file sep_node_duplicator.h
 * \brief Visitor that clones a node
 */

#ifndef PARSE_SMTLIB_SMT_NODE_DUPLICATOR_H
#define PARSE_SMTLIB_SMT_NODE_DUPLICATOR_H

#include "visitor/sep_visitor.h"
#include "visitor/sep_visitor_extra.h"

namespace smtlib {
    namespace sep {
        /** Clones the visited node */
        class Duplicator : public DummyVisitor1<sptr_t<Node>> {
        private:
            template<class T>
            std::vector<sptr_t<T>> duplicate(std::vector<sptr_t<T>> vec) {
                std::vector<sptr_t<T>> newVec;

                for (auto it = vec.begin(); it != vec.end(); it++) {
                    newVec.push_back(std::dynamic_pointer_cast<T>(wrappedVisit(*it)));
                }

                return newVec;
            }

        public:
            virtual void visit(sptr_t<SimpleAttribute> node);
            virtual void visit(sptr_t<SExpressionAttribute> node);
            virtual void visit(sptr_t<SymbolAttribute> node);
            virtual void visit(sptr_t<BooleanAttribute> node);
            virtual void visit(sptr_t<NumeralAttribute> node);
            virtual void visit(sptr_t<DecimalAttribute> node);
            virtual void visit(sptr_t<StringAttribute> node);
            virtual void visit(sptr_t<TheoriesAttribute> node);
            virtual void visit(sptr_t<SortsAttribute> node);
            virtual void visit(sptr_t<FunsAttribute> node);

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

            virtual void visit(sptr_t<SortDeclaration> node);
            virtual void visit(sptr_t<SelectorDeclaration> node);
            virtual void visit(sptr_t<ConstructorDeclaration> node);
            virtual void visit(sptr_t<SimpleDatatypeDeclaration> node);
            virtual void visit(sptr_t<ParametricDatatypeDeclaration> node);

            virtual void visit(sptr_t<FunctionDeclaration> node);
            virtual void visit(sptr_t<FunctionDefinition> node);

            virtual void visit(sptr_t<SimpleIdentifier> node);
            virtual void visit(sptr_t<QualifiedIdentifier> node);

            virtual void visit(sptr_t<NumeralLiteral> node);
            virtual void visit(sptr_t<DecimalLiteral> node);
            virtual void visit(sptr_t<StringLiteral> node);

            virtual void visit(sptr_t<Logic> node);
            virtual void visit(sptr_t<Theory> node);
            virtual void visit(sptr_t<Script> node);

            virtual void visit(sptr_t<QualifiedConstructor> node);
            virtual void visit(sptr_t<QualifiedPattern> node);
            virtual void visit(sptr_t<MatchCase> node);

            virtual void visit(sptr_t<CompSExpression> node);

            virtual void visit(sptr_t<Sort> node);

            virtual void visit(sptr_t<SortSymbolDeclaration> node);
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

            virtual void visit(sptr_t<SortedVariable> node);
            virtual void visit(sptr_t<VariableBinding> node);
        };

        typedef std::shared_ptr<Duplicator> DuplicatorPtr;
    }
}

#endif //PARSE_SMTLIB_SMT_NODE_DUPLICATOR_H
