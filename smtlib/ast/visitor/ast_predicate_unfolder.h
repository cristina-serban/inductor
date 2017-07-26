#ifndef INDUCTOR_AST_PREDICATE_UNFOLDER_H
#define INDUCTOR_AST_PREDICATE_UNFOLDER_H

#include "ast_visitor_extra.h"

#include "ast/ast_fun.h"
#include "ast/ast_interfaces.h"
#include "ast/ast_term.h"

#include <fstream>

namespace smtlib {
    namespace ast {
        /* ============================ IPredicateUnfolderContext ============================= */
        class IPredicateUnfolderContext {
        public:
            virtual int getUnfoldLevel() = 0;
            virtual void setUnfoldLevel(int level) = 0;

            virtual bool isExistential() = 0;
            virtual void setExistential(bool existential) = 0;

            virtual std::string getOutputPath() = 0;
            virtual std::string setOutputPath(std::string output) = 0;

            virtual bool isCvcEmp() = 0;
            virtual void setCvcEmp(bool cvcEmp) = 0;
        };

        /* ============================= PredicateUnfolderContext ============================= */
        class PredicateUnfolderContext : public IPredicateUnfolderContext {
        private:
            int unfoldLevel;
            bool existential;
            std::string output;
            bool cvcEmp;

        public:
            inline PredicateUnfolderContext(int level, bool existential, std::string output, bool cvcEmp)
                    : unfoldLevel(level), existential(existential), output(output), cvcEmp(cvcEmp) {}

            virtual int getUnfoldLevel() { return unfoldLevel; }
            virtual void setUnfoldLevel(int level) { unfoldLevel = level; }

            virtual bool isExistential() { return existential; }
            virtual void setExistential(bool existential) { this->existential = existential; }

            virtual std::string getOutputPath() { return output; }
            virtual std::string setOutputPath(std::string output) { this->output = output; }

            virtual bool isCvcEmp() { return cvcEmp; }
            virtual void setCvcEmp(bool cvcEmp) { this->cvcEmp = cvcEmp; }
        };

        /* ================================ PredicateUnfolder ================================= */
        class PredicateUnfolder : public DummyVisitor2<sptr_t<Node>, int>,
                                  public std::enable_shared_from_this<PredicateUnfolder> {
        private:
            sptr_t<FunctionDefinition> currentDefinition;
            sptr_t<Term> currentBaseCase;
            sptr_t<ExistsTerm> currentRecCase;

            sptr_t<IPredicateUnfolderContext> ctx;

            int findCounter;
            int prevFind;
            int *predLevelCounter;
            int predLevel;
            std::fstream output;

        public:
            inline PredicateUnfolder(sptr_t<IPredicateUnfolderContext> ctx) : ctx(ctx) { }

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

            virtual void visit(sptr_t<SpecConstFunDeclaration> node);
            virtual void visit(sptr_t<MetaSpecConstFunDeclaration> node);
            virtual void visit(sptr_t<SimpleFunDeclaration> node);
            virtual void visit(sptr_t<ParametricFunDeclaration> node);

            virtual void visit(sptr_t<SortDeclaration> node);
            virtual void visit(sptr_t<SelectorDeclaration> node);
            virtual void visit(sptr_t<ConstructorDeclaration> node);
            virtual void visit(sptr_t<SimpleDatatypeDeclaration> node);
            virtual void visit(sptr_t<ParametricDatatypeDeclaration> node);

            virtual void visit(sptr_t<QualifiedConstructor> node);
            virtual void visit(sptr_t<QualifiedPattern> node);
            virtual void visit(sptr_t<MatchCase> node);

            virtual void visit(sptr_t<QualifiedTerm> node);
            virtual void visit(sptr_t<LetTerm> node);
            virtual void visit(sptr_t<ForallTerm> node);
            virtual void visit(sptr_t<ExistsTerm> node);
            virtual void visit(sptr_t<MatchTerm> node);
            virtual void visit(sptr_t<AnnotatedTerm> node);

            virtual void visit(sptr_t<SortedVariable> node);
            virtual void visit(sptr_t<VariableBinding> node);

            sptr_t<Node> run(sptr_t<Node> node) {
                return wrappedVisit(0, node);
            }
        };
    }
}

#endif //INDUCTOR_AST_PREDICATE_UNFOLDER_H
