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
            virtual std::string setOutputPath(const std::string& output) = 0;

            virtual bool isCvcEmp() = 0;
            virtual void setCvcEmp(bool cvcEmp) = 0;
        };

        typedef std::shared_ptr<IPredicateUnfolderContext> IPredicateUnfolderContextPtr;

        /* ============================= PredicateUnfolderContext ============================= */
        class PredicateUnfolderContext : public IPredicateUnfolderContext {
        private:
            int unfoldLevel;
            bool existential;
            std::string output;
            bool cvcEmp;

        public:
            inline PredicateUnfolderContext(int level, bool existential, std::string output, bool cvcEmp)
                    : unfoldLevel(level)
                    , existential(existential)
                    , output(std::move(output))
                    , cvcEmp(cvcEmp) {}

            int getUnfoldLevel() override { return unfoldLevel; }
            void setUnfoldLevel(int level) override { unfoldLevel = level; }

            bool isExistential() override { return existential; }
            void setExistential(bool existential) override { this->existential = existential; }

            std::string getOutputPath() override { return output; }
            std::string setOutputPath(const std::string& output) override { this->output = output; }

            bool isCvcEmp() override { return cvcEmp; }
            void setCvcEmp(bool cvcEmp) override { this->cvcEmp = cvcEmp; }
        };

        typedef std::shared_ptr<PredicateUnfolderContext> PredicateUnfolderContextPtr;

        /* ================================ PredicateUnfolder ================================= */
        class PredicateUnfolder : public DummyVisitor2<NodePtr, int>,
                                  public std::enable_shared_from_this<PredicateUnfolder> {
        private:
            FunctionDefinitionPtr currentDefinition;
            TermPtr currentBaseCase;
            ExistsTermPtr currentRecCase;

            IPredicateUnfolderContextPtr ctx;

            int findCounter{};
            int prevFind{};
            int *predLevelCounter{};
            int predLevel{};
            std::fstream output;

        public:
            inline explicit PredicateUnfolder(IPredicateUnfolderContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const AttributePtr& node) override;
            void visit(const CompAttributeValuePtr& node) override;

            void visit(const SymbolPtr& node) override;
            void visit(const KeywordPtr& node) override;
            void visit(const MetaSpecConstantPtr& node) override;
            void visit(const BooleanValuePtr& node) override;
            void visit(const PropLiteralPtr& node) override;

            void visit(const AssertCommandPtr& node) override;
            void visit(const CheckSatCommandPtr& node) override;
            void visit(const CheckSatAssumCommandPtr& node) override;
            void visit(const DeclareConstCommandPtr& node) override;
            void visit(const DeclareDatatypeCommandPtr& node) override;
            void visit(const DeclareDatatypesCommandPtr& node) override;
            void visit(const DeclareFunCommandPtr& node) override;
            void visit(const DeclareSortCommandPtr& node) override;
            void visit(const DefineFunCommandPtr& node) override;
            void visit(const DefineFunRecCommandPtr& node) override;
            void visit(const DefineFunsRecCommandPtr& node) override;
            void visit(const DefineSortCommandPtr& node) override;
            void visit(const EchoCommandPtr& node) override;
            void visit(const ExitCommandPtr& node) override;
            void visit(const GetAssertsCommandPtr& node) override;
            void visit(const GetAssignsCommandPtr& node) override;
            void visit(const GetInfoCommandPtr& node) override;
            void visit(const GetModelCommandPtr& node) override;
            void visit(const GetOptionCommandPtr& node) override;
            void visit(const GetProofCommandPtr& node) override;
            void visit(const GetUnsatAssumsCommandPtr& node) override;
            void visit(const GetUnsatCoreCommandPtr& node) override;
            void visit(const GetValueCommandPtr& node) override;
            void visit(const PopCommandPtr& node) override;
            void visit(const PushCommandPtr& node) override;
            void visit(const ResetCommandPtr& node) override;
            void visit(const ResetAssertsCommandPtr& node) override;
            void visit(const SetInfoCommandPtr& node) override;
            void visit(const SetLogicCommandPtr& node) override;
            void visit(const SetOptionCommandPtr& node) override;

            void visit(const FunctionDeclarationPtr& node) override;
            void visit(const FunctionDefinitionPtr& node) override;

            void visit(const SimpleIdentifierPtr& node) override;
            void visit(const QualifiedIdentifierPtr& node) override;

            void visit(const DecimalLiteralPtr& node) override;
            void visit(const NumeralLiteralPtr& node) override;
            void visit(const StringLiteralPtr& node) override;

            void visit(const LogicPtr& node) override;
            void visit(const TheoryPtr& node) override;
            void visit(const ScriptPtr& node) override;

            void visit(const SortPtr& node) override;

            void visit(const CompSExpressionPtr& node) override;

            void visit(const SortSymbolDeclarationPtr& node) override;

            void visit(const SpecConstFunDeclarationPtr& node) override;
            void visit(const MetaSpecConstFunDeclarationPtr& node) override;
            void visit(const SimpleFunDeclarationPtr& node) override;
            void visit(const ParametricFunDeclarationPtr& node) override;

            void visit(const SortDeclarationPtr& node) override;
            void visit(const SelectorDeclarationPtr& node) override;
            void visit(const ConstructorDeclarationPtr& node) override;
            void visit(const SimpleDatatypeDeclarationPtr& node) override;
            void visit(const ParametricDatatypeDeclarationPtr& node) override;

            void visit(const QualifiedConstructorPtr& node) override;
            void visit(const QualifiedPatternPtr& node) override;
            void visit(const MatchCasePtr& node) override;

            void visit(const QualifiedTermPtr& node) override;
            void visit(const LetTermPtr& node) override;
            void visit(const ForallTermPtr& node) override;
            void visit(const ExistsTermPtr& node) override;
            void visit(const MatchTermPtr& node) override;
            void visit(const AnnotatedTermPtr& node) override;

            void visit(const SortedVariablePtr& node) override;
            void visit(const VariableBindingPtr& node) override;

            NodePtr run(const NodePtr& node) {
                return wrappedVisit(0, node);
            }
        };

        typedef std::shared_ptr<PredicateUnfolder> PredicateUnfolderPtr;
    }
}

#endif //INDUCTOR_AST_PREDICATE_UNFOLDER_H
