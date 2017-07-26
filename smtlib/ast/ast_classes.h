#ifndef INDUCTOR_AST_CLASSES_H
#define INDUCTOR_AST_CLASSES_H

#include <memory>

namespace smtlib {
    namespace ast {
        // Declarations of all classes in the smtlib::ast hierarchy
        class Node;
        class Root;

        class Attribute;
        class AttributeValue;
        class CompAttributeValue;

        class Index;
        class SpecConstant;
        class Symbol;
        class Keyword;
        class MetaSpecConstant;
        class BooleanValue;
        class PropLiteral;

        class Logic;
        class Theory;
        class Script;

        class Command;
        class AssertCommand;
        class CheckSatCommand;
        class CheckSatAssumCommand;
        class DeclareConstCommand;
        class DeclareDatatypeCommand;
        class DeclareDatatypesCommand;
        class DeclareFunCommand;
        class DeclareSortCommand;
        class DefineFunCommand;
        class DefineFunRecCommand;
        class DefineFunsRecCommand;
        class DefineSortCommand;
        class EchoCommand;
        class ExitCommand;
        class GetAssertsCommand;
        class GetAssignsCommand;
        class GetInfoCommand;
        class GetModelCommand;
        class GetOptionCommand;
        class GetProofCommand;
        class GetUnsatAssumsCommand;
        class GetUnsatCoreCommand;
        class GetValueCommand;
        class PopCommand;
        class PushCommand;
        class ResetCommand;
        class ResetAssertsCommand;
        class SetInfoCommand;
        class SetLogicCommand;
        class SetOptionCommand;

        class SortDeclaration;
        class SelectorDeclaration;
        class ConstructorDeclaration;
        class DatatypeDeclaration;
        class SimpleDatatypeDeclaration;
        class ParametricDatatypeDeclaration;

        class FunctionDeclaration;
        class FunctionDefinition;

        class Identifier;
        class SimpleIdentifier;
        class QualifiedIdentifier;

        class DecimalLiteral;
        class NumeralLiteral;
        class StringLiteral;

        class Sort;

        class SExpression;
        class CompSExpression;

        class SortSymbolDeclaration;
        class FunSymbolDeclaration;
        class SpecConstFunDeclaration;
        class MetaSpecConstFunDeclaration;
        class SimpleFunDeclaration;
        class ParametricFunDeclaration;

        class Constructor;
        class QualifiedConstructor;
        class Pattern;
        class QualifiedPattern;
        class MatchCase;

        class Term;
        class QualifiedTerm;
        class LetTerm;
        class ForallTerm;
        class ExistsTerm;
        class MatchTerm;
        class AnnotatedTerm;

        class SortedVariable;
        class VariableBinding;

        // Typedefs for smart pointers to all the classes in the smtlib::ast hierarchy
        typedef std::shared_ptr<Node> NodePtr;
        typedef std::shared_ptr<Root> RootPtr;

        typedef std::shared_ptr<Attribute> AttributePtr;
        typedef std::shared_ptr<AttributeValue> AttributeValuePtr;
        typedef std::shared_ptr<CompAttributeValue> CompAttributeValuePtr;

        typedef std::shared_ptr<Index> IndexPtr;
        typedef std::shared_ptr<SpecConstant> SpecConstantPtr;
        typedef std::shared_ptr<Symbol> SymbolPtr;
        typedef std::shared_ptr<Keyword> KeywordPtr;
        typedef std::shared_ptr<MetaSpecConstant> MetaSpecConstantPtr;
        typedef std::shared_ptr<BooleanValue> BooleanValuePtr;
        typedef std::shared_ptr<PropLiteral> PropLiteralPtr;

        typedef std::shared_ptr<Logic> LogicPtr;
        typedef std::shared_ptr<Theory> TheoryPtr;
        typedef std::shared_ptr<Script> ScriptPtr;

        typedef std::shared_ptr<Command> CommandPtr;
        typedef std::shared_ptr<AssertCommand> AssertCommandPtr;
        typedef std::shared_ptr<CheckSatCommand> CheckSatCommandPtr;
        typedef std::shared_ptr<CheckSatAssumCommand> CheckSatAssumCommandPtr;
        typedef std::shared_ptr<DeclareConstCommand> DeclareConstCommandPtr;
        typedef std::shared_ptr<DeclareDatatypeCommand> DeclareDatatypeCommandPtr;
        typedef std::shared_ptr<DeclareDatatypesCommand> DeclareDatatypesCommandPtr;
        typedef std::shared_ptr<DeclareFunCommand> DeclareFunCommandPtr;
        typedef std::shared_ptr<DeclareSortCommand> DeclareSortCommandPtr;
        typedef std::shared_ptr<DefineFunCommand> DefineFunCommandPtr;
        typedef std::shared_ptr<DefineFunRecCommand> DefineFunRecCommandPtr;
        typedef std::shared_ptr<DefineFunsRecCommand> DefineFunsRecCommandPtr;
        typedef std::shared_ptr<DefineSortCommand> DefineSortCommandPtr;
        typedef std::shared_ptr<EchoCommand> EchoCommandPtr;
        typedef std::shared_ptr<ExitCommand> ExitCommandPtr;
        typedef std::shared_ptr<GetAssertsCommand> GetAssertsCommandPtr;
        typedef std::shared_ptr<GetAssignsCommand> GetAssignsCommandPtr;
        typedef std::shared_ptr<GetInfoCommand> GetInfoCommandPtr;
        typedef std::shared_ptr<GetModelCommand> GetModelCommandPtr;
        typedef std::shared_ptr<GetOptionCommand> GetOptionCommandPtr;
        typedef std::shared_ptr<GetProofCommand> GetProofCommandPtr;
        typedef std::shared_ptr<GetUnsatAssumsCommand> GetUnsatAssumsCommandPtr;
        typedef std::shared_ptr<GetUnsatCoreCommand> GetUnsatCoreCommandPtr;
        typedef std::shared_ptr<GetValueCommand> GetValueCommandPtr;
        typedef std::shared_ptr<PopCommand> PopCommandPtr;
        typedef std::shared_ptr<PushCommand> PushCommandPtr;
        typedef std::shared_ptr<ResetCommand> ResetCommandPtr;
        typedef std::shared_ptr<ResetAssertsCommand> ResetAssertsCommandPtr;
        typedef std::shared_ptr<SetInfoCommand> SetInfoCommandPtr;
        typedef std::shared_ptr<SetLogicCommand> SetLogicCommandPtr;
        typedef std::shared_ptr<SetOptionCommand> SetOptionCommandPtr;

        typedef std::shared_ptr<SortDeclaration> SortDeclarationPtr;
        typedef std::shared_ptr<SelectorDeclaration> SelectorDeclarationPtr;
        typedef std::shared_ptr<ConstructorDeclaration> ConstructorDeclarationPtr;
        typedef std::shared_ptr<DatatypeDeclaration> DatatypeDeclarationPtr;
        typedef std::shared_ptr<SimpleDatatypeDeclaration> SimpleDatatypeDeclarationPtr;
        typedef std::shared_ptr<ParametricDatatypeDeclaration> ParametricDatatypeDeclarationPtr;

        typedef std::shared_ptr<FunctionDeclaration> FunctionDeclarationPtr;
        typedef std::shared_ptr<FunctionDefinition> FunctionDefinitionPtr;

        typedef std::shared_ptr<Identifier> IdentifierPtr;
        typedef std::shared_ptr<SimpleIdentifier> SimpleIdentifierPtr;
        typedef std::shared_ptr<QualifiedIdentifier> QualifiedIdentifierPtr;

        typedef std::shared_ptr<DecimalLiteral> DecimalLiteralPtr;
        typedef std::shared_ptr<NumeralLiteral> NumeralLiteralPtr;
        typedef std::shared_ptr<StringLiteral> StringLiteralPtr;

        typedef std::shared_ptr<Sort> SortPtr;

        typedef std::shared_ptr<SExpression> SExpressionPtr;
        typedef std::shared_ptr<CompSExpression> CompSExpressionPtr;

        typedef std::shared_ptr<SortSymbolDeclaration> SortSymbolDeclarationPtr;
        typedef std::shared_ptr<FunSymbolDeclaration> FunSymbolDeclarationPtr;
        typedef std::shared_ptr<SpecConstFunDeclaration> SpecConstFunDeclarationPtr;
        typedef std::shared_ptr<MetaSpecConstFunDeclaration> MetaSpecConstFunDeclarationPtr;
        typedef std::shared_ptr<SimpleFunDeclaration> SimpleFunDeclarationPtr;
        typedef std::shared_ptr<ParametricFunDeclaration> ParametricFunDeclarationPtr;

        typedef std::shared_ptr<Constructor> ConstructorPtr;
        typedef std::shared_ptr<QualifiedConstructor> QualifiedConstructorPtr;
        typedef std::shared_ptr<Pattern> PatternPtr;
        typedef std::shared_ptr<QualifiedPattern> QualifiedPatternPtr;
        typedef std::shared_ptr<MatchCase> MatchCasePtr;

        typedef std::shared_ptr<Term> TermPtr;
        typedef std::shared_ptr<QualifiedTerm> QualifiedTermPtr;
        typedef std::shared_ptr<LetTerm> LetTermPtr;
        typedef std::shared_ptr<ForallTerm> ForallTermPtr;
        typedef std::shared_ptr<ExistsTerm> ExistsTermPtr;
        typedef std::shared_ptr<MatchTerm> MatchTermPtr;
        typedef std::shared_ptr<AnnotatedTerm> AnnotatedTermPtr;

        typedef std::shared_ptr<SortedVariable> SortedVariablePtr;
        typedef std::shared_ptr<VariableBinding> VariableBindingPtr;
    }
}

#endif //INDUCTOR_AST_CLASSES_H
