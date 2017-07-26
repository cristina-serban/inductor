#ifndef INDUCTOR_SEP_CLASSES_H
#define INDUCTOR_SEP_CLASSES_H

namespace smtlib {
    namespace sep {
        class Node;
        class Root;

        class Attribute;
        class SimpleAttribute;
        class SExpressionAttribute;
        class SymbolAttribute;
        class BooleanAttribute;
        class NumeralAttribute;
        class DecimalAttribute;
        class StringAttribute;
        class TheoriesAttribute;
        class SortsAttribute;
        class FunsAttribute;

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

        class SimpleIdentifier;
        class QualifiedIdentifier;

        class NumeralLiteral;
        class DecimalLiteral;
        class StringLiteral;

        class Sort;

        class CompSExpression;

        class SortSymbolDeclaration;
        class FunSymbolDeclaration;
        class SpecConstFunDeclaration;
        class MetaSpecConstFunDeclaration;
        class SimpleFunDeclaration;
        class ParametricFunDeclaration;

        class QualifiedConstructor;
        class QualifiedPattern;
        class MatchCase;

        class QualifiedTerm;
        class LetTerm;
        class ForallTerm;
        class ExistsTerm;
        class MatchTerm;
        class AnnotatedTerm;

        class TrueTerm;
        class FalseTerm;
        class NotTerm;
        class ImpliesTerm;
        class AndTerm;
        class OrTerm;
        class XorTerm;
        class EqualsTerm;
        class DistinctTerm;
        class IteTerm;

        class EmpTerm;
        class SepTerm;
        class WandTerm;
        class PtoTerm;
        class NilTerm;

        class SortedVariable;
        class VariableBinding;
    }
}

#endif //INDUCTOR_SEP_CLASSES_H
