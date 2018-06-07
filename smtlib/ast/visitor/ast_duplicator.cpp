#include "ast_duplicator.h"

#include "ast/ast_datatype.h"
#include "ast/ast_logic.h"
#include "ast/ast_s_expr.h"
#include "ast/ast_script.h"
#include "ast/ast_symbol_decl.h"
#include "ast/ast_term.h"
#include "ast/ast_theory.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

void Duplicator::visit(const AttributePtr& node) {
    ret = make_shared<Attribute>(
            std::move(dynamic_pointer_cast<Keyword>(wrappedVisit(node->keyword))),
            std::move(dynamic_pointer_cast<AttributeValue>(wrappedVisit(node->value))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const CompAttributeValuePtr& node) {
    ret = make_shared<CompAttributeValue>(std::move(duplicate<AttributeValue>(node->values)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SymbolPtr& node) {
    ret = make_shared<Symbol>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const KeywordPtr& node) {
    ret = make_shared<Keyword>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const MetaSpecConstantPtr& node) {
    ret = make_shared<MetaSpecConstant>(node->type);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const BooleanValuePtr& node) {
    ret = make_shared<BooleanValue>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const PropLiteralPtr& node) {
    ret = make_shared<PropLiteral>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            node->negated);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const AssertCommandPtr& node) {
    ret = make_shared<AssertCommand>(
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const CheckSatCommandPtr& node) {
    ret = make_shared<CheckSatCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const CheckSatAssumCommandPtr& node) {
    ret = make_shared<CheckSatAssumCommand>(std::move(duplicate<PropLiteral>(node->assumptions)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DeclareConstCommandPtr& node) {
    ret = make_shared<DeclareConstCommand>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DeclareDatatypeCommandPtr& node) {
    ret = make_shared<DeclareDatatypeCommand>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(dynamic_pointer_cast<DatatypeDeclaration>(wrappedVisit(node->declaration))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DeclareDatatypesCommandPtr& node) {
    ret = make_shared<DeclareDatatypesCommand>(
            std::move(duplicate<SortDeclaration>(node->sorts)),
            std::move(duplicate<DatatypeDeclaration>(node->declarations)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DeclareFunCommandPtr& node) {
    ret = make_shared<DeclareFunCommand>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(duplicate<Sort>(node->parameters)),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DeclareSortCommandPtr& node) {
    ret = make_shared<DeclareSortCommand>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->arity))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DefineFunCommandPtr& node) {
    ret = make_shared<DefineFunCommand>(
            std::move(dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->definition))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DefineFunRecCommandPtr& node) {
    ret = make_shared<DefineFunRecCommand>(
            std::move(dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->definition))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DefineFunsRecCommandPtr& node) {
    ret = make_shared<DefineFunsRecCommand>(
            std::move(duplicate<FunctionDeclaration>(node->declarations)),
            std::move(duplicate<Term>(node->bodies)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DefineSortCommandPtr& node) {
    ret = make_shared<DefineSortCommand>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(duplicate<Symbol>(node->parameters)),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const EchoCommandPtr& node) {
    ret = make_shared<EchoCommand>(node->message);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const ExitCommandPtr& node) {
    ret = make_shared<ExitCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const GetAssertsCommandPtr& node) {
    ret = make_shared<GetAssertsCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const GetAssignsCommandPtr& node) {
    ret = make_shared<GetAssignsCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const GetInfoCommandPtr& node) {
    ret = make_shared<GetInfoCommand>(
            std::move(dynamic_pointer_cast<Keyword>(wrappedVisit(node->flag))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const GetModelCommandPtr& node) {
    ret = make_shared<GetModelCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const GetOptionCommandPtr& node) {
    ret = make_shared<GetOptionCommand>(
            std::move(dynamic_pointer_cast<Keyword>(wrappedVisit(node->option))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const GetProofCommandPtr& node) {
    ret = make_shared<GetProofCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const GetUnsatAssumsCommandPtr& node) {
    ret = make_shared<GetUnsatAssumsCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const GetUnsatCoreCommandPtr& node) {
    ret = make_shared<GetUnsatCoreCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const GetValueCommandPtr& node) {
    ret = make_shared<GetValueCommand>(std::move(duplicate<Term>(node->terms)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const PopCommandPtr& node) {
    ret = make_shared<PopCommand>(
            std::move(dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->numeral))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const PushCommandPtr& node) {
    ret = make_shared<PushCommand>(
            std::move(dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->numeral))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const ResetCommandPtr& node) {
    ret = make_shared<ResetCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const ResetAssertsCommandPtr& node) {
    ret = make_shared<ResetAssertsCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SetInfoCommandPtr& node) {
    ret = make_shared<SetInfoCommand>(
            std::move(dynamic_pointer_cast<Attribute>(wrappedVisit(node->info))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SetLogicCommandPtr& node) {
    auto newLogic = dynamic_pointer_cast<Symbol>(wrappedVisit(node->logic));
    ret = make_shared<SetLogicCommand>(std::move(newLogic));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SetOptionCommandPtr& node) {
    ret = make_shared<SetOptionCommand>(
            std::move(dynamic_pointer_cast<Attribute>(wrappedVisit(node->option))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const FunctionDeclarationPtr& node) {
    ret = make_shared<FunctionDeclaration>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(duplicate<SortedVariable>(node->parameters)),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const FunctionDefinitionPtr& node) {
    ret = make_shared<FunctionDefinition>(
            std::move(dynamic_pointer_cast<FunctionDeclaration>(wrappedVisit(node->signature))),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->body))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SimpleIdentifierPtr& node) {
    ret = make_shared<SimpleIdentifier>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(duplicate<Index>(node->indices)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const QualifiedIdentifierPtr& node) {
    ret = make_shared<QualifiedIdentifier>(
            std::move(dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const DecimalLiteralPtr& node) {
    ret = make_shared<DecimalLiteral>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const NumeralLiteralPtr& node) {
    ret = make_shared<NumeralLiteral>(node->value, node->base);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const StringLiteralPtr& node) {
    ret = make_shared<StringLiteral>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const LogicPtr& node) {
    ret = make_shared<Logic>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->name))),
            std::move(duplicate<Attribute>(node->attributes)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const TheoryPtr& node) {
    ret = make_shared<Theory>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->name))),
            std::move(duplicate<Attribute>(node->attributes)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const ScriptPtr& node) {
    ret = make_shared<Script>(std::move(duplicate<Command>(node->commands)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SortPtr& node) {
    ret = make_shared<Sort>(
            std::move(dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier))),
            std::move(duplicate<Sort>(node->arguments)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const CompSExpressionPtr& node) {
    ret = make_shared<CompSExpression>(std::move(duplicate<SExpression>(node->expressions)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SortSymbolDeclarationPtr& node) {
    ret = make_shared<SortSymbolDeclaration>(
            std::move(dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier))),
            std::move(dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->arity))),
            std::move(duplicate<Attribute>(node->attributes)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SortDeclarationPtr& node) {
    ret = make_shared<SortDeclaration>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->arity))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SelectorDeclarationPtr& node) {
    ret = make_shared<SelectorDeclaration>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const ConstructorDeclarationPtr& node) {
    ret = make_shared<ConstructorDeclaration>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(duplicate<SelectorDeclaration>(node->selectors)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SimpleDatatypeDeclarationPtr& node) {
    ret = make_shared<SimpleDatatypeDeclaration>(
            duplicate<ConstructorDeclaration>(node->constructors));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const ParametricDatatypeDeclarationPtr& node) {
    ret = make_shared<ParametricDatatypeDeclaration>(
            std::move(duplicate<Symbol>(node->parameters)),
            std::move(duplicate<ConstructorDeclaration>(node->constructors)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const QualifiedConstructorPtr& node) {
    ret = make_shared<QualifiedConstructor>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const QualifiedPatternPtr& node) {
    ret = make_shared<QualifiedPattern>(
            std::move(dynamic_pointer_cast<Constructor>(wrappedVisit(node->constructor))),
            std::move(duplicate<Symbol>(node->symbols)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const MatchCasePtr& node) {
    ret = make_shared<MatchCase>(
            std::move(dynamic_pointer_cast<Pattern>(wrappedVisit(node->pattern))),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SpecConstFunDeclarationPtr& node) {
    ret = make_shared<SpecConstFunDeclaration>(
            std::move(dynamic_pointer_cast<SpecConstant>(wrappedVisit(node->constant))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))),
            std::move(duplicate<Attribute>(node->attributes)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const MetaSpecConstFunDeclarationPtr& node) {
    ret = make_shared<MetaSpecConstFunDeclaration>(
            std::move(dynamic_pointer_cast<MetaSpecConstant>(wrappedVisit(node->constant))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))),
            std::move(duplicate<Attribute>(node->attributes)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SimpleFunDeclarationPtr& node) {
    ret = make_shared<SimpleFunDeclaration>(
            std::move(dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier))),
            std::move(duplicate<Sort>(node->signature)),
            std::move(duplicate<Attribute>(node->attributes)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const ParametricFunDeclarationPtr& node) {
    ret = make_shared<ParametricFunDeclaration>(
            std::move(duplicate<Symbol>(node->parameters)),
            std::move(dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier))),
            std::move(duplicate<Sort>(node->signature)),
            std::move(duplicate<Attribute>(node->attributes)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const QualifiedTermPtr& node) {
    ret = make_shared<QualifiedTerm>(
            std::move(dynamic_pointer_cast<Identifier>(wrappedVisit(node->identifier))),
            std::move(duplicate<Term>(node->terms)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const LetTermPtr& node) {
    ret = make_shared<LetTerm>(
            std::move(duplicate<VariableBinding>(node->bindings)),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const ForallTermPtr& node) {
    ret = make_shared<ForallTerm>(
            std::move(duplicate<SortedVariable>(node->bindings)),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const ExistsTermPtr& node) {
    ret = make_shared<ExistsTerm>(
            std::move(duplicate<SortedVariable>(node->bindings)),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}


void Duplicator::visit(const MatchTermPtr& node) {
    ret = make_shared<MatchTerm>(
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))),
            std::move(duplicate<MatchCase>(node->cases)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const AnnotatedTermPtr& node) {
    ret = make_shared<AnnotatedTerm>(
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))),
            std::move(duplicate<Attribute>(node->attributes)));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const SortedVariablePtr& node) {
    ret = make_shared<SortedVariable>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(const VariableBindingPtr& node) {
    ret = make_shared<VariableBinding>(
            std::move(dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol))),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}
