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

void Duplicator::visit(sptr_t<Attribute> node) {
    auto newKeyword = dynamic_pointer_cast<Keyword>(wrappedVisit(node->keyword));
    auto newValue = dynamic_pointer_cast<AttributeValue>(wrappedVisit(node->value));
    ret = make_shared<Attribute>(newKeyword, newValue);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<CompAttributeValue> node) {
    auto newValues = duplicate<AttributeValue>(node->values);
    ret = make_shared<CompAttributeValue>(newValues);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<Symbol> node) {
    ret = make_shared<Symbol>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<Keyword> node) {
    ret = make_shared<Keyword>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<MetaSpecConstant> node) {
    ret = make_shared<MetaSpecConstant>(node->type);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<BooleanValue> node) {
    ret = make_shared<BooleanValue>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<PropLiteral> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    ret = make_shared<PropLiteral>(newSymbol, node->negated);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<AssertCommand> node) {
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<AssertCommand>(newTerm);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<CheckSatCommand> node) {
    ret = make_shared<CheckSatCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<CheckSatAssumCommand> node) {
    auto newAssums = duplicate<PropLiteral>(node->assumptions);
    ret = make_shared<CheckSatAssumCommand>(newAssums);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DeclareConstCommand> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<DeclareConstCommand>(newSymbol, newSort);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DeclareDatatypeCommand> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newDecl = dynamic_pointer_cast<DatatypeDeclaration>(wrappedVisit(node->declaration));
    ret = make_shared<DeclareDatatypeCommand>(newSymbol, newDecl);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DeclareDatatypesCommand> node) {
    auto newSorts = duplicate<SortDeclaration>(node->sorts);
    auto newDecls = duplicate<DatatypeDeclaration>(node->declarations);
    ret = make_shared<DeclareDatatypesCommand>(newSorts, newDecls);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DeclareFunCommand> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newParams = duplicate<Sort>(node->parameters);
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<DeclareFunCommand>(newSymbol, newParams, newSort);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DeclareSortCommand> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newArity = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->arity));
    ret = make_shared<DeclareSortCommand>(newSymbol, newArity);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DefineFunCommand> node) {
    auto newDef = dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->definition));
    ret = make_shared<DefineFunCommand>(newDef);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DefineFunRecCommand> node) {
    auto newDef = dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->definition));
    ret = make_shared<DefineFunRecCommand>(newDef);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DefineFunsRecCommand> node) {
    auto newDecls = duplicate<FunctionDeclaration>(node->declarations);
    auto newBodies = duplicate<Term>(node->bodies);
    ret = make_shared<DefineFunsRecCommand>(newDecls, newBodies);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DefineSortCommand> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newParams = duplicate<Symbol>(node->parameters);
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<DefineSortCommand>(newSymbol, newParams, newSort);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<EchoCommand> node) {
    ret = make_shared<EchoCommand>(node->message);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<ExitCommand> node) {
    ret = make_shared<ExitCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<GetAssertsCommand> node) {
    ret = make_shared<GetAssertsCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<GetAssignsCommand> node) {
    ret = make_shared<GetAssignsCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<GetInfoCommand> node) {
    auto newFlag = dynamic_pointer_cast<Keyword>(wrappedVisit(node->flag));
    ret = make_shared<GetInfoCommand>(newFlag);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<GetModelCommand> node) {
    ret = make_shared<GetModelCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<GetOptionCommand> node) {
    auto newOpt = dynamic_pointer_cast<Keyword>(wrappedVisit(node->option));
    ret = make_shared<GetOptionCommand>(newOpt);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<GetProofCommand> node) {
    ret = make_shared<GetProofCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<GetUnsatAssumsCommand> node) {
    ret = make_shared<GetUnsatAssumsCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<GetUnsatCoreCommand> node) {
    ret = make_shared<GetUnsatCoreCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<GetValueCommand> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<GetValueCommand>(newTerms);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<PopCommand> node) {
    auto newNumeral = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->numeral));
    ret = make_shared<PopCommand>(newNumeral);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<PushCommand> node) {
    auto newNumeral = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->numeral));
    ret = make_shared<PushCommand>(newNumeral);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<ResetCommand> node) {
    ret = make_shared<ResetCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<ResetAssertsCommand> node) {
    ret = make_shared<ResetAssertsCommand>();

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SetInfoCommand> node) {
    auto newAttr = dynamic_pointer_cast<Attribute>(wrappedVisit(node->info));
    ret = make_shared<SetInfoCommand>(newAttr);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SetLogicCommand> node) {
    auto newLogic = dynamic_pointer_cast<Symbol>(wrappedVisit(node->logic));
    ret = make_shared<SetLogicCommand>(newLogic);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SetOptionCommand> node) {
    auto newOpt = dynamic_pointer_cast<Attribute>(wrappedVisit(node->option));
    ret = make_shared<SetOptionCommand>(newOpt);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<FunctionDeclaration> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newParams = duplicate<SortedVariable>(node->parameters);
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<FunctionDeclaration>(newSymbol, newParams, newSort);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<FunctionDefinition> node) {
    auto newSignature = dynamic_pointer_cast<FunctionDeclaration>(wrappedVisit(node->signature));
    auto newBody = dynamic_pointer_cast<Term>(wrappedVisit(node->body));
    ret = make_shared<FunctionDefinition>(newSignature, newBody);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SimpleIdentifier> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newIndices = duplicate<Index>(node->indices);
    ret = make_shared<SimpleIdentifier>(newSymbol, newIndices);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<QualifiedIdentifier> node) {
    auto newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<QualifiedIdentifier>(newId, newSort);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<DecimalLiteral> node) {
    ret = make_shared<DecimalLiteral>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<NumeralLiteral> node) {
    ret = make_shared<NumeralLiteral>(node->value, node->base);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<StringLiteral> node) {
    ret = make_shared<StringLiteral>(node->value);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<Logic> node) {
    auto newName = dynamic_pointer_cast<Symbol>(wrappedVisit(node->name));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<Logic>(newName, newAttrs);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<Theory> node) {
    auto newName = dynamic_pointer_cast<Symbol>(wrappedVisit(node->name));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<Theory>(newName, newAttrs);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<Script> node) {
    auto newCommands = duplicate<Command>(node->commands);
    ret = make_shared<Script>(newCommands);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<Sort> node) {
    auto newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier));
    auto newArgs = duplicate<Sort>(node->arguments);
    ret = make_shared<Sort>(newId, newArgs);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<CompSExpression> node) {
    auto newExps = duplicate<SExpression>(node->expressions);

    ret = make_shared<CompSExpression>(newExps);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SortSymbolDeclaration> node) {
    auto newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier));
    auto newArity = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->arity));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<SortSymbolDeclaration>(newId, newArity, newAttrs);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SortDeclaration> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newArity = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->arity));
    ret = make_shared<SortDeclaration>(newSymbol, newArity);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SelectorDeclaration> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<SelectorDeclaration>(newSymbol, newSort);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<ConstructorDeclaration> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newSelectors = duplicate<SelectorDeclaration>(node->selectors);
    ret = make_shared<ConstructorDeclaration>(newSymbol, newSelectors);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SimpleDatatypeDeclaration> node) {
    auto newConstructors = duplicate<ConstructorDeclaration>(node->constructors);
    ret = make_shared<SimpleDatatypeDeclaration>(newConstructors);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<ParametricDatatypeDeclaration> node) {
    auto newParams = duplicate<Symbol>(node->parameters);
    auto newConstructors = duplicate<ConstructorDeclaration>(node->constructors);
    ret = make_shared<ParametricDatatypeDeclaration>(newParams, newConstructors);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<QualifiedConstructor> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<QualifiedConstructor>(newSymbol, newSort);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<QualifiedPattern> node) {
    auto newSymbols = duplicate<Symbol>(node->symbols);
    auto newCons = dynamic_pointer_cast<Constructor>(wrappedVisit(node->constructor));
    ret = make_shared<QualifiedPattern>(newCons, newSymbols);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<MatchCase> node) {
    auto newPattern = dynamic_pointer_cast<Pattern>(wrappedVisit(node->pattern));
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<MatchCase>(newPattern, newTerm);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SpecConstFunDeclaration> node) {
    auto newConstant = dynamic_pointer_cast<SpecConstant>(wrappedVisit(node->constant));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<SpecConstFunDeclaration>(newConstant, newSort, newAttrs);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<MetaSpecConstFunDeclaration> node) {
    auto newConstant = dynamic_pointer_cast<MetaSpecConstant>(wrappedVisit(node->constant));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<MetaSpecConstFunDeclaration>(newConstant, newSort, newAttrs);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SimpleFunDeclaration> node) {
    auto newIdentifier = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier));
    auto newSignature = duplicate<Sort>(node->signature);
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<SimpleFunDeclaration>(newIdentifier, newSignature, newAttrs);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<ParametricFunDeclaration> node) {
    auto newParams  = duplicate<Symbol>(node->parameters);
    auto newIdentifier = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier));
    auto newSignature = duplicate<Sort>(node->signature);
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<ParametricFunDeclaration>(newParams, newIdentifier, newSignature, newAttrs);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<QualifiedTerm> node) {
    auto newId = dynamic_pointer_cast<Identifier>(wrappedVisit(node->identifier));
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<QualifiedTerm>(newId, newTerms);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<LetTerm> node) {
    auto newBindings = duplicate<VariableBinding>(node->bindings);
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<LetTerm>(newBindings, newTerm);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<ForallTerm> node) {
    auto newBindings = duplicate<SortedVariable>(node->bindings);
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<ForallTerm>(newBindings, newTerm);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<ExistsTerm> node) {
    auto newBindings = duplicate<SortedVariable>(node->bindings);
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<ExistsTerm>(newBindings, newTerm);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}


void Duplicator::visit(sptr_t<MatchTerm> node) {
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    auto newCases = duplicate<MatchCase>(node->cases);
    ret = make_shared<MatchTerm>(newTerm, newCases);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<AnnotatedTerm> node) {
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<AnnotatedTerm>(newTerm, newAttrs);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<SortedVariable> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<SortedVariable>(newSymbol, newSort);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}

void Duplicator::visit(sptr_t<VariableBinding> node) {
    auto newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->symbol));
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<VariableBinding>(newSymbol, newTerm);

    ret->colLeft = node->colLeft;
    ret->colRight = node->colRight;
    ret->rowLeft = node->rowLeft;
    ret->rowRight = node->rowRight;
    ret->filename = node->filename;
}