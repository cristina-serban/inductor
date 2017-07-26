#include "visitor/sep_duplicator.h"

#include "sep/sep_attribute.h"
#include "sep/sep_command.h"
#include "sep/sep_logic.h"
#include "sep/sep_script.h"
#include "sep/sep_s_expr.h"
#include "sep/sep_term.h"
#include "sep/sep_theory.h"

using namespace std;
using namespace smtlib::sep;


void Duplicator::visit(sptr_t<SimpleAttribute> node) {
    ret = make_shared<SimpleAttribute>(node->keyword);
}

void Duplicator::visit(sptr_t<SExpressionAttribute> node) {
    auto newValue = dynamic_pointer_cast<SExpression>(wrappedVisit(node->value));
    ret = make_shared<SExpressionAttribute>(node->keyword, newValue);
}

void Duplicator::visit(sptr_t<SymbolAttribute> node) {
    ret = make_shared<SymbolAttribute>(node->keyword, node->value);
}

void Duplicator::visit(sptr_t<BooleanAttribute> node) {
    ret = make_shared<BooleanAttribute>(node->keyword, node->value);
}

void Duplicator::visit(sptr_t<NumeralAttribute> node) {
    auto newValue = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->value));
    ret = make_shared<NumeralAttribute>(node->keyword, newValue);
}

void Duplicator::visit(sptr_t<DecimalAttribute> node) {
    auto newValue = dynamic_pointer_cast<DecimalLiteral>(wrappedVisit(node->value));
    ret = make_shared<DecimalAttribute>(node->keyword, newValue);
}

void Duplicator::visit(sptr_t<StringAttribute> node) {
    auto newValue = dynamic_pointer_cast<StringLiteral>(wrappedVisit(node->value));
    ret = make_shared<StringAttribute>(node->keyword, newValue);
}

void Duplicator::visit(sptr_t<TheoriesAttribute> node) {
    ret = make_shared<TheoriesAttribute>(node->theories);
}

void Duplicator::visit(sptr_t<SortsAttribute> node) {
    auto newSorts = duplicate<SortSymbolDeclaration>(node->declarations);
    ret = make_shared<SortsAttribute>(newSorts);
}

void Duplicator::visit(sptr_t<FunsAttribute> node) {
    auto newFuns = duplicate<FunSymbolDeclaration>(node->declarations);
    ret = make_shared<FunsAttribute>(newFuns);
}

void Duplicator::visit(sptr_t<Symbol> node) {
    ret = make_shared<Symbol>(node->value);
}

void Duplicator::visit(sptr_t<Keyword> node) {
    ret = make_shared<Keyword>(node->value);
}

void Duplicator::visit(sptr_t<MetaSpecConstant> node) {
    ret = make_shared<MetaSpecConstant>(node->type);
}

void Duplicator::visit(sptr_t<BooleanValue> node) {
    ret = make_shared<BooleanValue>(node->value);
}

void Duplicator::visit(sptr_t<PropLiteral> node) {
    ret = make_shared<PropLiteral>(node->value, node->negated);
}

void Duplicator::visit(sptr_t<AssertCommand> node) {
    ret = make_shared<AssertCommand>(dynamic_pointer_cast<Term>(wrappedVisit(node->term)));
}

void Duplicator::visit(sptr_t<CheckSatCommand> node) {
    ret = make_shared<CheckSatCommand>();
}

void Duplicator::visit(sptr_t<CheckSatAssumCommand> node) {
    auto newAssums = duplicate<PropLiteral>(node->assumptions);
    ret = make_shared<CheckSatAssumCommand>(newAssums);
}

void Duplicator::visit(sptr_t<DeclareConstCommand> node) {
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<DeclareConstCommand>(node->name, newSort);
}

void Duplicator::visit(sptr_t<DeclareDatatypeCommand> node) {
    auto newDecl = dynamic_pointer_cast<DatatypeDeclaration>(wrappedVisit(node->declaration));
    ret = make_shared<DeclareDatatypeCommand>(node->name, newDecl);
}

void Duplicator::visit(sptr_t<DeclareDatatypesCommand> node) {
    auto newSorts = duplicate<SortDeclaration>(node->sorts);
    auto newDecls = duplicate<DatatypeDeclaration>(node->declarations);
    ret = make_shared<DeclareDatatypesCommand>(newSorts, newDecls);
}

void Duplicator::visit(sptr_t<DeclareFunCommand> node) {
    auto newParams = duplicate<Sort>(node->params);
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<DeclareFunCommand>(node->name, newParams, newSort);
}

void Duplicator::visit(sptr_t<DeclareSortCommand> node) {
    ret = make_shared<DeclareSortCommand>(node->name, node->arity);
}

void Duplicator::visit(sptr_t<DefineFunCommand> node) {
    auto newDef = dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->definition));
    ret = make_shared<DefineFunCommand>(newDef);
}

void Duplicator::visit(sptr_t<DefineFunRecCommand> node) {
    auto newDef = dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->definition));
    ret = make_shared<DefineFunRecCommand>(newDef);
}

void Duplicator::visit(sptr_t<DefineFunsRecCommand> node) {
    auto newDecls = duplicate<FunctionDeclaration>(node->declarations);
    auto newBodies = duplicate<Term>(node->bodies);
    ret = make_shared<DefineFunsRecCommand>(newDecls, newBodies);
}

void Duplicator::visit(sptr_t<DefineSortCommand> node) {
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<DefineSortCommand>(node->name, node->params, newSort);
}

void Duplicator::visit(sptr_t<EchoCommand> node) {
    ret = make_shared<EchoCommand>(node->message);
}

void Duplicator::visit(sptr_t<ExitCommand> node) {
    ret = make_shared<ExitCommand>();
}

void Duplicator::visit(sptr_t<GetAssertsCommand> node) {
    ret = make_shared<GetAssertsCommand>();
}

void Duplicator::visit(sptr_t<GetAssignsCommand> node) {
    ret = make_shared<GetAssignsCommand>();
}

void Duplicator::visit(sptr_t<GetInfoCommand> node) {
    ret = make_shared<GetInfoCommand>(node->flag);
}

void Duplicator::visit(sptr_t<GetModelCommand> node) {
    ret = make_shared<GetModelCommand>();
}

void Duplicator::visit(sptr_t<GetOptionCommand> node) {
    ret = make_shared<GetInfoCommand>(node->option);
}

void Duplicator::visit(sptr_t<GetProofCommand> node) {
    ret = make_shared<GetProofCommand>();
}

void Duplicator::visit(sptr_t<GetUnsatAssumsCommand> node) {
    ret = make_shared<GetUnsatAssumsCommand>();
}

void Duplicator::visit(sptr_t<GetUnsatCoreCommand> node) {
    ret = make_shared<GetUnsatCoreCommand>();
}

void Duplicator::visit(sptr_t<GetValueCommand> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<GetValueCommand>(newTerms);
}

void Duplicator::visit(sptr_t<PopCommand> node) {
    ret = make_shared<PopCommand>(node->levelCount);
}

void Duplicator::visit(sptr_t<PushCommand> node) {
    ret = make_shared<PushCommand>(node->levelCount);
}

void Duplicator::visit(sptr_t<ResetCommand> node) {
    ret = make_shared<ResetCommand>();
}

void Duplicator::visit(sptr_t<ResetAssertsCommand> node) {
    ret = make_shared<ResetAssertsCommand>();
}

void Duplicator::visit(sptr_t<SetInfoCommand> node) {
    ret = make_shared<SetInfoCommand>(
        dynamic_pointer_cast<Attribute>(wrappedVisit(node->info)));
}

void Duplicator::visit(sptr_t<SetLogicCommand> node) {
    ret = make_shared<SetLogicCommand>(node->logic);
}

void Duplicator::visit(sptr_t<SetOptionCommand> node) {
    auto newAttr = dynamic_pointer_cast<Attribute>(wrappedVisit(node->option));
    ret = make_shared<SetOptionCommand>(newAttr);
}

void Duplicator::visit(sptr_t<SortDeclaration> node) {
    ret = make_shared<SortDeclaration>(node->name, node->arity);
}

void Duplicator::visit(sptr_t<SelectorDeclaration> node) {
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<SelectorDeclaration>(node->name, newSort);
}

void Duplicator::visit(sptr_t<ConstructorDeclaration> node) {
    auto newSels = duplicate<SelectorDeclaration>(node->selectors);
    ret = make_shared<ConstructorDeclaration>(node->name, newSels);
}

void Duplicator::visit(sptr_t<SimpleDatatypeDeclaration> node) {
    auto newCons = duplicate<ConstructorDeclaration>(node->constructors);
    ret = make_shared<SimpleDatatypeDeclaration>(newCons);
}

void Duplicator::visit(sptr_t<ParametricDatatypeDeclaration> node) {
    auto newCons = duplicate<ConstructorDeclaration>(node->constructors);
    ret = make_shared<ParametricDatatypeDeclaration>(node->params, newCons);
}

void Duplicator::visit(sptr_t<FunctionDeclaration> node) {
    auto newParams = duplicate<SortedVariable>(node->params);
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<FunctionDeclaration>(node->name, newParams, newSort);
}

void Duplicator::visit(sptr_t<FunctionDefinition> node) {
    auto newSignature = dynamic_pointer_cast<FunctionDeclaration>(wrappedVisit(node->signature));
    auto newBody = dynamic_pointer_cast<Term>(wrappedVisit(node->body));
    ret = make_shared<FunctionDefinition>(newSignature, newBody);
}

void Duplicator::visit(sptr_t<SimpleIdentifier> node) {
    auto newIndices = duplicate<Index>(node->indices);
    ret = make_shared<SimpleIdentifier>(node->name, newIndices);
}

void Duplicator::visit(sptr_t<QualifiedIdentifier> node) {
    auto newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<QualifiedIdentifier>(newId, newSort);
}

void Duplicator::visit(sptr_t<NumeralLiteral> node) {
    ret = make_shared<NumeralLiteral>(node->value, node->base);
}

void Duplicator::visit(sptr_t<DecimalLiteral> node) {
    ret = make_shared<DecimalLiteral>(node->value);
}

void Duplicator::visit(sptr_t<StringLiteral> node) {
    ret = make_shared<StringLiteral>(node->value);
}

void Duplicator::visit(sptr_t<Logic> node) {
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<Logic>(node->name, newAttrs);
}

void Duplicator::visit(sptr_t<Theory> node) {
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<Theory>(node->name, newAttrs);
}

void Duplicator::visit(sptr_t<Script> node) {
    auto newCmds = duplicate<Command>(node->commands);
    ret = make_shared<Script>(newCmds);
}

void Duplicator::visit(sptr_t<QualifiedConstructor> node) {
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<QualifiedConstructor>(node->name, newSort);
}

void Duplicator::visit(sptr_t<QualifiedPattern> node) {
    auto newCons = dynamic_pointer_cast<Constructor>(wrappedVisit(node->constructor));
    ret = make_shared<QualifiedPattern>(newCons, node->args);
}

void Duplicator::visit(sptr_t<MatchCase> node) {
    auto newPattern = dynamic_pointer_cast<Pattern>(wrappedVisit(node->pattern));
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<MatchCase>(newPattern, newTerm);
}

void Duplicator::visit(sptr_t<CompSExpression> node) {
    auto newExps = duplicate<SExpression>(node->exprs);
    ret = make_shared<CompSExpression>(newExps);
}

void Duplicator::visit(sptr_t<Sort> node) {
    auto newArgs = duplicate<Sort>(node->args);
    ret = make_shared<Sort>(node->name, newArgs);
}

void Duplicator::visit(sptr_t<SortSymbolDeclaration> node) {
    auto newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<SortSymbolDeclaration>(newId, node->arity, newAttrs);
}

void Duplicator::visit(sptr_t<SpecConstFunDeclaration> node) {
    auto newConst = dynamic_pointer_cast<SpecConstant>(wrappedVisit(node->constant));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<SpecConstFunDeclaration>(newConst, newSort, newAttrs);
}

void Duplicator::visit(sptr_t<MetaSpecConstFunDeclaration> node) {
    auto newConst = dynamic_pointer_cast<MetaSpecConstant>(wrappedVisit(node->constant));
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<MetaSpecConstFunDeclaration>(newConst, newSort, newAttrs);
}

void Duplicator::visit(sptr_t<SimpleFunDeclaration> node) {
    auto newParams = duplicate<Sort>(node->signature);
    auto newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier));
    auto newSignature = duplicate<Sort>(node->signature);
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<SimpleFunDeclaration>(newId, newSignature, newAttrs);
}

void Duplicator::visit(sptr_t<ParametricFunDeclaration> node) {
    auto newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier));
    auto newSignature = duplicate<Sort>(node->signature);
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<ParametricFunDeclaration>(node->params, newId, newSignature, newAttrs);
}

void Duplicator::visit(sptr_t<QualifiedTerm> node) {
    auto newId = dynamic_pointer_cast<Identifier>(wrappedVisit(node->identifier));
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<QualifiedTerm>(newId, newTerms);
}

void Duplicator::visit(sptr_t<LetTerm> node) {
    auto newBindings = duplicate<VariableBinding>(node->bindings);
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<LetTerm>(newBindings, newTerm);
}

void Duplicator::visit(sptr_t<ForallTerm> node) {
    auto newBindings = duplicate<SortedVariable>(node->bindings);
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<ForallTerm>(newBindings, newTerm);
}

void Duplicator::visit(sptr_t<ExistsTerm> node) {
    auto newBindings = duplicate<SortedVariable>(node->bindings);
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<ExistsTerm>(newBindings, newTerm);
}

void Duplicator::visit(sptr_t<MatchTerm> node) {
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    auto newCases = duplicate<MatchCase>(node->cases);
    ret = make_shared<MatchTerm>(newTerm, newCases);
}

void Duplicator::visit(sptr_t<AnnotatedTerm> node) {
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    auto newAttrs = duplicate<Attribute>(node->attributes);
    ret = make_shared<AnnotatedTerm>(newTerm, newAttrs);
}

void Duplicator::visit(sptr_t<TrueTerm> node) {
    ret = make_shared<TrueTerm>();
}

void Duplicator::visit(sptr_t<FalseTerm> node) {
    ret = make_shared<FalseTerm>();
}

void Duplicator::visit(sptr_t<NotTerm> node) {
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<NotTerm>(newTerm);
}

void Duplicator::visit(sptr_t<ImpliesTerm> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<ImpliesTerm>(newTerms);
}

void Duplicator::visit(sptr_t<AndTerm> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<AndTerm>(newTerms);
}

void Duplicator::visit(sptr_t<OrTerm> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<OrTerm>(newTerms);
}

void Duplicator::visit(sptr_t<XorTerm> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<XorTerm>(newTerms);
}

void Duplicator::visit(sptr_t<EqualsTerm> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<EqualsTerm>(newTerms);
}

void Duplicator::visit(sptr_t<DistinctTerm> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<DistinctTerm>(newTerms);
}

void Duplicator::visit(sptr_t<IteTerm> node) {
    auto newTest = dynamic_pointer_cast<Term>(wrappedVisit(node->testTerm));
    auto newThen = dynamic_pointer_cast<Term>(wrappedVisit(node->thenTerm));
    auto newElse = dynamic_pointer_cast<Term>(wrappedVisit(node->elseTerm));
    ret = make_shared<IteTerm>(newTest, newThen, newElse);
}

void Duplicator::visit(sptr_t<EmpTerm> node) {
    ret = make_shared<EmpTerm>();
}

void Duplicator::visit(sptr_t<SepTerm> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<SepTerm>(newTerms);
}

void Duplicator::visit(sptr_t<WandTerm> node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<WandTerm>(newTerms);
}

void Duplicator::visit(sptr_t<PtoTerm> node) {
    auto newLeft = dynamic_pointer_cast<Term>(wrappedVisit(node->leftTerm));
    auto newRight = dynamic_pointer_cast<Term>(wrappedVisit(node->rightTerm));
    ret = make_shared<PtoTerm>(newLeft, newRight);
}

void Duplicator::visit(sptr_t<NilTerm> node) {
    if (node->sort) {
        auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
        ret = make_shared<NilTerm>(newSort);
    } else {
        ret = make_shared<NilTerm>();
    }
}

void Duplicator::visit(sptr_t<SortedVariable> node) {
    auto newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->sort));
    ret = make_shared<SortedVariable>(node->name, newSort);
}

void Duplicator::visit(sptr_t<VariableBinding> node) {
    auto newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->term));
    ret = make_shared<VariableBinding>(node->name, newTerm);
}