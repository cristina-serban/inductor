#include "smtlib-glue.h"

#include "ast/ast_attribute.h"
#include "ast/ast_basic.h"
#include "ast/ast_command.h"
#include "ast/ast_datatype.h"
#include "ast/ast_fun.h"
#include "ast/ast_identifier.h"
#include "ast/ast_interfaces.h"
#include "ast/ast_literal.h"
#include "ast/ast_logic.h"
#include "ast/ast_match.h"
#include "ast/ast_s_expr.h"
#include "ast/ast_script.h"
#include "ast/ast_sort.h"
#include "ast/ast_symbol_decl.h"
#include "ast/ast_term.h"
#include "ast/ast_theory.h"
#include "ast/ast_variable.h"
#include "parser/smtlib_parser.h"
#include "util/global_typedef.h"

#include <iostream>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

unordered_map<smtlib::ast::Node*, smtlib::ast::NodePtr> smtlib_nodemap;

template<class T>
shared_ptr<T> share(AstPtr nakedPtr) {
    return dynamic_pointer_cast<T>(smtlib_nodemap[nakedPtr]);
}

template<>
SpecConstantPtr share(AstPtr nakedPtr) {
    NumeralLiteralPtr option1 = dynamic_pointer_cast<NumeralLiteral>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    DecimalLiteralPtr option2 = dynamic_pointer_cast<DecimalLiteral>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    StringLiteralPtr option3 = dynamic_pointer_cast<StringLiteral>(smtlib_nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    throw;
}

template<>
CommandPtr share(AstPtr nakedPtr) {
    AssertCommandPtr option1 = dynamic_pointer_cast<AssertCommand>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    CheckSatCommandPtr option2 = dynamic_pointer_cast<CheckSatCommand>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    CheckSatAssumCommandPtr option3 = dynamic_pointer_cast<CheckSatAssumCommand>(smtlib_nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    DeclareConstCommandPtr option4 = dynamic_pointer_cast<DeclareConstCommand>(smtlib_nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    DeclareFunCommandPtr option5 = dynamic_pointer_cast<DeclareFunCommand>(smtlib_nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    DeclareSortCommandPtr option6 = dynamic_pointer_cast<DeclareSortCommand>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    DefineFunCommandPtr option7 = dynamic_pointer_cast<DefineFunCommand>(smtlib_nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    DefineFunRecCommandPtr option8 = dynamic_pointer_cast<DefineFunRecCommand>(smtlib_nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    DefineFunsRecCommandPtr option9 = dynamic_pointer_cast<DefineFunsRecCommand>(smtlib_nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    DefineSortCommandPtr option10 = dynamic_pointer_cast<DefineSortCommand>(smtlib_nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    EchoCommandPtr option11 = dynamic_pointer_cast<EchoCommand>(smtlib_nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    ExitCommandPtr option12 = dynamic_pointer_cast<ExitCommand>(smtlib_nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }

    SetOptionCommandPtr option13 = dynamic_pointer_cast<SetOptionCommand>(smtlib_nodemap[nakedPtr]);
    if (option13) {
        return option13->shared_from_this();
    }

    GetAssertsCommandPtr option14 = dynamic_pointer_cast<GetAssertsCommand>(smtlib_nodemap[nakedPtr]);
    if (option14) {
        return option14->shared_from_this();
    }

    GetAssignsCommandPtr option15 = dynamic_pointer_cast<GetAssignsCommand>(smtlib_nodemap[nakedPtr]);
    if (option15) {
        return option15->shared_from_this();
    }

    GetInfoCommandPtr option16 = dynamic_pointer_cast<GetInfoCommand>(smtlib_nodemap[nakedPtr]);
    if (option16) {
        return option16->shared_from_this();
    }

    GetModelCommandPtr option17 = dynamic_pointer_cast<GetModelCommand>(smtlib_nodemap[nakedPtr]);
    if (option17) {
        return option17->shared_from_this();
    }

    GetOptionCommandPtr option18 = dynamic_pointer_cast<GetOptionCommand>(smtlib_nodemap[nakedPtr]);
    if (option18) {
        return option18->shared_from_this();
    }

    GetProofCommandPtr option19 = dynamic_pointer_cast<GetProofCommand>(smtlib_nodemap[nakedPtr]);
    if (option19) {
        return option19->shared_from_this();
    }

    GetUnsatAssumsCommandPtr option20 = dynamic_pointer_cast<GetUnsatAssumsCommand>(smtlib_nodemap[nakedPtr]);
    if (option20) {
        return option20->shared_from_this();
    }

    GetUnsatCoreCommandPtr option21 = dynamic_pointer_cast<GetUnsatCoreCommand>(smtlib_nodemap[nakedPtr]);
    if (option21) {
        return option21->shared_from_this();
    }

    GetValueCommandPtr option22 = dynamic_pointer_cast<GetValueCommand>(smtlib_nodemap[nakedPtr]);
    if (option22) {
        return option22->shared_from_this();
    }

    PopCommandPtr option23 = dynamic_pointer_cast<PopCommand>(smtlib_nodemap[nakedPtr]);
    if (option23) {
        return option23->shared_from_this();
    }

    PushCommandPtr option24 = dynamic_pointer_cast<PushCommand>(smtlib_nodemap[nakedPtr]);
    if (option24) {
        return option24->shared_from_this();
    }

    ResetCommandPtr option25 = dynamic_pointer_cast<ResetCommand>(smtlib_nodemap[nakedPtr]);
    if (option25) {
        return option25->shared_from_this();
    }

    ResetAssertsCommandPtr option26 = dynamic_pointer_cast<ResetAssertsCommand>(smtlib_nodemap[nakedPtr]);
    if (option26) {
        return option26->shared_from_this();
    }

    SetInfoCommandPtr option27 = dynamic_pointer_cast<SetInfoCommand>(smtlib_nodemap[nakedPtr]);
    if (option27) {
        return option27->shared_from_this();
    }

    SetLogicCommandPtr option28 = dynamic_pointer_cast<SetLogicCommand>(smtlib_nodemap[nakedPtr]);
    if (option28) {
        return option28->shared_from_this();
    }

    DeclareDatatypeCommandPtr option29 = dynamic_pointer_cast<DeclareDatatypeCommand>(smtlib_nodemap[nakedPtr]);
    if (option29) {
        return option29->shared_from_this();
    }

    DeclareDatatypesCommandPtr option30 = dynamic_pointer_cast<DeclareDatatypesCommand>(smtlib_nodemap[nakedPtr]);
    if (option30) {
        return option30->shared_from_this();
    }

    throw;
}

template<>
FunSymbolDeclarationPtr share(AstPtr nakedPtr) {
    SpecConstFunDeclarationPtr option6 = dynamic_pointer_cast<SpecConstFunDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    MetaSpecConstFunDeclarationPtr option7 = dynamic_pointer_cast<MetaSpecConstFunDeclaration>(
            smtlib_nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    SimpleFunDeclarationPtr option8 = dynamic_pointer_cast<SimpleFunDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    ParametricFunDeclarationPtr option9 = dynamic_pointer_cast<ParametricFunDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    throw;
}

template<>
ConstructorPtr share(AstPtr nakedPtr) {
    SymbolPtr option1 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    QualifiedConstructorPtr option2 = dynamic_pointer_cast<QualifiedConstructor>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
PatternPtr share(AstPtr nakedPtr) {
    if (dynamic_cast<Constructor*>(nakedPtr)) {
        return share<Constructor>(nakedPtr);
    }

    SymbolPtr option1 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    QualifiedPatternPtr option2 = dynamic_pointer_cast<QualifiedPattern>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
DatatypeDeclarationPtr share(AstPtr nakedPtr) {
    SimpleDatatypeDeclarationPtr option1 =
            dynamic_pointer_cast<SimpleDatatypeDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    ParametricDatatypeDeclarationPtr option2 =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
AttributeValuePtr share(AstPtr nakedPtr) {
    BooleanValuePtr option1 = dynamic_pointer_cast<BooleanValue>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    SortSymbolDeclarationPtr option5 = dynamic_pointer_cast<SortSymbolDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    if (dynamic_cast<FunSymbolDeclaration*>(nakedPtr)) {
        return share<FunSymbolDeclaration>(nakedPtr);
    }

    SymbolPtr option10 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    CompSExpressionPtr option11 = dynamic_pointer_cast<CompSExpression>(smtlib_nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    CompAttributeValuePtr option12 = dynamic_pointer_cast<CompAttributeValue>(smtlib_nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }

    throw;
}

template<>
SExpressionPtr share(AstPtr nakedPtr) {
    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    SymbolPtr option4 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    KeywordPtr option5 = dynamic_pointer_cast<Keyword>(smtlib_nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    CompSExpressionPtr option6 = dynamic_pointer_cast<CompSExpression>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    throw;
}

template<>
IdentifierPtr share(AstPtr nakedPtr) {
    SimpleIdentifierPtr option1 = dynamic_pointer_cast<SimpleIdentifier>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    QualifiedIdentifierPtr option2 = dynamic_pointer_cast<QualifiedIdentifier>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
TermPtr share(AstPtr nakedPtr) {
    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    if (dynamic_cast<Identifier*>(nakedPtr)) {
        return share<Identifier>(nakedPtr);
    }

    AnnotatedTermPtr option6 = dynamic_pointer_cast<AnnotatedTerm>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    ExistsTermPtr option7 = dynamic_pointer_cast<ExistsTerm>(smtlib_nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    ForallTermPtr option8 = dynamic_pointer_cast<ForallTerm>(smtlib_nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    LetTermPtr option9 = dynamic_pointer_cast<LetTerm>(smtlib_nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    QualifiedTermPtr option10 = dynamic_pointer_cast<QualifiedTerm>(smtlib_nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    MatchTermPtr option11 = dynamic_pointer_cast<MatchTerm>(smtlib_nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    throw;
}

template<>
IndexPtr share(AstPtr nakedPtr) {
    NumeralLiteralPtr option1 = dynamic_pointer_cast<NumeralLiteral>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    SymbolPtr option2 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

//namespace smtlib {
//namespace ast {

class ParserInternalList {
private:
    vector<AstPtr> v;
public:
    template<class T>
    vector<shared_ptr<T>> unwrap() {
        vector<shared_ptr<T>> result;
        for (unsigned long i = 0, n = v.size(); i < n; ++i) {
            shared_ptr<T> ptr = share<T>(v[i]);
            result.push_back(ptr);
        }
        v.clear();
        return result;
    };

    inline void add(AstPtr item) {
        v.push_back(item);
    }
};
//}
//}

AstList ast_listCreate() {
    return new ParserInternalList();
}

void ast_listAdd(AstList list, AstPtr item) {
    list->add(item);
}

void ast_listDelete(AstList list) {
    delete list;
}

void ast_print(AstPtr ptr) {
    cout << ptr->toString();
}

void ast_setAst(SmtPrsr parser, AstPtr ast) {
    if (parser && ast) {
        parser->setAst(smtlib_nodemap[ast]);
        smtlib_nodemap.clear();
    }
}

void ast_reportError(SmtPrsr parser, unsigned int rowLeft, unsigned int colLeft,
                     unsigned int rowRight, unsigned int colRight, const char* msg) {
    if (parser && msg) {
        parser->reportError(rowLeft, colLeft, rowRight, colRight, msg);
    }
}

void ast_setLocation(SmtPrsr parser, AstPtr ptr, int rowLeft, int colLeft, int rowRight, int colRight) {
    ptr->filename = parser->getFilename();
    ptr->rowLeft = rowLeft;
    ptr->colLeft = colLeft;
    ptr->rowRight = rowRight;
    ptr->colRight = colRight;
}

int ast_bool_value(AstPtr ptr) {
    BooleanValuePtr val = share<BooleanValue>(ptr);
    if (val) {
        return val->value;
    } else {
        return 2;
    }
}

// ast_attribute.h
AstPtr ast_newAttribute1(AstPtr keyword) {
    AttributePtr ptr = make_shared<Attribute>(share<Keyword>(keyword));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newAttribute2(AstPtr keyword, AstPtr attr_value) {
    AttributePtr ptr = make_shared<Attribute>(share<Keyword>(keyword), share<AttributeValue>(attr_value));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCompAttributeValue(AstList values) {
    vector<AttributeValuePtr> v = values->unwrap<AttributeValue>();
    CompAttributeValuePtr ptr = make_shared<CompAttributeValue>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_basic.h
AstPtr ast_newSymbol(char const* value) {
    SymbolPtr ptr = make_shared<Symbol>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newKeyword(char const* value) {
    KeywordPtr ptr = make_shared<Keyword>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMetaSpecConstant(int value) {
    MetaSpecConstantPtr ptr = make_shared<MetaSpecConstant>(
            static_cast<MetaSpecConstant::Type>(value));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newBooleanValue(int value) {
    BooleanValuePtr ptr = make_shared<BooleanValue>((bool) value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newPropLiteral(AstPtr symbol, int negated) {
    PropLiteralPtr ptr = make_shared<PropLiteral>(share<Symbol>(symbol), (bool) negated);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_command.h
AstPtr ast_newAssertCommand(AstPtr term) {
    AssertCommandPtr ptr = make_shared<AssertCommand>(share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCheckSatCommand() {
    CheckSatCommandPtr ptr = make_shared<CheckSatCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCheckSatAssumCommand(AstList assumptions) {
    vector<PropLiteralPtr> v = assumptions->unwrap<PropLiteral>();
    CheckSatAssumCommandPtr ptr = make_shared<CheckSatAssumCommand>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareConstCommand(AstPtr symbol, AstPtr sort) {
    DeclareConstCommandPtr ptr =
            make_shared<DeclareConstCommand>(share<Symbol>(symbol), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareDatatypeCommand(AstPtr symbol, AstPtr declaration) {
    DeclareDatatypeCommandPtr ptr =
            make_shared<DeclareDatatypeCommand>(share<Symbol>(symbol),
                                                share<DatatypeDeclaration>(declaration));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareDatatypesCommand(AstList sorts, AstList declarations) {
    vector<SortDeclarationPtr> v1 = sorts->unwrap<SortDeclaration>();
    vector<DatatypeDeclarationPtr> v2 = declarations->unwrap<DatatypeDeclaration>();
    DeclareDatatypesCommandPtr ptr = make_shared<DeclareDatatypesCommand>(v1, v2);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareFunCommand(AstPtr symbol, AstList params, AstPtr sort) {
    vector<SortPtr> v = params->unwrap<Sort>();
    DeclareFunCommandPtr ptr = make_shared<DeclareFunCommand>(share<Symbol>(symbol), v, share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareSortCommand(AstPtr symbol, AstPtr arity) {
    DeclareSortCommandPtr ptr =
            make_shared<DeclareSortCommand>(share<Symbol>(symbol), share<NumeralLiteral>(arity));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineFunCommand(AstPtr definition) {
    DefineFunCommandPtr ptr =
            make_shared<DefineFunCommand>(share<FunctionDefinition>(definition));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineFunRecCommand(AstPtr definition) {
    DefineFunRecCommandPtr ptr = make_shared<DefineFunRecCommand>(share<FunctionDefinition>(definition));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineFunsRecCommand(AstList declarations, AstList bodies) {
    vector<FunctionDeclarationPtr> v1 = declarations->unwrap<FunctionDeclaration>();
    vector<TermPtr> v2 = bodies->unwrap<Term>();
    DefineFunsRecCommandPtr ptr = make_shared<DefineFunsRecCommand>(v1, v2);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineSortCommand(AstPtr symbol, AstList params, AstPtr sort) {
    vector<SymbolPtr> v1 = params->unwrap<Symbol>();
    DefineSortCommandPtr ptr =
            make_shared<DefineSortCommand>(share<Symbol>(symbol), v1, share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newEchoCommand(AstPtr msg) {
    EchoCommandPtr ptr = make_shared<EchoCommand>(share<StringLiteral>(msg)->value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newExitCommand() {
    ExitCommandPtr ptr = make_shared<ExitCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetAssertsCommand() {
    GetAssertsCommandPtr ptr = make_shared<GetAssertsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetAssignsCommand() {
    GetAssignsCommandPtr ptr = make_shared<GetAssignsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetInfoCommand(AstPtr keyword) {
    GetInfoCommandPtr ptr = make_shared<GetInfoCommand>(share<Keyword>(keyword));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetModelCommand() {
    GetModelCommandPtr ptr = make_shared<GetModelCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetOptionCommand(AstPtr keyword) {
    GetOptionCommandPtr ptr = make_shared<GetOptionCommand>(share<Keyword>(keyword));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetProofCommand() {
    GetProofCommandPtr ptr = make_shared<GetProofCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetUnsatAssumsCommand() {
    GetUnsatAssumsCommandPtr ptr = make_shared<GetUnsatAssumsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetUnsatCoreCommand() {
    GetUnsatCoreCommandPtr ptr = make_shared<GetUnsatCoreCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetValueCommand(AstList terms) {
    vector<TermPtr> v = terms->unwrap<Term>();
    GetValueCommandPtr ptr = make_shared<GetValueCommand>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newPopCommand(AstPtr numeral) {
    PopCommandPtr ptr = make_shared<PopCommand>(share<NumeralLiteral>(numeral));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newPushCommand(AstPtr numeral) {
    PushCommandPtr ptr = make_shared<PushCommand>(share<NumeralLiteral>(numeral));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newResetCommand() {
    ResetCommandPtr ptr = make_shared<ResetCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newResetAssertsCommand() {
    ResetAssertsCommandPtr ptr = make_shared<ResetAssertsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSetInfoCommand(AstPtr info) {
    SetInfoCommandPtr ptr = make_shared<SetInfoCommand>(share<Attribute>(info));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSetLogicCommand(AstPtr logic) {
    SetLogicCommandPtr ptr = make_shared<SetLogicCommand>(share<Symbol>(logic));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSetOptionCommand(AstPtr option) {
    SetOptionCommandPtr ptr = make_shared<SetOptionCommand>(share<Attribute>(option));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//ast_datatype.h
AstPtr ast_newSortDeclaration(AstPtr symbol, AstPtr numeral) {
    SortDeclarationPtr ptr =
            make_shared<SortDeclaration>(share<Symbol>(symbol), share<NumeralLiteral>(numeral));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSelectorDeclaration(AstPtr symbol, AstPtr sort) {
    SelectorDeclarationPtr ptr =
            make_shared<SelectorDeclaration>(share<Symbol>(symbol), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newConstructorDeclaration(AstPtr symbol, AstList selectors) {
    vector<SelectorDeclarationPtr> v = selectors->unwrap<SelectorDeclaration>();
    ConstructorDeclarationPtr ptr = make_shared<ConstructorDeclaration>(share<Symbol>(symbol), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSimpleDatatypeDeclaration(AstList constructors) {
    vector<ConstructorDeclarationPtr> v = constructors->unwrap<ConstructorDeclaration>();
    SimpleDatatypeDeclarationPtr ptr = make_shared<SimpleDatatypeDeclaration>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newParametricDatatypeDeclaration(AstList params, AstList constructors) {
    vector<SymbolPtr> v1 = params->unwrap<Symbol>();
    vector<ConstructorDeclarationPtr> v2 = constructors->unwrap<ConstructorDeclaration>();
    ParametricDatatypeDeclarationPtr ptr = make_shared<ParametricDatatypeDeclaration>(v1, v2);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_fun.h
AstPtr ast_newFunctionDeclaration(AstPtr symbol, AstList params, AstPtr sort) {
    vector<SortedVariablePtr> v = params->unwrap<SortedVariable>();
    FunctionDeclarationPtr ptr =
            make_shared<FunctionDeclaration>(share<Symbol>(symbol), v, share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newFunctionDefinition(AstPtr signature, AstPtr body) {
    FunctionDefinitionPtr ptr = make_shared<FunctionDefinition>(
            share<FunctionDeclaration>(signature), share<Term>(body));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_identifier.h
AstPtr ast_newSimpleIdentifier1(AstPtr symbol) {
    SimpleIdentifierPtr ptr = make_shared<SimpleIdentifier>(share<Symbol>(symbol));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSimpleIdentifier2(AstPtr symbol, AstList indices) {
    vector<IndexPtr> v = indices->unwrap<Index>();
    SimpleIdentifierPtr ptr =
            make_shared<SimpleIdentifier>(share<Symbol>(symbol), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newQualifiedIdentifier(AstPtr identifier, AstPtr sort) {
    QualifiedIdentifierPtr ptr =
            make_shared<QualifiedIdentifier>(share<SimpleIdentifier>(identifier), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_literal.h
AstPtr ast_newNumeralLiteral(long value, unsigned int base) {
    NumeralLiteralPtr ptr = make_shared<NumeralLiteral>(value, base);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDecimalLiteral(double value) {
    DecimalLiteralPtr ptr = make_shared<DecimalLiteral>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newStringLiteral(char const* value) {
    StringLiteralPtr ptr = make_shared<StringLiteral>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_logic.h
AstPtr ast_newLogic(AstPtr name, AstList attributes) {
    vector<AttributePtr> v = attributes->unwrap<Attribute>();
    LogicPtr ptr = make_shared<Logic>(share<Symbol>(name), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_match.h
AstPtr ast_newQualifiedConstructor(AstPtr symbol, AstPtr sort) {
    QualifiedConstructorPtr ptr =
            make_shared<QualifiedConstructor>(share<Symbol>(symbol), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newQualifiedPattern(AstPtr constructor, AstList symbols) {
    vector<SymbolPtr> v = symbols->unwrap<Symbol>();
    QualifiedPatternPtr ptr = make_shared<QualifiedPattern>(share<Constructor>(constructor), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMatchCase(AstPtr pattern, AstPtr term) {
    MatchCasePtr ptr = make_shared<MatchCase>(share<Pattern>(pattern), share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_s_expr.h
AstPtr ast_newCompSExpression(AstList exprs) {
    vector<SExpressionPtr> v = exprs->unwrap<SExpression>();
    CompSExpressionPtr ptr = make_shared<CompSExpression>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_script.h
AstPtr ast_newScript(AstList cmds) {
    vector<CommandPtr> v = cmds->unwrap<Command>();
    ScriptPtr ptr = make_shared<Script>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_sort.h
AstPtr ast_newSort1(AstPtr identifier) {
    SortPtr ptr = make_shared<Sort>(share<SimpleIdentifier>(identifier));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSort2(AstPtr identifier, AstList params) {
    vector<SortPtr> v = params->unwrap<Sort>();
    SortPtr ptr = make_shared<Sort>(share<SimpleIdentifier>(identifier), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_symbol_decl.h
AstPtr ast_newSortSymbolDeclaration(AstPtr identifier, AstPtr arity, AstList attributes) {
    vector<AttributePtr> v = attributes->unwrap<Attribute>();
    SortSymbolDeclarationPtr ptr =
            make_shared<SortSymbolDeclaration>(share<SimpleIdentifier>(identifier),
                                               share<NumeralLiteral>(arity), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSpecConstFunDeclaration(AstPtr constant, AstPtr sort, AstList attributes) {
    vector<AttributePtr> v = attributes->unwrap<Attribute>();
    SpecConstFunDeclarationPtr ptr =
            make_shared<SpecConstFunDeclaration>(share<SpecConstant>(constant), share<Sort>(sort), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMetaSpecConstFunDeclaration(AstPtr constant, AstPtr sort, AstList attributes) {
    vector<AttributePtr> v = attributes->unwrap<Attribute>();
    MetaSpecConstFunDeclarationPtr ptr =
            make_shared<MetaSpecConstFunDeclaration>(share<MetaSpecConstant>(constant), share<Sort>(sort), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSimpleFunDeclaration(AstPtr identifier, AstList signature, AstList attributes) {
    vector<SortPtr> v1 = signature->unwrap<Sort>();
    vector<AttributePtr> v2 = attributes->unwrap<Attribute>();
    SimpleFunDeclarationPtr ptr =
            make_shared<SimpleFunDeclaration>(share<SimpleIdentifier>(identifier), v1, v2);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newParametricFunDeclaration(AstList params, AstPtr identifier, AstList signature, AstList attributes) {
    vector<SymbolPtr> v1 = params->unwrap<Symbol>();
    vector<SortPtr> v2 = signature->unwrap<Sort>();
    vector<AttributePtr> v3 = attributes->unwrap<Attribute>();
    ParametricFunDeclarationPtr ptr =
            make_shared<ParametricFunDeclaration>(v1, share<SimpleIdentifier>(identifier), v2, v3);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_term.h
AstPtr ast_newQualifiedTerm(AstPtr identifier, AstList terms) {
    vector<TermPtr> v = terms->unwrap<Term>();
    QualifiedTermPtr ptr = make_shared<QualifiedTerm>(share<Identifier>(identifier), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newLetTerm(AstList bindings, AstPtr term) {
    vector<VariableBindingPtr> v = bindings->unwrap<VariableBinding>();
    LetTermPtr ptr = make_shared<LetTerm>(v, share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newForallTerm(AstList bindings, AstPtr term) {
    vector<SortedVariablePtr> v = bindings->unwrap<SortedVariable>();
    ForallTermPtr ptr = make_shared<ForallTerm>(v, share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newExistsTerm(AstList bindings, AstPtr term) {
    vector<SortedVariablePtr> v = bindings->unwrap<SortedVariable>();
    ExistsTermPtr ptr = make_shared<ExistsTerm>(v, share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMatchTerm(AstPtr term, AstList cases) {
    vector<MatchCasePtr> v = cases->unwrap<MatchCase>();
    MatchTermPtr ptr = make_shared<MatchTerm>(share<Term>(term), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newAnnotatedTerm(AstPtr term, AstList attrs) {
    vector<AttributePtr> v = attrs->unwrap<Attribute>();
    AnnotatedTermPtr ptr = make_shared<AnnotatedTerm>(share<Term>(term), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_theory.h
AstPtr ast_newTheory(AstPtr name, AstList attributes) {
    vector<AttributePtr> v = attributes->unwrap<Attribute>();
    TheoryPtr ptr = make_shared<Theory>(share<Symbol>(name), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_variable.h
AstPtr ast_newSortedVariable(AstPtr symbol, AstPtr sort) {
    SortedVariablePtr ptr = make_shared<SortedVariable>(share<Symbol>(symbol), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newVariableBinding(AstPtr symbol, AstPtr term) {
    VariableBindingPtr ptr = make_shared<VariableBinding>(share<Symbol>(symbol), share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}
