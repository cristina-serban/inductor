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

sptr_um2<smtlib::ast::Node*, smtlib::ast::Node> smtlib_nodemap;

template<class T>
sptr_t<T> share(AstPtr nakedPtr) {
    return dynamic_pointer_cast<T>(smtlib_nodemap[nakedPtr]);
}

template<>
sptr_t<SpecConstant> share(AstPtr nakedPtr) {
    sptr_t<NumeralLiteral> option1 = dynamic_pointer_cast<NumeralLiteral>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    sptr_t<DecimalLiteral> option2 = dynamic_pointer_cast<DecimalLiteral>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    sptr_t<StringLiteral> option3 = dynamic_pointer_cast<StringLiteral>(smtlib_nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    throw;
}

template<>
sptr_t<Command> share(AstPtr nakedPtr) {
    sptr_t<AssertCommand> option1 = dynamic_pointer_cast<AssertCommand>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    sptr_t<CheckSatCommand> option2 = dynamic_pointer_cast<CheckSatCommand>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    sptr_t<CheckSatAssumCommand> option3 = dynamic_pointer_cast<CheckSatAssumCommand>(smtlib_nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    sptr_t<DeclareConstCommand> option4 = dynamic_pointer_cast<DeclareConstCommand>(smtlib_nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    sptr_t<DeclareFunCommand> option5 = dynamic_pointer_cast<DeclareFunCommand>(smtlib_nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    sptr_t<DeclareSortCommand> option6 = dynamic_pointer_cast<DeclareSortCommand>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    sptr_t<DefineFunCommand> option7 = dynamic_pointer_cast<DefineFunCommand>(smtlib_nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    sptr_t<DefineFunRecCommand> option8 = dynamic_pointer_cast<DefineFunRecCommand>(smtlib_nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    sptr_t<DefineFunsRecCommand> option9 = dynamic_pointer_cast<DefineFunsRecCommand>(smtlib_nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    sptr_t<DefineSortCommand> option10 = dynamic_pointer_cast<DefineSortCommand>(smtlib_nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    sptr_t<EchoCommand> option11 = dynamic_pointer_cast<EchoCommand>(smtlib_nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    sptr_t<ExitCommand> option12 = dynamic_pointer_cast<ExitCommand>(smtlib_nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }

    sptr_t<SetOptionCommand> option13 = dynamic_pointer_cast<SetOptionCommand>(smtlib_nodemap[nakedPtr]);
    if (option13) {
        return option13->shared_from_this();
    }

    sptr_t<GetAssertsCommand> option14 = dynamic_pointer_cast<GetAssertsCommand>(smtlib_nodemap[nakedPtr]);
    if (option14) {
        return option14->shared_from_this();
    }

    sptr_t<GetAssignsCommand> option15 = dynamic_pointer_cast<GetAssignsCommand>(smtlib_nodemap[nakedPtr]);
    if (option15) {
        return option15->shared_from_this();
    }

    sptr_t<GetInfoCommand> option16 = dynamic_pointer_cast<GetInfoCommand>(smtlib_nodemap[nakedPtr]);
    if (option16) {
        return option16->shared_from_this();
    }

    sptr_t<GetModelCommand> option17 = dynamic_pointer_cast<GetModelCommand>(smtlib_nodemap[nakedPtr]);
    if (option17) {
        return option17->shared_from_this();
    }

    sptr_t<GetOptionCommand> option18 = dynamic_pointer_cast<GetOptionCommand>(smtlib_nodemap[nakedPtr]);
    if (option18) {
        return option18->shared_from_this();
    }

    sptr_t<GetProofCommand> option19 = dynamic_pointer_cast<GetProofCommand>(smtlib_nodemap[nakedPtr]);
    if (option19) {
        return option19->shared_from_this();
    }

    sptr_t<GetUnsatAssumsCommand> option20 = dynamic_pointer_cast<GetUnsatAssumsCommand>(smtlib_nodemap[nakedPtr]);
    if (option20) {
        return option20->shared_from_this();
    }

    sptr_t<GetUnsatCoreCommand> option21 = dynamic_pointer_cast<GetUnsatCoreCommand>(smtlib_nodemap[nakedPtr]);
    if (option21) {
        return option21->shared_from_this();
    }

    sptr_t<GetValueCommand> option22 = dynamic_pointer_cast<GetValueCommand>(smtlib_nodemap[nakedPtr]);
    if (option22) {
        return option22->shared_from_this();
    }

    sptr_t<PopCommand> option23 = dynamic_pointer_cast<PopCommand>(smtlib_nodemap[nakedPtr]);
    if (option23) {
        return option23->shared_from_this();
    }

    sptr_t<PushCommand> option24 = dynamic_pointer_cast<PushCommand>(smtlib_nodemap[nakedPtr]);
    if (option24) {
        return option24->shared_from_this();
    }

    sptr_t<ResetCommand> option25 = dynamic_pointer_cast<ResetCommand>(smtlib_nodemap[nakedPtr]);
    if (option25) {
        return option25->shared_from_this();
    }

    sptr_t<ResetAssertsCommand> option26 = dynamic_pointer_cast<ResetAssertsCommand>(smtlib_nodemap[nakedPtr]);
    if (option26) {
        return option26->shared_from_this();
    }

    sptr_t<SetInfoCommand> option27 = dynamic_pointer_cast<SetInfoCommand>(smtlib_nodemap[nakedPtr]);
    if (option27) {
        return option27->shared_from_this();
    }

    sptr_t<SetLogicCommand> option28 = dynamic_pointer_cast<SetLogicCommand>(smtlib_nodemap[nakedPtr]);
    if (option28) {
        return option28->shared_from_this();
    }

    sptr_t<DeclareDatatypeCommand> option29 = dynamic_pointer_cast<DeclareDatatypeCommand>(smtlib_nodemap[nakedPtr]);
    if (option29) {
        return option29->shared_from_this();
    }

    sptr_t<DeclareDatatypesCommand> option30 = dynamic_pointer_cast<DeclareDatatypesCommand>(smtlib_nodemap[nakedPtr]);
    if (option30) {
        return option30->shared_from_this();
    }

    throw;
}

template<>
sptr_t<FunSymbolDeclaration> share(AstPtr nakedPtr) {
    sptr_t<SpecConstFunDeclaration> option6 = dynamic_pointer_cast<SpecConstFunDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    sptr_t<MetaSpecConstFunDeclaration> option7 = dynamic_pointer_cast<MetaSpecConstFunDeclaration>(
            smtlib_nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    sptr_t<SimpleFunDeclaration> option8 = dynamic_pointer_cast<SimpleFunDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    sptr_t<ParametricFunDeclaration> option9 = dynamic_pointer_cast<ParametricFunDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    throw;
}

template<>
sptr_t<Constructor> share(AstPtr nakedPtr) {
    sptr_t<Symbol> option1 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    sptr_t<QualifiedConstructor> option2 = dynamic_pointer_cast<QualifiedConstructor>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
sptr_t<Pattern> share(AstPtr nakedPtr) {
    if (dynamic_cast<Constructor*>(nakedPtr)) {
        return share<Constructor>(nakedPtr);
    }

    sptr_t<Symbol> option1 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    sptr_t<QualifiedPattern> option2 = dynamic_pointer_cast<QualifiedPattern>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
sptr_t<DatatypeDeclaration> share(AstPtr nakedPtr) {
    sptr_t<SimpleDatatypeDeclaration> option1 =
            dynamic_pointer_cast<SimpleDatatypeDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    sptr_t<ParametricDatatypeDeclaration> option2 =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
sptr_t<AttributeValue> share(AstPtr nakedPtr) {
    sptr_t<BooleanValue> option1 = dynamic_pointer_cast<BooleanValue>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    sptr_t<SortSymbolDeclaration> option5 = dynamic_pointer_cast<SortSymbolDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    if (dynamic_cast<FunSymbolDeclaration*>(nakedPtr)) {
        return share<FunSymbolDeclaration>(nakedPtr);
    }

    sptr_t<Symbol> option10 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    sptr_t<CompSExpression> option11 = dynamic_pointer_cast<CompSExpression>(smtlib_nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    sptr_t<CompAttributeValue> option12 = dynamic_pointer_cast<CompAttributeValue>(smtlib_nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }

    throw;
}

template<>
sptr_t<SExpression> share(AstPtr nakedPtr) {
    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    sptr_t<Symbol> option4 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    sptr_t<Keyword> option5 = dynamic_pointer_cast<Keyword>(smtlib_nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    sptr_t<CompSExpression> option6 = dynamic_pointer_cast<CompSExpression>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    throw;
}

template<>
sptr_t<Identifier> share(AstPtr nakedPtr) {
    sptr_t<SimpleIdentifier> option1 = dynamic_pointer_cast<SimpleIdentifier>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    sptr_t<QualifiedIdentifier> option2 = dynamic_pointer_cast<QualifiedIdentifier>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
sptr_t<Term> share(AstPtr nakedPtr) {
    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    if (dynamic_cast<Identifier*>(nakedPtr)) {
        return share<Identifier>(nakedPtr);
    }

    sptr_t<AnnotatedTerm> option6 = dynamic_pointer_cast<AnnotatedTerm>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    sptr_t<ExistsTerm> option7 = dynamic_pointer_cast<ExistsTerm>(smtlib_nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    sptr_t<ForallTerm> option8 = dynamic_pointer_cast<ForallTerm>(smtlib_nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    sptr_t<LetTerm> option9 = dynamic_pointer_cast<LetTerm>(smtlib_nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    sptr_t<QualifiedTerm> option10 = dynamic_pointer_cast<QualifiedTerm>(smtlib_nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    sptr_t<MatchTerm> option11 = dynamic_pointer_cast<MatchTerm>(smtlib_nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    throw;
}

template<>
sptr_t<Index> share(AstPtr nakedPtr) {
    sptr_t<NumeralLiteral> option1 = dynamic_pointer_cast<NumeralLiteral>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    sptr_t<Symbol> option2 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
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
    vector<sptr_t<T>> unwrap() {
        vector<sptr_t<T>> result;
        for (unsigned long i = 0, n = v.size(); i < n; ++i) {
            sptr_t<T> ptr = share<T>(v[i]);
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
    sptr_t<BooleanValue> val = share<BooleanValue>(ptr);
    if (val) {
        return val->value;
    } else {
        return 2;
    }
}

// ast_attribute.h
AstPtr ast_newAttribute1(AstPtr keyword) {
    sptr_t<Attribute> ptr = make_shared<Attribute>(share<Keyword>(keyword));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newAttribute2(AstPtr keyword, AstPtr attr_value) {
    sptr_t<Attribute> ptr = make_shared<Attribute>(share<Keyword>(keyword),
                                                       share<AttributeValue>(attr_value));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCompAttributeValue(AstList values) {
    vector<sptr_t<AttributeValue>> v = values->unwrap<AttributeValue>();
    sptr_t<CompAttributeValue> ptr = make_shared<CompAttributeValue>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_basic.h
AstPtr ast_newSymbol(char const* value) {
    sptr_t<Symbol> ptr = make_shared<Symbol>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newKeyword(char const* value) {
    sptr_t<Keyword> ptr = make_shared<Keyword>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMetaSpecConstant(int value) {
    sptr_t<MetaSpecConstant> ptr = make_shared<MetaSpecConstant>(
            static_cast<MetaSpecConstant::Type>(value));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newBooleanValue(int value) {
    sptr_t<BooleanValue> ptr = make_shared<BooleanValue>((bool) value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newPropLiteral(AstPtr symbol, int negated) {
    sptr_t<PropLiteral> ptr = make_shared<PropLiteral>(share<Symbol>(symbol), (bool) negated);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_command.h
AstPtr ast_newAssertCommand(AstPtr term) {
    sptr_t<AssertCommand> ptr = make_shared<AssertCommand>(share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCheckSatCommand() {
    sptr_t<CheckSatCommand> ptr = make_shared<CheckSatCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCheckSatAssumCommand(AstList assumptions) {
    vector<sptr_t<PropLiteral>> v = assumptions->unwrap<PropLiteral>();
    sptr_t<CheckSatAssumCommand> ptr = make_shared<CheckSatAssumCommand>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareConstCommand(AstPtr symbol, AstPtr sort) {
    sptr_t<DeclareConstCommand> ptr =
            make_shared<DeclareConstCommand>(share<Symbol>(symbol), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareDatatypeCommand(AstPtr symbol, AstPtr declaration) {
    sptr_t<DeclareDatatypeCommand> ptr =
            make_shared<DeclareDatatypeCommand>(share<Symbol>(symbol),
                                                share<DatatypeDeclaration>(declaration));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareDatatypesCommand(AstList sorts, AstList declarations) {
    vector<sptr_t<SortDeclaration>> v1 = sorts->unwrap<SortDeclaration>();
    vector<sptr_t<DatatypeDeclaration>> v2 = declarations->unwrap<DatatypeDeclaration>();
    sptr_t<DeclareDatatypesCommand> ptr = make_shared<DeclareDatatypesCommand>(v1, v2);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareFunCommand(AstPtr symbol, AstList params, AstPtr sort) {
    vector<sptr_t<Sort>> v = params->unwrap<Sort>();
    sptr_t<DeclareFunCommand> ptr =
            make_shared<DeclareFunCommand>(share<Symbol>(symbol), v, share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareSortCommand(AstPtr symbol, AstPtr arity) {
    sptr_t<DeclareSortCommand> ptr =
            make_shared<DeclareSortCommand>(share<Symbol>(symbol), share<NumeralLiteral>(arity));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineFunCommand(AstPtr definition) {
    sptr_t<DefineFunCommand> ptr =
            make_shared<DefineFunCommand>(share<FunctionDefinition>(definition));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineFunRecCommand(AstPtr definition) {
    sptr_t<DefineFunRecCommand> ptr = make_shared<DefineFunRecCommand>(
            share<FunctionDefinition>(definition));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineFunsRecCommand(AstList declarations, AstList bodies) {
    vector<sptr_t<FunctionDeclaration>> v1 = declarations->unwrap<FunctionDeclaration>();
    vector<sptr_t<Term>> v2 = bodies->unwrap<Term>();
    sptr_t<DefineFunsRecCommand> ptr = make_shared<DefineFunsRecCommand>(v1, v2);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineSortCommand(AstPtr symbol, AstList params, AstPtr sort) {
    vector<sptr_t<Symbol>> v1 = params->unwrap<Symbol>();
    sptr_t<DefineSortCommand> ptr =
            make_shared<DefineSortCommand>(share<Symbol>(symbol), v1, share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newEchoCommand(AstPtr msg) {
    sptr_t<EchoCommand> ptr = make_shared<EchoCommand>(share<StringLiteral>(msg)->value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newExitCommand() {
    sptr_t<ExitCommand> ptr = make_shared<ExitCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetAssertsCommand() {
    sptr_t<GetAssertsCommand> ptr = make_shared<GetAssertsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetAssignsCommand() {
    sptr_t<GetAssignsCommand> ptr = make_shared<GetAssignsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetInfoCommand(AstPtr keyword) {
    sptr_t<GetInfoCommand> ptr = make_shared<GetInfoCommand>(share<Keyword>(keyword));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetModelCommand() {
    sptr_t<GetModelCommand> ptr = make_shared<GetModelCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetOptionCommand(AstPtr keyword) {
    sptr_t<GetOptionCommand> ptr = make_shared<GetOptionCommand>(share<Keyword>(keyword));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetProofCommand() {
    sptr_t<GetProofCommand> ptr = make_shared<GetProofCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetUnsatAssumsCommand() {
    sptr_t<GetUnsatAssumsCommand> ptr = make_shared<GetUnsatAssumsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetUnsatCoreCommand() {
    sptr_t<GetUnsatCoreCommand> ptr = make_shared<GetUnsatCoreCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetValueCommand(AstList terms) {
    vector<sptr_t<Term>> v = terms->unwrap<Term>();
    sptr_t<GetValueCommand> ptr = make_shared<GetValueCommand>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newPopCommand(AstPtr numeral) {
    sptr_t<PopCommand> ptr = make_shared<PopCommand>(share<NumeralLiteral>(numeral));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newPushCommand(AstPtr numeral) {
    sptr_t<PushCommand> ptr = make_shared<PushCommand>(share<NumeralLiteral>(numeral));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newResetCommand() {
    sptr_t<ResetCommand> ptr = make_shared<ResetCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newResetAssertsCommand() {
    sptr_t<ResetAssertsCommand> ptr = make_shared<ResetAssertsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSetInfoCommand(AstPtr info) {
    sptr_t<SetInfoCommand> ptr = make_shared<SetInfoCommand>(share<Attribute>(info));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSetLogicCommand(AstPtr logic) {
    sptr_t<SetLogicCommand> ptr = make_shared<SetLogicCommand>(share<Symbol>(logic));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSetOptionCommand(AstPtr option) {
    sptr_t<SetOptionCommand> ptr = make_shared<SetOptionCommand>(share<Attribute>(option));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//ast_datatype.h
AstPtr ast_newSortDeclaration(AstPtr symbol, AstPtr numeral) {
    sptr_t<SortDeclaration> ptr =
            make_shared<SortDeclaration>(share<Symbol>(symbol), share<NumeralLiteral>(numeral));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSelectorDeclaration(AstPtr symbol, AstPtr sort) {
    sptr_t<SelectorDeclaration> ptr =
            make_shared<SelectorDeclaration>(share<Symbol>(symbol), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newConstructorDeclaration(AstPtr symbol, AstList selectors) {
    vector<sptr_t<SelectorDeclaration>> v = selectors->unwrap<SelectorDeclaration>();
    sptr_t<ConstructorDeclaration> ptr = make_shared<ConstructorDeclaration>(share<Symbol>(symbol), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSimpleDatatypeDeclaration(AstList constructors) {
    vector<sptr_t<ConstructorDeclaration>> v = constructors->unwrap<ConstructorDeclaration>();
    sptr_t<SimpleDatatypeDeclaration> ptr = make_shared<SimpleDatatypeDeclaration>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newParametricDatatypeDeclaration(AstList params, AstList constructors) {
    vector<sptr_t<Symbol>> v1 = params->unwrap<Symbol>();
    vector<sptr_t<ConstructorDeclaration>> v2 = constructors->unwrap<ConstructorDeclaration>();
    sptr_t<ParametricDatatypeDeclaration> ptr = make_shared<ParametricDatatypeDeclaration>(v1, v2);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_fun.h
AstPtr ast_newFunctionDeclaration(AstPtr symbol, AstList params, AstPtr sort) {
    vector<sptr_t<SortedVariable>> v = params->unwrap<SortedVariable>();
    sptr_t<FunctionDeclaration> ptr =
            make_shared<FunctionDeclaration>(share<Symbol>(symbol), v, share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newFunctionDefinition(AstPtr signature, AstPtr body) {
    sptr_t<FunctionDefinition> ptr = make_shared<FunctionDefinition>(
            share<FunctionDeclaration>(signature), share<Term>(body));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_identifier.h
AstPtr ast_newSimpleIdentifier1(AstPtr symbol) {
    sptr_t<SimpleIdentifier> ptr = make_shared<SimpleIdentifier>(share<Symbol>(symbol));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSimpleIdentifier2(AstPtr symbol, AstList indices) {
    vector<sptr_t<Index>> v = indices->unwrap<Index>();
    sptr_t<SimpleIdentifier> ptr =
            make_shared<SimpleIdentifier>(share<Symbol>(symbol), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newQualifiedIdentifier(AstPtr identifier, AstPtr sort) {
    sptr_t<QualifiedIdentifier> ptr =
            make_shared<QualifiedIdentifier>(share<SimpleIdentifier>(identifier), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_literal.h
AstPtr ast_newNumeralLiteral(long value, unsigned int base) {
    sptr_t<NumeralLiteral> ptr = make_shared<NumeralLiteral>(value, base);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDecimalLiteral(double value) {
    sptr_t<DecimalLiteral> ptr = make_shared<DecimalLiteral>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newStringLiteral(char const* value) {
    sptr_t<StringLiteral> ptr = make_shared<StringLiteral>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_logic.h
AstPtr ast_newLogic(AstPtr name, AstList attributes) {
    vector<sptr_t<Attribute>> v = attributes->unwrap<Attribute>();
    sptr_t<Logic> ptr = make_shared<Logic>(share<Symbol>(name), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_match.h
AstPtr ast_newQualifiedConstructor(AstPtr symbol, AstPtr sort) {
    sptr_t<QualifiedConstructor> ptr =
            make_shared<QualifiedConstructor>(share<Symbol>(symbol), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newQualifiedPattern(AstPtr constructor, AstList symbols) {
    vector<sptr_t<Symbol>> v = symbols->unwrap<Symbol>();
    sptr_t<QualifiedPattern> ptr = make_shared<QualifiedPattern>(share<Constructor>(constructor), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMatchCase(AstPtr pattern, AstPtr term) {
    sptr_t<MatchCase> ptr =
            make_shared<MatchCase>(share<Pattern>(pattern), share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_s_expr.h
AstPtr ast_newCompSExpression(AstList exprs) {
    vector<sptr_t<SExpression>> v = exprs->unwrap<SExpression>();
    sptr_t<CompSExpression> ptr = make_shared<CompSExpression>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_script.h
AstPtr ast_newScript(AstList cmds) {
    vector<sptr_t<Command>> v = cmds->unwrap<Command>();
    sptr_t<Script> ptr = make_shared<Script>(v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_sort.h
AstPtr ast_newSort1(AstPtr identifier) {
    sptr_t<Sort> ptr = make_shared<Sort>(share<SimpleIdentifier>(identifier));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSort2(AstPtr identifier, AstList params) {
    vector<sptr_t<Sort>> v = params->unwrap<Sort>();
    sptr_t<Sort> ptr = make_shared<Sort>(share<SimpleIdentifier>(identifier), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_symbol_decl.h
AstPtr ast_newSortSymbolDeclaration(AstPtr identifier, AstPtr arity, AstList attributes) {
    vector<sptr_t<Attribute>> v = attributes->unwrap<Attribute>();
    sptr_t<SortSymbolDeclaration> ptr =
            make_shared<SortSymbolDeclaration>(share<SimpleIdentifier>(identifier),
                                               share<NumeralLiteral>(arity), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSpecConstFunDeclaration(AstPtr constant, AstPtr sort, AstList attributes) {
    vector<sptr_t<Attribute>> v = attributes->unwrap<Attribute>();
    sptr_t<SpecConstFunDeclaration> ptr =
            make_shared<SpecConstFunDeclaration>(share<SpecConstant>(constant), share<Sort>(sort), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMetaSpecConstFunDeclaration(AstPtr constant, AstPtr sort, AstList attributes) {
    vector<sptr_t<Attribute>> v = attributes->unwrap<Attribute>();
    sptr_t<MetaSpecConstFunDeclaration> ptr =
            make_shared<MetaSpecConstFunDeclaration>(share<MetaSpecConstant>(constant), share<Sort>(sort), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSimpleFunDeclaration(AstPtr identifier, AstList signature, AstList attributes) {
    vector<sptr_t<Sort>> v1 = signature->unwrap<Sort>();
    vector<sptr_t<Attribute>> v2 = attributes->unwrap<Attribute>();
    sptr_t<SimpleFunDeclaration> ptr =
            make_shared<SimpleFunDeclaration>(share<SimpleIdentifier>(identifier), v1, v2);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newParametricFunDeclaration(AstList params, AstPtr identifier, AstList signature, AstList attributes) {
    vector<sptr_t<Symbol>> v1 = params->unwrap<Symbol>();
    vector<sptr_t<Sort>> v2 = signature->unwrap<Sort>();
    vector<sptr_t<Attribute>> v3 = attributes->unwrap<Attribute>();
    sptr_t<ParametricFunDeclaration> ptr =
            make_shared<ParametricFunDeclaration>(v1, share<SimpleIdentifier>(identifier), v2, v3);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_term.h
AstPtr ast_newQualifiedTerm(AstPtr identifier, AstList terms) {
    vector<sptr_t<Term>> v = terms->unwrap<Term>();
    sptr_t<QualifiedTerm> ptr = make_shared<QualifiedTerm>(share<Identifier>(identifier), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newLetTerm(AstList bindings, AstPtr term) {
    vector<sptr_t<VariableBinding>> v = bindings->unwrap<VariableBinding>();
    sptr_t<LetTerm> ptr = make_shared<LetTerm>(v, share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newForallTerm(AstList bindings, AstPtr term) {
    vector<sptr_t<SortedVariable>> v = bindings->unwrap<SortedVariable>();
    sptr_t<ForallTerm> ptr = make_shared<ForallTerm>(v, share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newExistsTerm(AstList bindings, AstPtr term) {
    vector<sptr_t<SortedVariable>> v = bindings->unwrap<SortedVariable>();
    sptr_t<ExistsTerm> ptr = make_shared<ExistsTerm>(v, share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMatchTerm(AstPtr term, AstList cases) {
    vector<sptr_t<MatchCase>> v = cases->unwrap<MatchCase>();
    sptr_t<MatchTerm> ptr = make_shared<MatchTerm>(share<Term>(term), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newAnnotatedTerm(AstPtr term, AstList attrs) {
    vector<sptr_t<Attribute>> v = attrs->unwrap<Attribute>();
    sptr_t<AnnotatedTerm> ptr = make_shared<AnnotatedTerm>(share<Term>(term), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_theory.h
AstPtr ast_newTheory(AstPtr name, AstList attributes) {
    vector<sptr_t<Attribute>> v = attributes->unwrap<Attribute>();
    sptr_t<Theory> ptr =
            make_shared<Theory>(share<Symbol>(name), v);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_variable.h
AstPtr ast_newSortedVariable(AstPtr symbol, AstPtr sort) {
    sptr_t<SortedVariable> ptr =
            make_shared<SortedVariable>(share<Symbol>(symbol), share<Sort>(sort));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newVariableBinding(AstPtr symbol, AstPtr term) {
    sptr_t<VariableBinding> ptr =
            make_shared<VariableBinding>(share<Symbol>(symbol), share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}