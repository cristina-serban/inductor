#ifndef DOWN_INCL_TIMBUK_GLUE_H
#define DOWN_INCL_TIMBUK_GLUE_H

#ifdef __cplusplus
#include "../ast/ast_abstract.h"
namespace strat {
    namespace ast {
        class Node;
    }
    class Parser;
}
class ParserInternalList;

typedef class strat::ast::Node* StratPtr;
typedef class ParserInternalList* StratList;
typedef class strat::Parser* StratPrsr;
#else
typedef void *StratPtr, *StratList, *StratPrsr;
#endif

#ifdef __cplusplus
extern "C" {
#endif

int strat_yylex (void);
int strat_yyparse(StratPrsr);

void strat_print(StratPtr ptr);

void strat_setAst(StratPrsr parser, StratPtr ast);
void strat_reportError(StratPrsr parser,
                       int rowLeft, int colLeft,
                       int rowRight, int colRight,
                       const char* msg);

StratList strat_listCreate();
void strat_listAdd(StratList list, StratPtr item);
void strat_listDelete(StratList list);

void strat_setLocation(StratPrsr parser, StratPtr ptr,
                       int rowLeft, int colLeft,
                       int rowRight, int colRight);

//ast_basic.h
StratPtr strat_newStringLiteral(char const* value);
StratPtr strat_newRule(StratPtr name);
StratPtr strat_newState(StratPtr name);

//ast_transition.h
StratPtr strat_newTransition(StratPtr start, StratPtr rule, StratPtr end);

//ast_automaton.h
StratPtr strat_newAutomaton(StratPtr name, StratList states,
                            StratPtr initial, StratList final,
                            StratList transitions);

//ast_file.h
StratPtr strat_newFile(StratList rules, StratPtr automaton);

#ifdef __cplusplus
}; // extern "C"
#endif

#endif //DOWN_INCL_TIMBUK_GLUE_H
