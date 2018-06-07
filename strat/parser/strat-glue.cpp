#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <unordered_map>
#include "strat-glue.h"

#include "strat_parser.h"

#include "../ast/ast_abstract.h"
#include "../ast/ast_automaton.h"
#include "../ast/ast_basic.h"
#include "../ast/ast_file.h"
#include "../ast/ast_transition.h"

using namespace std;
using namespace strat;
using namespace strat::ast;

unordered_map<strat::ast::Node *, shared_ptr<strat::ast::Node>> strat_nodemap;

template<class T>
shared_ptr<T> share(StratPtr nakedPtr) {
    return dynamic_pointer_cast<T>(strat_nodemap[nakedPtr]);
}

//namespace strat {
//namespace ast {

class ParserInternalList {
private:
    vector<StratPtr> v;
public:
    template<class T>
    vector<shared_ptr<T>> unwrap() {
        vector<shared_ptr<T>> result;
        for (auto& elem : v) {
            shared_ptr<T> ptr = share<T>(elem);
            result.push_back(ptr);
        }
        v.clear();
        return result;
    };

    inline void add(StratPtr item) {
        v.push_back(item);
    }
};
//}
//}

StratList strat_listCreate() {
    return new ParserInternalList();
}

void strat_listAdd(StratList list, StratPtr item) {
    list->add(item);
}

void strat_listDelete(StratList list) {
    delete list;
}

void strat_print(StratPtr ptr) {
    cout << ptr->toString();
}

void strat_setAst(StratPrsr parser, StratPtr ast) {
    if (parser && ast) {
        parser->setAst(strat_nodemap[ast]);
        strat_nodemap.clear();
    }
}

void strat_reportError(StratPrsr parser,
                       int rowLeft, int colLeft,
                       int rowRight, int colRight,
                       const char* msg) {
    if (parser && msg) {
        parser->reportError(rowLeft, colLeft, rowRight, colRight, msg);
    }
}

void strat_setLocation(StratPrsr parser, StratPtr ptr,
                       int rowLeft, int colLeft,
                       int rowRight, int colRight) {
    ptr->filename = parser->getFilename();
    ptr->rowLeft = rowLeft;
    ptr->colLeft = colLeft;
    ptr->rowRight = rowRight;
    ptr->colRight = colRight;
}

//ast_basic.h
StratPtr strat_newStringLiteral(char const *value) {
    StringLiteralPtr ptr = make_shared<StringLiteral>(value);
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

StratPtr strat_newRule(StratPtr name) {
    RulePtr ptr = make_shared<Rule>(std::move(share<StringLiteral>(name)));
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

StratPtr strat_newState(StratPtr name) {
    StatePtr ptr = make_shared<State>(std::move(share<StringLiteral>(name)));
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//ast_transition.h
StratPtr strat_newTransition(StratPtr start, StratPtr rule, StratPtr end) {
    TransitionPtr ptr = make_shared<Transition>(std::move(share<State>(start)),
                                                std::move(share<Rule>(rule)),
                                                std::move(share<State>(end)));
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//ast_automaton.h
StratPtr strat_newAutomaton(StratPtr name, StratList states,
                            StratPtr initial, StratList final,
                            StratList transitions) {
    AutomatonPtr ptr = make_shared<Automaton>(std::move(share<StringLiteral>(name)),
                                              std::move(states->unwrap<State>()),
                                              std::move(share<State>(initial)),
                                              std::move(final->unwrap<State>()),
                                              std::move(transitions->unwrap<Transition>()));
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//ast_file.h
StratPtr strat_newFile(StratList declarations, StratPtr automaton) {
    FilePtr ptr = make_shared<File>(std::move(declarations->unwrap<Rule>()),
                                    std::move(share<Automaton>(automaton)));
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}
