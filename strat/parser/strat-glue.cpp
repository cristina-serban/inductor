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
        for (unsigned long i = 0, n = v.size(); i < n; ++i) {
            shared_ptr<T> ptr = share<T>(v[i]);
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

void strat_reportError(StratPrsr parser, unsigned int rowLeft, unsigned int colLeft,
                     unsigned int rowRight, unsigned int colRight, const char *msg) {
    if (parser && msg) {
        parser->reportError(rowLeft, colLeft, rowRight, colRight, msg);
    }
}

void strat_setLocation(StratPrsr parser, StratPtr ptr, int rowLeft, int colLeft, int rowRight, int colRight) {
    ptr->filename = parser->getFilename();
    ptr->rowLeft = rowLeft;
    ptr->colLeft = colLeft;
    ptr->rowRight = rowRight;
    ptr->colRight = colRight;
}

//ast_basic.h
StratPtr strat_newStringLiteral(char const *value) {
    shared_ptr<StringLiteral> ptr = make_shared<StringLiteral>(value);
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

StratPtr strat_newRule(StratPtr name) {
    shared_ptr<Rule> ptr = make_shared<Rule>(share<StringLiteral>(name));
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

StratPtr strat_newState(StratPtr name) {
    shared_ptr<State> ptr = make_shared<State>(share<StringLiteral>(name));
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//ast_transition.h
StratPtr strat_newTransition(StratPtr start, StratPtr rule, StratPtr end) {
    shared_ptr<Transition> ptr =
            make_shared<Transition>(share<State>(start), share<Rule>(rule), share<State>(end));
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//ast_automaton.h
StratPtr strat_newAutomaton(StratPtr name, StratList states, StratPtr init,
                            StratList final, StratList transitions) {
    vector<shared_ptr<State>> unwrappedStates = states->unwrap<State>();
    vector<shared_ptr<State>> unwrappedFinalStates = final->unwrap<State>();
    vector<shared_ptr<Transition>> unwrappedTransitions = transitions->unwrap<Transition>();

    shared_ptr<Automaton> ptr = make_shared<Automaton>(share<StringLiteral>(name), unwrappedStates,
                                                       share<State>(init), unwrappedFinalStates, unwrappedTransitions);
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//ast_file.h
StratPtr strat_newFile(StratList declarations, StratPtr automaton) {
    vector<shared_ptr<Rule>> unwrappedRules = declarations->unwrap<Rule>();

    shared_ptr<File> ptr = make_shared<File>(unwrappedRules, share<Automaton>(automaton));
    strat_nodemap[ptr.get()] = ptr;
    return ptr.get();
}