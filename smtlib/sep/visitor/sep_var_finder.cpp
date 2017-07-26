#include <algorithm>
#include "sep_var_finder.h"

#include "sep/sep_term.h"

using namespace std;
using namespace smtlib::sep;

void VariableFinder::addUniqueVariable(sptr_t<SortedVariable> var) {
    auto &vars = ctx->getVariables();
    string str = var->toString();

    bool dup = vars.end() != find_if(vars.begin(), vars.end(),
                                     [&](const sptr_t<SortedVariable> &varsIt) {
                                         return varsIt->toString() == str;
                                     });

    if (!dup) {
        vars.push_back(var);
    }
}

void VariableFinder::addUniqueBinding(sptr_t<SortedVariable> bind) {
    auto &binds = ctx->getBindings();
    string str = bind->toString();

    bool dup = binds.end() != find_if(binds.begin(), binds.end(),
                                      [&](const sptr_t<SortedVariable> &varsIt) {
                                          return varsIt->toString() == str;
                                      });

    if (!dup) {
        binds.push_back(bind);
    }
}

void VariableFinder::visit(sptr_t<SimpleIdentifier> node) {
    string name = node->name;
    sptr_t<Sort> sort;

    sptr_v<FunEntry> entries = ctx->getStack()->getFunEntry(name);
    for (size_t i = 0, n = entries.size(); i < n; i++) {
        if(entries[i]->params.size() == 0) {
            sort = entries[i]->signature[0];
            break;
        }
    }

    if(sort) {
        addUniqueVariable(make_shared<SortedVariable>(name, sort));
    }
}

void VariableFinder::visit(sptr_t<QualifiedIdentifier> node) {
    string name = node->identifier->name;
    sptr_t<Sort> sort = node->sort;
    string sortStr = node->sort->toString();

    sptr_v<FunEntry> entries = ctx->getStack()->getFunEntry(name);
    for (size_t i = 0, n = entries.size(); i < n; i++) {
        if(entries[i]->params.size() == 1
           && entries[i]->signature[0]->toString() == sortStr) {
            addUniqueVariable(make_shared<SortedVariable>(name, sort));
        }
    }
}

void VariableFinder::visit(sptr_t<QualifiedTerm> node) {
    if (node->terms.empty()) {
        visit0(node->identifier);
    }

    visit0(node->terms);
}

void VariableFinder::visit(sptr_t<ExistsTerm> node) {
    sptr_v<SortedVariable> &binds = node->bindings;

    for(size_t i = 0, n = binds.size(); i < n; i++) {
        addUniqueBinding(make_shared<SortedVariable>(binds[i]->name, binds[i]->sort));
    }

    visit0(node->term);
}