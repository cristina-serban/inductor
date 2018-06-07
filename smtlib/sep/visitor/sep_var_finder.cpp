#include <algorithm>
#include "sep_var_finder.h"

#include "sep/sep_term.h"

using namespace std;
using namespace smtlib::sep;

void VariableFinder::addUniqueVariable(const SortedVariablePtr& var) {
    auto& vars = ctx->getVariables();
    string str = var->toString();

    bool dup = vars.end() != find_if(vars.begin(), vars.end(),
                                     [&](const SortedVariablePtr& varsIt) {
                                         return varsIt->toString() == str;
                                     });

    if (!dup) {
        vars.push_back(var);
    }
}

void VariableFinder::addUniqueBinding(const SortedVariablePtr& bind) {
    auto& binds = ctx->getBindings();
    string str = bind->toString();

    bool dup = binds.end() != find_if(binds.begin(), binds.end(),
                                      [&](const SortedVariablePtr& varsIt) {
                                          return varsIt->toString() == str;
                                      });

    if (!dup) {
        binds.push_back(bind);
    }
}

void VariableFinder::visit(const SimpleIdentifierPtr& node) {
    string name = node->name;
    SortPtr sort;

    std::vector<FunEntryPtr> entries = ctx->getStack()->getFunEntry(name);
    for (const auto& entry : entries) {
        if(entry->params.empty()) {
            sort = entry->signature[0];
            break;
        }
    }

    if(sort) {
        addUniqueVariable(make_shared<SortedVariable>(name, sort));
    }
}

void VariableFinder::visit(const QualifiedIdentifierPtr& node) {
    string name = node->identifier->name;
    SortPtr sort = node->sort;
    string sortStr = node->sort->toString();

    std::vector<FunEntryPtr> entries = ctx->getStack()->getFunEntry(name);
    for (const auto& entry : entries) {
        if(entry->params.size() == 1
           && entry->signature[0]->toString() == sortStr) {
            addUniqueVariable(make_shared<SortedVariable>(name, sort));
        }
    }
}

void VariableFinder::visit(const QualifiedTermPtr& node) {
    if (node->terms.empty()) {
        visit0(node->identifier);
    }

    visit0(node->terms);
}

void VariableFinder::visit(const ExistsTermPtr& node) {
    for (const auto& bind : node->bindings) {
        addUniqueBinding(make_shared<SortedVariable>(bind->name, bind->sort));
    }

    visit0(node->term);
}
