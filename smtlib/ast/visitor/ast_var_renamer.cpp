#include "ast_var_renamer.h"

#include "ast/ast_variable.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

unordered_map<string, string> &VariableRenamerContext::getRenamingMap() {
    return renamingMap;
};

void VariableRenamer::visit(sptr_t<SimpleIdentifier> node) {
    string &name = node->symbol->value;

    auto &renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->symbol->value = renamingMap[name];
    }
}

void VariableRenamer::visit(sptr_t<SortedVariable> node) {
    string &name = node->symbol->value;

    auto &renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->symbol->value = renamingMap[name];
    }
}

void VariableRenamer::visit(sptr_t<VariableBinding> node) {
    string &name = node->symbol->value;

    auto &renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->symbol->value = renamingMap[name];
    }
}