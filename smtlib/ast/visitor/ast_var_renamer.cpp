#include "ast_var_renamer.h"

#include "ast/ast_variable.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

RenamingMap& VariableRenamerContext::getRenamingMap() {
    return renamingMap;
};

void VariableRenamer::visit(const SimpleIdentifierPtr& node) {
    string& name = node->symbol->value;

    auto& renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->symbol->value = it->second;
    }
}

void VariableRenamer::visit(const SortedVariablePtr& node) {
    string& name = node->symbol->value;

    auto& renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->symbol->value = it->second;
    }
}

void VariableRenamer::visit(const VariableBindingPtr& node) {
    string& name = node->symbol->value;

    auto& renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->symbol->value = it->second;
    }
}