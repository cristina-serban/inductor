#include "sep_var_renamer.h"

#include "sep/sep_variable.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::sep;

RenamingMap& VariableRenamerContext::getRenamingMap() {
    return renamingMap;
};

void VariableRenamer::visit(const SimpleIdentifierPtr& node) {
    string name = node->name;

    auto& renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->name = it->second;
    }
}

void VariableRenamer::visit(const SortedVariablePtr& node) {
    string name = node->name;

    auto& renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->name = it->second;
    }
}

void VariableRenamer::visit(const VariableBindingPtr& node) {
    string name = node->name;

    auto& renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->name = it->second;
    }
}
