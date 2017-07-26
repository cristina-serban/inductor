#include "sep_var_renamer.h"

#include "sep/sep_variable.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::sep;

unordered_map<string, string> &VariableRenamerContext::getRenamingMap() {
    return renamingMap;
};

void VariableRenamer::visit(sptr_t<SimpleIdentifier> node) {
    string name = node->name;

    auto &renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->name = renamingMap[name];
    }
}

void VariableRenamer::visit(sptr_t<SortedVariable> node) {
    string name = node->name;

    auto &renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->name = renamingMap[name];
    }
}

void VariableRenamer::visit(sptr_t<VariableBinding> node) {
    string name = node->name;

    auto &renamingMap = ctx->getRenamingMap();
    auto it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->name = renamingMap[name];
    }
}