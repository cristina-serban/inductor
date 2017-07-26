#include "ast_symbol_table.h"

#include "ast/ast_command.h"
#include "ast/ast_symbol_decl.h"

using namespace std;
using namespace smtlib::ast;

sptr_t<SortInfo> SymbolTable::getSortInfo(string name) {
    auto it = sorts.find(name);
    if (it != sorts.end()) {
        return it->second;
    } else {
        sptr_t<SortInfo> empty;
        return empty;
    }
}

sptr_v<FunInfo> SymbolTable::getFunInfo(string name) {
    auto it = funs.find(name);
    if (it != funs.end()) {
        return it->second;
    } else {
        sptr_v<FunInfo> empty;
        return empty;
    }
}

sptr_t<VarInfo> SymbolTable::getVarInfo(string name) {
    auto it = vars.find(name);
    if (it != vars.end()) {
        return it->second;
    } else {
        sptr_t<VarInfo> empty;
        return empty;
    }
}

bool SymbolTable::add(sptr_t<SortInfo> info) {
    if(sorts.find(info->name) == sorts.end()) {
        sorts[info->name] = info;
        return true;
    } else {
        return false;
    }
}

bool SymbolTable::add(sptr_t<FunInfo> info) {
    funs[info->name].push_back(info);
    return true;
}

bool SymbolTable::add(sptr_t<VarInfo> info) {
    if(vars.find(info->name) == vars.end()) {
        vars[info->name] = info;
        return true;
    } else {
        return false;
    }
}

void SymbolTable::reset() {
    // Clear all variables
    vars.clear();

    // Erase sort information that does not come from theory files
    sptr_v<SortInfo> sortInfos;
    for (auto sortIt = sorts.begin(); sortIt != sorts.end(); sortIt++) {
        sortInfos.push_back(sortIt->second);
    }

    for (auto sortInfoIt = sortInfos.begin(); sortInfoIt != sortInfos.end(); sortInfoIt++) {
        if(!dynamic_pointer_cast<SortSymbolDeclaration>((*sortInfoIt)->source)) {
            sorts.erase((*sortInfoIt)->name);
        }
    }

    // Erase function information that does not come from theory files
    vector<string> funKeys;
    vector<sptr_v<FunInfo>> funInfos;
    for (auto funIt = funs.begin(); funIt != funs.end(); funIt++) {
        funKeys.push_back(funIt->first);
        funInfos.push_back(funIt->second);
    }

    for (int i = 0; i < funKeys.size(); i++) {
        sptr_v<FunInfo>& info = funs[funKeys[i]];
        for (int j = 0; j < funInfos[i].size(); j++) {
            if(!dynamic_pointer_cast<FunSymbolDeclaration>(funInfos[i][j]->source)) {
                info.erase(info.begin() + j);
            }
        }
        if(info.empty())
            funs.erase(funKeys[i]);
    }
}