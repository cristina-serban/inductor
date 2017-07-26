#include "sep_symbol_table.h"

#include "sep/sep_symbol_decl.h"

using namespace std;
using namespace smtlib::sep;

sptr_t<SortEntry> SymbolTable::getSortEntry(string name) {
    auto it = sorts.find(name);
    if (it != sorts.end()) {
        return it->second;
    } else {
        sptr_t<SortEntry> empty;
        return empty;
    }
}

sptr_v<FunEntry> SymbolTable::getFunEntry(string name) {
    auto it = funs.find(name);
    if (it != funs.end()) {
        return it->second;
    } else {
        sptr_v<FunEntry> empty;
        return empty;
    }
}

sptr_t<VarEntry> SymbolTable::getVarEntry(string name) {
    auto it = vars.find(name);
    if (it != vars.end()) {
        return it->second;
    } else {
        sptr_t<VarEntry> empty;
        return empty;
    }
}

bool SymbolTable::add(sptr_t<SortEntry> entry) {
    if(sorts.find(entry->name) == sorts.end()) {
        sorts[entry->name] = entry;
        return true;
    } else {
        return false;
    }
}

bool SymbolTable::add(sptr_t<FunEntry> entry) {
    funs[entry->name].push_back(entry);
    return true;
}

bool SymbolTable::add(sptr_t<VarEntry> entry) {
    if(vars.find(entry->name) == vars.end()) {
        vars[entry->name] = entry;
        return true;
    } else {
        return false;
    }
}

void SymbolTable::reset() {
    // Clear all variables
    vars.clear();

    // Erase sort entries that do not come from theory files
    sptr_v<SortEntry> sortEntries;
    for (auto sortIt = sorts.begin(); sortIt != sorts.end(); sortIt++) {
        sortEntries.push_back(sortIt->second);
    }

    for (auto sortEntryIt = sortEntries.begin(); sortEntryIt != sortEntries.end(); sortEntryIt++) {
        if(!dynamic_pointer_cast<SortSymbolDeclaration>((*sortEntryIt)->source)) {
            sorts.erase((*sortEntryIt)->name);
        }
    }

    // Erase function entries that do not come from theory files
    vector<string> funKeys;
    vector<sptr_v<FunEntry>> funEntries;
    for (auto funIt = funs.begin(); funIt != funs.end(); funIt++) {
        funKeys.push_back(funIt->first);
        funEntries.push_back(funIt->second);
    }

    for (int i = 0; i < funKeys.size(); i++) {
        sptr_v<FunEntry>& entry = funs[funKeys[i]];
        for (int j = 0; j < funEntries[i].size(); j++) {
            if(!dynamic_pointer_cast<FunSymbolDeclaration>(funEntries[i][j]->source)) {
                entry.erase(entry.begin() + j);
            }
        }

        if(entry.empty())
            funs.erase(funKeys[i]);
    }
}
