#include "sep_symbol_stack.h"

using namespace std;
using namespace smtlib::sep;

SymbolStack::SymbolStack() {
    push();
}

sptr_t<SymbolTable> SymbolStack::getTopLevel() {
    return stack[stack.size() - 1];
}

sptr_v<SymbolTable>& SymbolStack::getStack() {
    return stack;
}

bool SymbolStack::push() {
    unsigned long size = stack.size();
    stack.push_back(make_shared<SymbolTable>());
    return (stack.size() == size + 1);
}

bool SymbolStack::push(unsigned long levels) {
    unsigned long size = stack.size();
    for (int i = 0; i < levels; i++)
        stack.push_back(make_shared<SymbolTable>());
    return (stack.size() == size + levels);
}

bool SymbolStack::pop() {
    if (stack.size() <= 1) {
        return false;
    } else {
        unsigned long size = stack.size();
        stack.erase(stack.begin() + (stack.size() - 1));
        return (stack.size() == size - 1);
    }
}

bool SymbolStack::pop(unsigned long levels) {
    if (stack.size() <= 1 + levels || levels == 0) {
        return false;
    } else {
        unsigned long size = stack.size();
        stack.erase(stack.begin() + (stack.size() - levels), stack.begin() + (stack.size() - 1));
        return (stack.size() == size - 1);
    }
}

void SymbolStack::reset() {
    pop(stack.size() - 1);
    getTopLevel()->reset();
}

sptr_t<SortEntry> SymbolStack::getSortEntry(string name) {
    sptr_t<SortEntry> null;
    for (auto lvlIt = stack.begin(); lvlIt != stack.end(); lvlIt++) {
        sptr_t<SortEntry> entry = (*lvlIt)->getSortEntry(name);
        if (entry)
            return entry;
    }
    return null;
}

sptr_v<FunEntry> SymbolStack::getFunEntry(string name) {
    sptr_v<FunEntry> result;
    for (auto lvlIt = stack.begin(); lvlIt != stack.end(); lvlIt++) {
        sptr_v<FunEntry> entries = (*lvlIt)->getFunEntry(name);
        result.insert(result.end(), entries.begin(), entries.end());
    }
    return result;
}

sptr_t<VarEntry> SymbolStack::getVarEntry(string name) {
    sptr_t<VarEntry> null;
    for (auto lvlIt = stack.begin(); lvlIt != stack.end(); lvlIt++) {
        sptr_t<VarEntry> entry = (*lvlIt)->getVarEntry(name);
        if (entry)
            return entry;
    }
    return null;
}

sptr_t<SortEntry> SymbolStack::findDuplicate(sptr_t<SortEntry> entry) {
    sptr_t<SortEntry> null;
    for (auto lvlIt = stack.begin(); lvlIt != stack.end(); lvlIt++) {
        sptr_t<SortEntry> dup = (*lvlIt)->getSortEntry(entry->name);
        if (dup)
            return dup;
    }
    return null;
}

sptr_t<FunEntry> SymbolStack::findDuplicate(sptr_t<FunEntry> entry) {
    sptr_t<FunEntry> null;
    sptr_v<FunEntry> knownFuns = getFunEntry(entry->name);
    for (auto funIt = knownFuns.begin(); funIt != knownFuns.end(); funIt++) {
        if (entry->params.size() == 0 && (*funIt)->params.size() == 0) {
            if (equal(entry->signature, (*funIt)->signature)) {
                return (*funIt);
            }
        } else {
            if (equal(entry->params, entry->signature,
                      (*funIt)->params, (*funIt)->signature)) {
                return (*funIt);
            }
        }
    }
    return null;
}

sptr_t<VarEntry> SymbolStack::findDuplicate(sptr_t<VarEntry> entry) {
    return getTopLevel()->getVarEntry(entry->name);
}

sptr_t<Sort> SymbolStack::replace(sptr_t<Sort> sort,
                                      unordered_map<string, sptr_t<Sort>>& mapping) {
    if (mapping.empty())
        return sort;

    if (!sort->hasArgs()) {
        if (mapping.find(sort->toString()) != mapping.end())
            return mapping[sort->toString()];
        else
            return sort;
    } else {
        sptr_v<Sort> newargs;
        bool changed = false;
        sptr_v<Sort> argSorts = sort->args;
        for (auto argIt = argSorts.begin(); argIt != argSorts.end(); argIt++) {
            sptr_t<Sort> result = replace(*argIt, mapping);

            newargs.push_back(result);
            if (result.get() != (*argIt).get())
                changed = true;
        }

        if (changed) {
            return make_shared<Sort>(sort->name, newargs);
        } else {
            return sort;
        }
    }
}

sptr_t<Sort> SymbolStack::expand(sptr_t<Sort> sort) {
    if (!sort)
        return sort;

    sptr_t<Sort> null;

    sptr_t<SortEntry> entry = getSortEntry(sort->name);
    if (!sort->hasArgs()) {
        if (entry) {
            if (entry->params.empty()) {
                sptr_v<Sort> empty;
                sptr_t<Sort> newsort = make_shared<Sort>(entry->name, empty);
                return newsort;
            } else {
                return null;
            }
        } else {
            return sort;
        }
    } else {
        if (entry) {
            if (entry->arity != sort->args.size())
                return null;

            if (entry->params.size() == sort->args.size()) {
                unordered_map<string, sptr_t<Sort>> mapping;
                for (int i = 0; i < entry->params.size(); i++) {
                    mapping[entry->params[i]] = sort->args[i];
                }

                sptr_t<Sort> newsort = replace(entry->sort, mapping);
                newsort = expand(newsort);
                return newsort;
            } else {
                return null;
            }
        } else {
            sptr_v<Sort> newargs;
            bool changed = false;
            sptr_v<Sort> argSorts = sort->args;
            for (auto argIt = argSorts.begin(); argIt != argSorts.end(); argIt++) {
                sptr_t<Sort> result = expand(*argIt);
                if (!result)
                    return null;

                newargs.push_back(result);
                if (result.get() != (*argIt).get())
                    changed = true;
            }

            if (changed) {
                sptr_t<Sort> newsort = make_shared<Sort>(sort->name, newargs);
                return newsort;
            } else {
                return sort;
            }
        }
    }
}

bool SymbolStack::equal(sptr_t<Sort> sort1,
                        sptr_t<Sort> sort2) {
    if(sort1 && sort2) {
        return sort1->toString() == sort2->toString();
    } else {
        return false;
    }
}

bool SymbolStack::equal(vector<string>& params1,
                        sptr_t<Sort> sort1,
                        vector<string>& params2,
                        sptr_t<Sort> sort2,
                        unordered_map<string, string>& mapping) {
    if(!sort1 || !sort2) {
        return false;
    }

    if (sort1->args.size() != sort2->args.size())
        return false;

    if (sort1->args.size() == 0) {
        bool isParam1 = false;
        bool isParam2 = false;

        string str1 = sort1->toString();
        string str2 = sort2->toString();

        for (unsigned long j = 0; j < params1.size(); j++) {
            if (params1[j] == str1)
                isParam1 = true;
            if (params2[j] == str2)
                isParam2 = true;
        }

        if ((isParam1 && !isParam2) || (!isParam1 && isParam2)) {
            return false;
        } else if (isParam1) {
            if (mapping.find(str1) != mapping.end()) {
                return mapping[str1] == str2;
            } else {
                mapping[str1] = str2;
                return true;
            }
        } else {
            return equal(sort1, sort2);
        }
    } else {
        if (sort1->name != sort2->name)
            return false;

        for (unsigned long k = 0; k < sort1->args.size(); k++) {
            if (!equal(params1, sort1->args[k], params2, sort2->args[k], mapping))
                return false;
        }

        return true;
    }
}

bool SymbolStack::equal(sptr_v<Sort>& signature1,
                        sptr_v<Sort>& signature2) {
    if (signature1.size() != signature2.size())
        return false;

    for (unsigned long i = 0; i < signature1.size(); i++) {
        if (!equal(signature1[i], signature2[i]))
            return false;
    }

    return true;
}

bool SymbolStack::equal(vector<string>& params1,
                        sptr_v<Sort>& signature1,
                        vector<string>& params2,
                        sptr_v<Sort>& signature2) {
    if (params1.size() != params2.size() || signature1.size() != signature2.size())
        return false;

    unordered_map<string, string> mapping;
    for (unsigned long i = 0; i < signature1.size(); i++) {
        sptr_t<Sort> sort1 = signature1[i];
        sptr_t<Sort> sort2 = signature2[i];

        if (!equal(params1, sort1, params2, sort2, mapping))
            return false;
    }

    return mapping.size() == params1.size();
}

sptr_t<SortEntry> SymbolStack::tryAdd(sptr_t<SortEntry> entry) {
    sptr_t<SortEntry> dup = findDuplicate(entry);
    if (!dup)
        getTopLevel()->add(entry);
    return dup;
}

sptr_t<FunEntry> SymbolStack::tryAdd(sptr_t<FunEntry> entry) {
    sptr_t<FunEntry> dup = findDuplicate(entry);
    if (!dup)
        getTopLevel()->add(entry);
    return dup;
}

sptr_t<VarEntry> SymbolStack::tryAdd(sptr_t<VarEntry> entry) {
    sptr_t<VarEntry> dup = findDuplicate(entry);
    if (!dup)
        getTopLevel()->add(entry);
    return dup;
}