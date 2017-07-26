#include "ast_symbol_stack.h"

using namespace std;
using namespace smtlib::ast;

SymbolStack::SymbolStack() {
    push();
}

sptr_t<SymbolTable> SymbolStack::getTopLevel() {
    return stack[stack.size() - 1];
}

sptr_v<SymbolTable> &SymbolStack::getStack() {
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

sptr_t<SortInfo> SymbolStack::getSortInfo(string name) {
    sptr_t<SortInfo> null;
    for (auto lvlIt = stack.begin(); lvlIt != stack.end(); lvlIt++) {
        sptr_t<SortInfo> info = (*lvlIt)->getSortInfo(name);
        if (info)
            return info;
    }
    return null;
}

sptr_v<FunInfo> SymbolStack::getFunInfo(string name) {
    sptr_v<FunInfo> result;
    for (auto lvlIt = stack.begin(); lvlIt != stack.end(); lvlIt++) {
        sptr_v<FunInfo> infos = (*lvlIt)->getFunInfo(name);
        result.insert(result.end(), infos.begin(), infos.end());
    }
    return result;
}

sptr_t<VarInfo> SymbolStack::getVarInfo(string name) {
    sptr_t<VarInfo> null;
    for (auto lvlIt = stack.begin(); lvlIt != stack.end(); lvlIt++) {
        sptr_t<VarInfo> info = (*lvlIt)->getVarInfo(name);
        if (info)
            return info;
    }
    return null;
}

sptr_t<SortInfo> SymbolStack::findDuplicate(sptr_t<SortInfo> info) {
    sptr_t<SortInfo> null;
    for (auto lvlIt = stack.begin(); lvlIt != stack.end(); lvlIt++) {
        sptr_t<SortInfo> dup = (*lvlIt)->getSortInfo(info->name);
        if (dup)
            return dup;
    }
    return null;
}

sptr_t<FunInfo> SymbolStack::findDuplicate(sptr_t<FunInfo> info) {
    sptr_t<FunInfo> null;
    sptr_v<FunInfo> knownFuns = getFunInfo(info->name);
    for (auto funIt = knownFuns.begin(); funIt != knownFuns.end(); funIt++) {
        if (info->params.size() == 0 && (*funIt)->params.size() == 0) {
            if (equal(info->signature, (*funIt)->signature)) {
                return (*funIt);
            }
        } else {
            if (equal(info->params, info->signature,
                      (*funIt)->params, (*funIt)->signature)) {
                return (*funIt);
            }
        }
    }
    return null;
}

sptr_t<VarInfo> SymbolStack::findDuplicate(sptr_t<VarInfo> info) {
    return getTopLevel()->getVarInfo(info->name);
}

sptr_t<Sort> SymbolStack::replace(sptr_t<Sort> sort,
                                  unordered_map<string, sptr_t<Sort>> &mapping) {
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
            return make_shared<Sort>(sort->identifier, newargs);
        } else {
            return sort;
        }
    }
}

sptr_t<Sort> SymbolStack::expand(sptr_t<Sort> sort) {
    if (!sort)
        return sort;

    sptr_t<Sort> null;

    sptr_t<SortInfo> info = getSortInfo(sort->identifier->toString());
    if (!sort->hasArgs()) {
        if (info && info->definition) {
            if (info->definition->params.empty()) {
                sptr_t<Sort> newsort = make_shared<Sort>(info->definition->sort->identifier,
                                                         info->definition->sort->args);
                newsort->rowLeft = sort->rowLeft;
                newsort->colLeft = sort->colLeft;
                newsort->rowRight = sort->rowRight;
                newsort->colRight = sort->colRight;
                newsort->filename = sort->filename;

                return newsort;
            } else {
                return null;
            }
        } else {
            return sort;
        }
    } else {
        if (info && info->definition) {
            if (info->definition->params.size() == sort->args.size()) {
                unordered_map<string, sptr_t<Sort>> mapping;
                for (int i = 0; i < info->definition->params.size(); i++) {
                    mapping[info->definition->params[i]->toString()] = sort->args[i];
                }

                sptr_t<Sort> newsort = replace(info->definition->sort, mapping);
                newsort = expand(newsort);
                newsort->rowLeft = sort->rowLeft;
                newsort->colLeft = sort->colLeft;
                newsort->rowRight = sort->rowRight;
                newsort->colRight = sort->colRight;
                newsort->filename = sort->filename;

                return newsort;
            } else {
                return null;
            }
        } else {
            if (info && info->arity != sort->args.size())
                return null;

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
                sptr_t<Sort> newsort = make_shared<Sort>(sort->identifier, newargs);
                newsort->rowLeft = sort->rowLeft;
                newsort->colLeft = sort->colLeft;
                newsort->rowRight = sort->rowRight;
                newsort->colRight = sort->colRight;
                newsort->filename = sort->filename;

                return newsort;
            } else {
                return sort;
            }
        }
    }
}

bool SymbolStack::equal(sptr_t<Sort> sort1,
                        sptr_t<Sort> sort2) {
    if (sort1 && sort2) {
        return sort1->toString() == sort2->toString();
    } else {
        return false;
    }
}

bool SymbolStack::equal(sptr_v<Symbol> &params1,
                        sptr_t<Sort> sort1,
                        sptr_v<Symbol> &params2,
                        sptr_t<Sort> sort2,
                        unordered_map<string, string> &mapping) {
    if (!sort1 || !sort2) {
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
            if (params1[j]->toString() == str1)
                isParam1 = true;
            if (params2[j]->toString() == str2)
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
        if (sort1->identifier->toString() != sort2->identifier->toString())
            return false;

        for (unsigned long k = 0; k < sort1->args.size(); k++) {
            if (!equal(params1, sort1->args[k], params2, sort2->args[k], mapping))
                return false;
        }

        return true;
    }
}

bool SymbolStack::equal(sptr_v<Sort> &signature1,
                        sptr_v<Sort> &signature2) {
    if (signature1.size() != signature2.size())
        return false;

    for (unsigned long i = 0; i < signature1.size(); i++) {
        if (!equal(signature1[i], signature2[i]))
            return false;
    }

    return true;
}

bool SymbolStack::equal(sptr_v<Symbol> &params1,
                        sptr_v<Sort> &signature1,
                        sptr_v<Symbol> &params2,
                        sptr_v<Sort> &signature2) {
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

sptr_t<SortInfo> SymbolStack::tryAdd(sptr_t<SortInfo> info) {
    sptr_t<SortInfo> dup = findDuplicate(info);
    if (!dup)
        getTopLevel()->add(info);
    return dup;
}

sptr_t<FunInfo> SymbolStack::tryAdd(sptr_t<FunInfo> info) {
    sptr_t<FunInfo> dup = findDuplicate(info);
    if (!dup)
        getTopLevel()->add(info);
    return dup;
}

sptr_t<VarInfo> SymbolStack::tryAdd(sptr_t<VarInfo> info) {
    sptr_t<VarInfo> dup = findDuplicate(info);
    if (!dup)
        getTopLevel()->add(info);
    return dup;
}