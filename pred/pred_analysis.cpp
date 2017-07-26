#include "pred_analysis.h"

using namespace std;
using namespace equiv;
using namespace reach;
using namespace pred;
using namespace smtlib::sep;

sptr_t<IndexAllocAnalysis> IndexAllocAnalysis::clone() {
    sptr_t<IndexAllocAnalysis> copy = make_shared<IndexAllocAnalysis>();
    copy->pred.insert(pred.begin(), pred.end());
    copy->base.insert(base.begin(), base.end());
    copy->ind.insert(ind.begin(), ind.end());
    return copy;
}

bool IndexAllocAnalysis::equals(sptr_t<IndexAllocAnalysis> other) {
    if (!other)
        return false;

    if (base.size() != other->base.size() ||
        ind.size() != other->ind.size() ||
        pred.size() != other->pred.size()) {
        return false;
    }

    for (auto it = pred.begin(); it != pred.end(); it++) {
        string name = (*it).first;
        if (other->pred.find(name) == other->pred.end())
            return false;

        if ((*it).second.size() != other->pred[name].size())
            return false;

        for (int i = 0; i < (*it).second.size(); i++) {
            if ((*it).second[i] != other->pred[name][i])
                return false;
        }
    }

    for (auto it = ind.begin(); it != ind.end(); it++) {
        string name = (*it).first;

        if (other->ind.find(name) == other->ind.end())
            return false;

        sptr_um3<InductiveCase, vector<Allocated>> map = (*it).second;
        sptr_um3<InductiveCase, vector<Allocated>> otherMap = other->ind[name];

        for (auto itt = map.begin(); itt != map.end(); itt++) {
            sptr_t<InductiveCase> icase = (*itt).first;
            if (otherMap.find(icase) == otherMap.end())
                return false;

            if ((*itt).second.size() != otherMap[icase].size())
                return false;

            for (int i = 0; i < (*itt).second.size(); i++) {
                if ((*itt).second[i] != otherMap[icase][i])
                    return false;
            }
        }
    }

    for (auto it = base.begin(); it != base.end(); it++) {
        string name = (*it).first;

        if (other->base.find(name) == other->base.end())
            return false;

        sptr_um3<BaseCase, vector<Allocated>> map = (*it).second;
        sptr_um3<BaseCase, vector<Allocated>> otherMap = other->base[name];

        for (auto itt = map.begin(); itt != map.end(); itt++) {
            sptr_t<BaseCase> bcase = (*itt).first;
            if (otherMap.find(bcase) == otherMap.end())
                return false;

            if ((*itt).second.size() != otherMap[bcase].size())
                return false;

            for (int i = 0; i < (*itt).second.size(); i++) {
                if ((*itt).second[i] != otherMap[bcase][i])
                    return false;
            }
        }
    }

    return true;
}

sptr_t<IndexReachAnalysis> IndexReachAnalysis::clone() {
    sptr_t<IndexReachAnalysis> copy = make_shared<IndexReachAnalysis>();

    for (auto it = pred.begin(); it != pred.end(); it++) {
        copy->pred[(*it).first] = (*it).second->clone();
    }

    for (auto it = base.begin(); it != base.end(); it++) {
        sptr_um1<BaseCase, IndexReachability> cloneBase;
        for (auto itt = (*it).second.begin(); itt != (*it).second.end(); itt++) {
            cloneBase[(*itt).first] = (*itt).second->clone();
        }

        copy->base[(*it).first] = cloneBase;
    }

    for (auto it = ind.begin(); it != ind.end(); it++) {
        sptr_um1<InductiveCase, IndexReachability> cloneInd;
        for (auto itt = (*it).second.begin(); itt != (*it).second.end(); itt++) {
            cloneInd[(*itt).first] = (*itt).second->clone();
        }

        copy->ind[(*it).first] = cloneInd;
    }

    return copy;
}

bool IndexReachAnalysis::equals(sptr_t<IndexReachAnalysis> other) {
    if (!other)
        return false;

    if (base.size() != other->base.size() ||
        ind.size() != other->ind.size() ||
        pred.size() != other->pred.size()) {
        return false;
    }

    for (auto it = pred.begin(); it != pred.end(); it++) {
        string name = (*it).first;
        if (other->pred.find(name) == other->pred.end())
            return false;

        if (!(*it).second->equals(other->pred[(*it).first]))
            return false;
    }

    for (auto it = ind.begin(); it != ind.end(); it++) {
        string name = (*it).first;

        if (other->ind.find(name) == other->ind.end())
            return false;

        sptr_um1<InductiveCase, IndexReachability> map = (*it).second;
        sptr_um1<InductiveCase, IndexReachability> otherMap = other->ind[name];

        for (auto itt = map.begin(); itt != map.end(); itt++) {
            sptr_t<InductiveCase> icase = (*itt).first;
            if (otherMap.find(icase) == otherMap.end())
                return false;

            if (!(*itt).second->equals(otherMap[icase]))
                return false;
        }
    }

    for (auto it = base.begin(); it != base.end(); it++) {
        string name = (*it).first;

        if (other->base.find(name) == other->base.end())
            return false;

        sptr_um1<BaseCase, IndexReachability> map = (*it).second;
        sptr_um1<BaseCase, IndexReachability> otherMap = other->base[name];

        for (auto itt = map.begin(); itt != map.end(); itt++) {
            sptr_t<BaseCase> bcase = (*itt).first;
            if (otherMap.find(bcase) == otherMap.end())
                return false;

            if (!(*itt).second->equals(otherMap[bcase]))
                return false;
        }
    }

    return true;
}

Allocated pred::conj(Allocated a1, Allocated a2) {
    if (a1 == a2) {
        return a1;
    }

    return Allocated::MAYBE;
}

Allocated pred::conj(vector<Allocated> vec) {
    bool always = true;
    bool never = true;

    for (auto it = vec.begin(); it != vec.end(); it++) {
        if (*it != Allocated::ALWAYS)
            always = false;

        if (*it != Allocated::NEVER)
            never = false;
    }

    Allocated value = Allocated::MAYBE;
    if (always)
        value = Allocated::ALWAYS;
    if (never)
        value = Allocated::NEVER;

    return value;
}

vector<Allocated> pred::conj(vector<Allocated> vec1, vector<Allocated> vec2) {
    vector<Allocated> result;
    if (vec1.size() != vec2.size()) {
        return result;
    }

    result = vec1;
    for (unsigned long i = 1; i < vec2.size(); i++) {
        result[i] = conj(result[i], vec2[i]);
    }

    return result;
}

vector<Allocated> pred::conj(vector<vector<Allocated>> vec) {
    vector<Allocated> result;
    if (vec.empty())
        return result;

    result = vec[0];
    for (unsigned long i = 1; i < vec.size(); i++) {
        for (unsigned long j = 0; j < vec[i].size(); j++) {
            result[j] = conj(result[j], vec[i][j]);
        }
    }

    return result;
}

Allocated pred::disj(Allocated a1, Allocated a2) {
    if (a1 == a2) {
        return a1;
    }

    if (a1 == Allocated::ALWAYS) {
        return a1;
    }

    if (a1 == Allocated::NEVER) {
        return a2;
    }

    return Allocated::MAYBE;
}

Allocated pred::disj(vector<Allocated> vec) {
    bool never = true;

    for (auto it = vec.begin(); it != vec.end(); it++) {
        if (*it == Allocated::ALWAYS)
            return Allocated::ALWAYS;

        if (*it != Allocated::NEVER)
            never = false;
    }

    return never ? Allocated::NEVER : Allocated::MAYBE;
}

vector<Allocated> pred::disj(vector<Allocated> vec1, vector<Allocated> vec2) {
    vector<Allocated> result;
    if (vec1.size() != vec2.size()) {
        return result;
    }

    result = vec1;
    for (unsigned long i = 1; i < vec2.size(); i++) {
        result[i] = disj(result[i], vec2[i]);
    }

    return result;
}

vector<Allocated> pred::disj(vector<vector<Allocated>> vec) {
    vector<Allocated> result;
    if (vec.empty())
        return result;

    result = vec[0];
    for (unsigned long i = 1; i < vec.size(); i++) {
        for (unsigned long j = 0; j < vec[i].size(); j++) {
            result[j] = disj(result[j], vec[i][j]);
        }
    }

    return result;
}

vector<vector<Allocated>> pred::varToIndex(vector<umap<string, Allocated>> cases,
                                           sptr_v<SortedVariable> params) {
    vector<vector<Allocated>> results(cases.size());
    for (unsigned long i = 0; i < cases.size(); i++) {
        for (unsigned long j = 0; j < params.size(); j++) {
            results[i].push_back(cases[i][params[j]->name]);
        }
    }

    return results;
}

string pred::allocToString(Allocated a) {
    if (a == Allocated::ALWAYS) {
        return "A";
    } else if (a == Allocated::NEVER) {
        return "N";
    } else {
        return "M";
    }
}

sptr_t<IndexReachability> pred::conj(sptr_t<IndexReachability> r1,
                                     sptr_t<IndexReachability> r2) {
    sptr_t<IndexReachability> result = r1->clone();
    result->conj(r2);

    return result;
}

sptr_t<IndexReachability> pred::conj(sptr_v<IndexReachability> vec) {
    sptr_t<IndexReachability> result;

    if (vec.empty()) {
        return result;
    }

    result = vec[0]->clone();
    for (unsigned long i = 1; i < vec.size(); i++) {
        result->conj(vec[i]);
    }

    return result;
}

sptr_t<IndexReachability> pred::varToIndex(sptr_t<StringReachability> reach,
                                           sptr_v<SortedVariable> params) {
    umap<string, unsigned long> paramMap;
    for (unsigned long i = 0; i < params.size(); i++) {
        paramMap[params[i]->name] = i;
    }

    return reach->toIndexReachability(paramMap);
}

sptr_v<IndexReachability> pred::varToIndex(sptr_v<StringReachability> cases,
                                           sptr_v<SortedVariable> params) {
    sptr_v<IndexReachability> result;

    umap<string, unsigned long> paramMap;
    for (unsigned long i = 0; i < params.size(); i++) {
        paramMap[params[i]->name] = i;
    }

    for (unsigned long i = 0; i < cases.size(); i++) {
        result.push_back(cases[i]->toIndexReachability(paramMap));
    }

    return result;
}

sptr_t<StringReachability> pred::disj(sptr_t<StringReachability> reach,
                                      sptr_t<IndexReachability> idxReach,
                                      sptr_v<Term> args) {
    sptr_t<StringReachability> result = reach->clone();

    for (unsigned long i = 0; i < args.size(); i++) {
        for (unsigned long j = 0; j < args.size(); j++) {
            if (idxReach->find(i, j)) {
                result->link(args[i]->toString(), args[j]->toString());
            }
        }
    }

    return result;
}