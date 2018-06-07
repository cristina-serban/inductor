#include "pred_analysis.h"

using namespace std;
using namespace equiv;
using namespace reach;
using namespace pred;
using namespace smtlib::sep;

/* ================================ IndexAllocAnalysis ================================ */

IndexAllocAnalysisPtr IndexAllocAnalysis::clone() {
    auto copy = make_shared<IndexAllocAnalysis>();
    copy->predicates.insert(predicates.begin(), predicates.end());
    copy->base.insert(base.begin(), base.end());
    copy->inductive.insert(inductive.begin(), inductive.end());
    return copy;
}

bool IndexAllocAnalysis::equals(const IndexAllocAnalysisPtr& other) {
    if (!other)
        return false;

    if (base.size() != other->base.size() ||
        inductive.size() != other->inductive.size() ||
        predicates.size() != other->predicates.size()) {
        return false;
    }

    for (const auto& predEntry : predicates) {
        const string& name = predEntry.first;
        if (other->predicates.find(name) == other->predicates.end())
            return false;

        if (predEntry.second.size() != other->predicates[name].size())
            return false;

        for (size_t i = 0, sz = predEntry.second.size(); i < sz; i++) {
            if (predEntry.second[i] != other->predicates[name][i])
                return false;
        }
    }

    for (const auto& indEntry : inductive) {
        const string& name = indEntry.first;

        if (other->inductive.find(name) == other->inductive.end())
            return false;

        const IndexAllocInductiveMap& map = indEntry.second;
        const IndexAllocInductiveMap& otherMap = other->inductive[name];

        for (const auto& icaseEntry : map) {
            const InductiveCasePtr& icase = icaseEntry.first;

            if (otherMap.find(icase) == otherMap.end())
                return false;

            if (icaseEntry.second.size() != otherMap.at(icase).size())
                return false;

            for (size_t i = 0, sz = icaseEntry.second.size(); i < sz; i++) {
                if (icaseEntry.second[i] != otherMap.at(icase)[i])
                    return false;
            }
        }
    }

    for (const auto& baseEntry : base) {
        string name = baseEntry.first;

        if (other->base.find(name) == other->base.end())
            return false;

        const IndexAllocBaseMap& map = baseEntry.second;
        const IndexAllocBaseMap& otherMap = other->base[name];

        for (const auto& bcaseEntry : map) {
            BaseCasePtr bcase = bcaseEntry.first;

            if (otherMap.find(bcase) == otherMap.end())
                return false;

            if (bcaseEntry.second.size() != otherMap.at(bcase).size())
                return false;

            for (size_t i = 0, sz = bcaseEntry.second.size(); i < sz; i++) {
                if (bcaseEntry.second[i] != otherMap.at(bcase)[i])
                    return false;
            }
        }
    }

    return true;
}

/* ================================ IndexReachAnalysis ================================ */

IndexReachAnalysisPtr IndexReachAnalysis::clone() {
    auto copy = make_shared<IndexReachAnalysis>();

    for (const auto& predEntry : predicates) {
        copy->predicates[predEntry.first] = predEntry.second->clone();
    }

    for (const auto& baseEntry : base) {
        IndexReachBaseMap cloneBase;

        for (const auto& bcaseEntry : baseEntry.second) {
            cloneBase[bcaseEntry.first] = bcaseEntry.second->clone();
        }

        copy->base[baseEntry.first] = cloneBase;
    }

    for (const auto& indEntry : inductive) {
        IndexReachInductiveMap cloneInd;

        for (const auto& icaseEntry : indEntry.second) {
            cloneInd[icaseEntry.first] = icaseEntry.second->clone();
        }

        copy->inductive[indEntry.first] = cloneInd;
    }

    return copy;
}

bool IndexReachAnalysis::equals(const IndexReachAnalysisPtr& other) {
    if (!other)
        return false;

    if (base.size() != other->base.size() ||
        inductive.size() != other->inductive.size() ||
        predicates.size() != other->predicates.size()) {
        return false;
    }

    for (auto& predEntry : predicates) {
        const string& name = predEntry.first;
        if (other->predicates.find(name) == other->predicates.end())
            return false;

        if (!predEntry.second->equals(other->predicates[predEntry.first]))
            return false;
    }

    for (const auto& indEntry : inductive) {
        const string& name = indEntry.first;

        if (other->inductive.find(name) == other->inductive.end())
            return false;

        const IndexReachInductiveMap& map = indEntry.second;
        const IndexReachInductiveMap& otherMap = other->inductive[name];

        for (const auto& icaseEntry : map) {
            InductiveCasePtr icase = icaseEntry.first;
            if (otherMap.find(icase) == otherMap.end())
                return false;

            if (!icaseEntry.second->equals(otherMap.at(icase)))
                return false;
        }
    }

    for (const auto& baseEntry : base) {
        const string& name = baseEntry.first;

        if (other->base.find(name) == other->base.end())
            return false;

        const IndexReachBaseMap& map = baseEntry.second;
        const IndexReachBaseMap& otherMap = other->base[name];

        for (const auto& bcaseEntry : map) {
            const BaseCasePtr& bcase = bcaseEntry.first;
            if (otherMap.find(bcase) == otherMap.end())
                return false;

            if (!bcaseEntry.second->equals(otherMap.at(bcase)))
                return false;
        }
    }

    return true;
}

/* ==================================== Utilities ===================================== */

string pred::allocToString(Allocated a) {
    if (a == Allocated::ALWAYS) {
        return "A";
    }

    if (a == Allocated::NEVER) {
        return "N";
    }

    return "M";
}

Allocated pred::conj(Allocated a1, Allocated a2) {
    if (a1 == a2) {
        return a1;
    }

    return Allocated::MAYBE;
}

Allocated pred::conj(const vector<Allocated>& vec) {
    bool always = true;
    bool never = true;

    for (const auto& elem : vec) {
        if (elem != Allocated::ALWAYS)
            always = false;

        if (elem != Allocated::NEVER)
            never = false;
    }

    Allocated value = Allocated::MAYBE;
    if (always)
        value = Allocated::ALWAYS;
    if (never)
        value = Allocated::NEVER;

    return value;
}

vector<Allocated> pred::conj(const vector<Allocated>& vec1, const vector<Allocated>& vec2) {
    vector<Allocated> result;

    if (vec1.size() != vec2.size()) {
        return result;
    }

    result = vec1;
    for (size_t i = 1, sz = vec2.size(); i < sz; i++) {
        result[i] = conj(result[i], vec2[i]);
    }

    return result;
}

vector<Allocated> pred::conj(const vector<vector<Allocated>>& vec) {
    vector<Allocated> result;

    if (vec.empty())
        return result;

    result = vec[0];
    for (size_t i = 1, szi = vec.size(); i < szi; i++) {
        for (size_t j = 0, szj = vec[i].size(); j < szj; j++) {
            result[j] = conj(result[j], vec[i][j]);
        }
    }

    return result;
}

IndexReachabilityPtr pred::conj(const IndexReachabilityPtr& r1, const IndexReachabilityPtr& r2) {
    IndexReachabilityPtr result = r1->clone();
    result->conj(r2);

    return result;
}

IndexReachabilityPtr pred::conj(const vector<IndexReachabilityPtr>& vec) {
    IndexReachabilityPtr result;

    if (vec.empty()) {
        return result;
    }

    result = vec[0]->clone();
    for (size_t i = 1, sz = vec.size(); i < sz; i++) {
        result->conj(vec[i]);
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

Allocated pred::disj(const vector<Allocated>& vec) {
    bool never = true;

    for (auto& elem : vec) {
        if (elem == Allocated::ALWAYS)
            return Allocated::ALWAYS;

        if (elem != Allocated::NEVER)
            never = false;
    }

    return never ? Allocated::NEVER : Allocated::MAYBE;
}

vector<Allocated> pred::disj(const vector<Allocated>& vec1, const vector<Allocated>& vec2) {
    vector<Allocated> result;

    if (vec1.size() != vec2.size()) {
        return result;
    }

    result = vec1;
    for (size_t i = 1, sz = vec2.size(); i < sz; i++) {
        result[i] = disj(result[i], vec2[i]);
    }

    return result;
}

vector<Allocated> pred::disj(const vector<vector<Allocated>>& vec) {
    vector<Allocated> result;
    if (vec.empty())
        return result;

    result = vec[0];
    for (size_t i = 1, szi = vec.size(); i < szi; i++) {
        for (size_t j = 0, szj = vec[i].size(); j < szj; j++) {
            result[j] = disj(result[j], vec[i][j]);
        }
    }

    return result;
}

StringReachabilityPtr pred::disj(const StringReachabilityPtr& reach,
                                 const IndexReachabilityPtr& idxReach,
                                 const vector<TermPtr>& args) {
    StringReachabilityPtr result = reach->clone();

    for (size_t i = 0, szi = args.size(); i < szi; i++) {
        for (size_t j = 0, szj = args.size(); j < szj; j++) {
            if (idxReach->find(i, j)) {
                result->link(args[i]->toString(), args[j]->toString());
            }
        }
    }

    return result;
}

vector<vector<Allocated>> pred::varToIndex(const vector<unordered_map<string, Allocated>>& cases,
                                           const vector<smtlib::sep::SortedVariablePtr>& params) {
    vector<vector<Allocated>> results(cases.size());

    for (size_t i = 1, sz = cases.size(); i < sz; i++) {
        for (const auto& param : params) {
            results[i].push_back(cases[i].at(param->name));
        }
    }

    return results;
}


IndexReachabilityPtr pred::varToIndex(const StringReachabilityPtr& reach,
                                      const vector<SortedVariablePtr>& params) {
    StringToIndexMap paramMap;

    for (size_t i = 0, sz = params.size(); i < sz; i++) {
        paramMap[params[i]->name] = i;
    }

    return reach->toIndexReachability(paramMap);
}

vector<IndexReachabilityPtr> pred::varToIndex(const vector<StringReachabilityPtr>& cases,
                                              const vector<SortedVariablePtr>& params) {
    vector<IndexReachabilityPtr> result;

    StringToIndexMap paramMap;
    for (size_t i = 0, sz = params.size(); i < sz; i++) {
        paramMap[params[i]->name] = i;
    }

    for (const auto& caseReach : cases) {
        result.push_back(caseReach->toIndexReachability(paramMap));
    }

    return result;
}
