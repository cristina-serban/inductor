#include "reach_string.h"

#include <algorithm>
#include <sstream>

using namespace std;
using namespace reach;

bool StringReachability::add(string x) {
    if (map.find(x) != map.end())
        return false;

    vector<string> vec;
    vec.push_back(x);
    map[x] = vec;

    return true;
}

bool StringReachability::link(string x, string y) {
    if (map.find(x) == map.end() || std::find(map[x].begin(), map[x].end(), y) != map[x].end()) {
        return false;
    }

    map[x].push_back(y);
    close();

    return true;
}

bool StringReachability::unlink(string x, string y) {
    if (map.find(x) == map.end() || std::find(map[x].begin(), map[x].end(), y) == map[x].end()) {
        return false;
    }

    map[x].erase(std::remove(map[x].begin(), map[x].end(), y), map[x].end());

    return true;
}

vector<string> StringReachability::find(string x) {
    return map[x];
}

vector<string> StringReachability::keys() {
    vector<string> result;
    for (auto it = map.begin(); it != map.end(); it++) {
        result.push_back((*it).first);
    }

    return result;
}

bool StringReachability::fill(vector<string> vec) {
    for (auto it = vec.begin(); it != vec.end(); it++) {
        if (!add(*it))
            return false;
    }

    return true;
}

bool StringReachability::find(string x, string y) {
    if (map.find(x) == map.end()) {
        return false;
    }

    return std::find(map[x].begin(), map[x].end(), y) != map[x].end();
}

umap<string, vector<string>> StringReachability::copyMap() {
    umap<string, vector<string>> result;
    result.insert(map.begin(), map.end());
    return result;
};

bool StringReachability::equalsMap(umap<string, vector<string>> other) {
    if (map.size() != other.size())
        return false;

    for (auto it = map.begin(); it != map.end(); it++) {
        if (other.find((*it).first) == other.end())
            return false;

        vector<string> otherVec = other[(*it).first];

        if ((*it).second.size() != otherVec.size())
            return false;

        for (unsigned long i = 0; i < (*it).second.size(); i++) {
            if (std::find(otherVec.begin(), otherVec.end(), (*it).second[i]) == otherVec.end())
                return false;
        }

        for (unsigned long i = 0; i < otherVec.size(); i++) {
            if (std::find((*it).second.begin(), (*it).second.end(), otherVec[i]) == (*it).second.end())
                return false;
        }
    }

    return true;
}

void StringReachability::close() {
    umap<string, vector<string>> copy;
    do {
        copy = copyMap();
        for (auto it = map.begin(); it != map.end(); it++) {
            vector<string> trans;
            for (unsigned long i = 0; i < (*it).second.size(); i++) {
                trans.insert(trans.begin(), map[(*it).second[i]].begin(), map[(*it).second[i]].end());
            }

            for (unsigned long i = 0; i < trans.size(); i++) {
                link((*it).first, trans[i]);
            }
        }

    } while (!equalsMap(copy));
}

sptr_t<StringReachability> StringReachability::clone() {
    sptr_t<StringReachability> result = make_shared<StringReachability>();
    result->map = copyMap();
    return result;
}

sptr_t<IndexReachability> StringReachability::toIndexReachability(umap<string, unsigned long> params) {
    sptr_t<IndexReachability> result = make_shared<IndexReachability>();

    for (unsigned long i = 0; i < params.size(); i++) {
        result->add();
    }

    for (auto it = map.begin(); it != map.end(); it++) {
        if (params.find((*it).first) == params.end())
            continue;

        unsigned long pos1 = params[(*it).first];

        for (auto itt = (*it).second.begin(); itt != (*it).second.end(); itt++) {
            if (params.find(*itt) == params.end())
                continue;

            unsigned long pos2 = params[*itt];
            result->link(pos1, pos2);
        }
    }

    return result;
}

std::string StringReachability::toString() {
    stringstream ss;
    ss << "{";

    bool first = true;
    for (auto i = map.begin(); i != map.end(); i++) {
        for (unsigned long j = 0; j < map[(*i).first].size(); j++) {
            if (!first) {
                ss << ", ";
            } else {
                first = false;
            }

            ss << "(" << (*i).first << ", " << map[(*i).first][j] << ")";
        }
    }

    ss << "}";
    return ss.str();
}