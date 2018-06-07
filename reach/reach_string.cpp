#include "reach_string.h"

#include <algorithm>
#include <sstream>

using namespace std;
using namespace reach;

bool StringReachability::add(const string& x) {
    if (map.find(x) != map.end())
        return false;

    vector<string> vec;
    vec.push_back(x);
    map[x] = vec;

    return true;
}

bool StringReachability::link(const string& x, const string& y) {
    if (map.find(x) == map.end() || std::find(map[x].begin(), map[x].end(), y) != map[x].end()) {
        return false;
    }

    map[x].push_back(y);
    close();

    return true;
}

bool StringReachability::unlink(const string& x, const string& y) {
    if (map.find(x) == map.end() || std::find(map[x].begin(), map[x].end(), y) == map[x].end()) {
        return false;
    }

    map[x].erase(std::remove(map[x].begin(), map[x].end(), y), map[x].end());

    return true;
}

vector<string> StringReachability::find(const string& x) {
    return map[x];
}

vector<string> StringReachability::keys() {
    vector<string> result;
    for (const auto& entry : map) {
        result.push_back(entry.first);
    }

    return result;
}

bool StringReachability::fill(const vector<string>& vec) {
    for (const string& elem : vec) {
        if (!add(elem))
            return false;
    }

    return true;
}

bool StringReachability::find(const string& x, const string& y) {
    if (map.find(x) == map.end()) {
        return false;
    }

    return std::find(map[x].begin(), map[x].end(), y) != map[x].end();
}

void StringReachability::close() {
    unordered_map<string, vector<string>> copy;
    do {
        copy = copyMap();
        for (const auto& entry : map) {
            vector<string> trans;
            for (const string& elem : entry.second) {
                trans.insert(trans.begin(), map[elem].begin(), map[elem].end());
            }

            for (const auto& tr : trans) {
                link(entry.first, tr);
            }
        }

    } while (!equalsMap(copy));
}

StringReachabilityPtr StringReachability::clone() {
    StringReachabilityPtr result = make_shared<StringReachability>();
    result->map = copyMap();
    return result;
}

IndexReachabilityPtr StringReachability::toIndexReachability(const StringToIndexMap& params) {
    IndexReachabilityPtr result = make_shared<IndexReachability>();

    for (size_t i = 0, sz = params.size(); i < sz; i++) {
        result->add();
    }

    for (const auto& entry : map) {
        if (params.find(entry.first) == params.end())
            continue;

        unsigned long pos1 = params.at(entry.first);

        for (const string& elem : entry.second) {
            if (params.find(elem) == params.end())
                continue;

            unsigned long pos2 = params.at(elem);
            result->link(pos1, pos2);
        }
    }

    return result;
}

std::string StringReachability::toString() {
    stringstream ss;
    ss << "{";

    bool first = true;
    for (const auto& entry : map) {
        for (const string& elem : entry.second) {
            if (!first) {
                ss << ", ";
            } else {
                first = false;
            }

            ss << "(" << entry.first << ", " << elem << ")";
        }
    }

    ss << "}";
    return ss.str();
}

unordered_map<string, vector<string>> StringReachability::copyMap() {
    unordered_map<string, vector<string>> result;
    result.insert(map.begin(), map.end());
    return result;
};

bool StringReachability::equalsMap(const unordered_map<string, vector<string>>& other) {
    if (map.size() != other.size())
        return false;

    for (const auto& entry : map) {
        if (other.find(entry.first) == other.end())
            return false;

        const vector<string>& otherVec = other.at(entry.first);

        if (entry.second.size() != otherVec.size())
            return false;

        for (const string& elem : entry.second) {
            if (std::find(otherVec.begin(), otherVec.end(), elem) == otherVec.end())
                return false;
        }

        for (const string& i : otherVec) {
            if (std::find(entry.second.begin(), entry.second.end(), i) == entry.second.end())
                return false;
        }
    }

    return true;
}
