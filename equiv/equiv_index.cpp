#include "equiv_index.h"

#include <sstream>

using namespace std;
using namespace equiv;

long IndexEquivalence::add() {
    unsigned long newClass = classes.size() + 1;
    classes.push_back(newClass);
    return newClass;
}

long IndexEquivalence::find(unsigned long i) {
    if (i >= classes.size())
        return -1;

    return classes[i];
}

long IndexEquivalence::unite(unsigned long i, unsigned long j) {
    long iclass = find(i);
    long jclass = find(j);

    if (iclass < 0 || jclass < 0)
        return -1;

    for (size_t k = 0, sz = classes.size(); k < sz; k++) {
        if (classes[k] == jclass)
            classes[k] = iclass;
    }

    return iclass;
}

string IndexEquivalence::toString() {
    stringstream ss;

    for (size_t i = 0, szi = classes.size(); i < szi; i++) {
        if (i != 0)
            ss << "; ";

        ss << (i + 1) << " => {";

        long iclass = find(i);
        bool first = true;

        for (size_t j = 0, szj = classes.size(); j < szj; j++) {
            if (find(j) == iclass) {
                if (first) {
                    first = false;
                } else {
                    ss << ", ";
                }

                ss << (j + 1);
            }
        }
        ss << "}";
    }

    return ss.str();
}
