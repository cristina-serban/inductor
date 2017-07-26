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

    for (unsigned long it = 0; it < classes.size(); it++) {
        if (classes[it] == jclass)
            classes[it] = iclass;
    }

    return iclass;
}

string IndexEquivalence::toString() {
    stringstream ss;

    bool first1 = true;
    for(unsigned long i = 0; i < classes.size(); i++) {
        if(first1) {
            first1 = false;
        } else {
            ss << "; ";
        }

        long iclass = find(i);

        ss << (i+1) << " => {";
        bool first2 = true;
        for(unsigned long j = 0; j < classes.size(); j++) {
            if(find(j) == iclass) {
                if(first2) {
                    first2 = false;
                } else {
                    ss << ", ";
                }

                ss << (j+1);
            }
        }
        ss << "}";
    }

    return ss.str();
}