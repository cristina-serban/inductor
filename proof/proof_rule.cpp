#include "proof_rule.h"

using namespace std;
using namespace proof;

string proof::toString(Rule rule) {
    switch (rule) {
        case NONE:
            return "";
        case INFINITE_DESCENT:
            return "ID";
        case LEFT_UNFOLD:
            return "LU";
        case RIGHT_UNFOLD:
            return "RU";
        case REDUCE:
            return "RD";
        case SPLIT:
            return "SP";
        case AXIOM:
            return "AX";
        case COUNTEREXAMPLE:
            return "CE";
        default:
            return "";
    }
}
