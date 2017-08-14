#include "proof_rule.h"
#include "proof_state.h"

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
        default:
            return "";
    }
}
