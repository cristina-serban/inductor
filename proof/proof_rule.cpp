#include "proof_rule.h"
#include "proof_state.h"

using namespace std;
using namespace proof;

string proof::toString(Rule rule) {
    switch (rule) {
        case NONE:
            return "";
        case CALL:
            return "CALL";
        case INDUCTION:
            return "IND";
        case UNFOLD_LEFT:
            return "UL";
        case UNFOLD_RIGHT:
            return "UR";
        case REDUCE:
            return "RED";
        case SPLIT:
            return "SEP";
        case SIMPLIFY:
            return "SIM";
        case SUBSTITUTE:
            return "SUB";
        case SMT_TRUE:
            return "T-SMT";
        case SMT_FALSE:
            return "F-SMT";
        default:
            return "";
    }
}

ReduceApplication::ReduceApplication() : newPair(make_shared<Pair>()) {
    rule = Rule::REDUCE;
}