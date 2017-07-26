#include "sep_s_expr.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

void CompSExpression::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string CompSExpression::toString() {
    stringstream ss;
    ss << "(";
    for (auto exprIt = exprs.begin(); exprIt != exprs.end(); exprIt++) {
        if(exprIt != exprs.begin())
            ss << " ";
        ss << (*exprIt)->toString();
    }
    ss <<")";
    return ss.str();
}