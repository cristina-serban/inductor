#include "ast_sort.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

Sort::Sort(sptr_t<SimpleIdentifier> identifier,
           sptr_v<Sort>& args) : identifier(identifier) {
    this->args.insert(this->args.end(), args.begin(), args.end());
}

bool Sort::hasArgs() {
    return !args.empty();
}

void Sort::accept(Visitor0* visitor) {
     visitor->visit(shared_from_this());
}

string Sort::toString() {
    if(!hasArgs()) {
        return identifier->toString();
    } else {
        stringstream ss;
        ss << "(" << identifier->toString() << " ";

        for (auto argIt = args.begin(); argIt != args.end(); argIt++) {
            if(argIt != args.begin())
                ss << " ";
            ss << (*argIt)->toString();
        }

        ss << ")";
        return ss.str();
    }
}