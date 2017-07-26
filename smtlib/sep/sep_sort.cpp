#include "sep_sort.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

Sort::Sort(string name, sptr_v<Sort>& args) : name(name) {
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
        return name;
    } else {
        stringstream ss;
        ss << "(" << name << " ";

        for (auto argIt = args.begin(); argIt != args.end(); argIt++) {
            if(argIt != args.begin())
                ss << " ";
            ss << (*argIt)->toString();
        }

        ss << ")";
        return ss.str();
    }
}