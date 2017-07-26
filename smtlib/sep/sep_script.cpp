#include "sep_script.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

Script::Script(sptr_v<Command>& commands) {
    this->commands.insert(this->commands.end(), commands.begin(), commands.end());
}

void Script::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string Script::toString() {
    stringstream ss;
    for (auto commandIt = commands.begin(); commandIt != commands.end(); commandIt++) {
        ss << (*commandIt)->toString() << "\n";
    }
    return ss.str();
}