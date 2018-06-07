#include "equiv_string.h"

#include <sstream>

using namespace std;
using namespace equiv;

/* ======================================= Set ======================================== */

void Set::init(const string& data) {
    NodePtr null;
    head = make_shared<Node>(data, null, shared_from_this());
    tail = head;
    length = 1;
}

string Set::toString() {
    stringstream ss;
    ss << "{";

    bool first = true;
    NodePtr p = head;
    while (p) {
        if(first) {
            first = false;
        } else {
            ss << ", ";
        }

        ss << p->data;
        p = p->next;
    }

    ss << "}";
    return ss.str();
}

/* ================================ StringEquivalence ================================= */

NodePtr StringEquivalence::makeSet(const string& data) {
    SetPtr set = make_shared<Set>();
    set->init(data);

    return set->head;
}

NodePtr StringEquivalence::findSet(const NodePtr& x) {
    return x->parent->head;
}

NodePtr StringEquivalence::unionSet(const NodePtr& x, const NodePtr& y) {
    NodePtr n1 = findSet(x);
    NodePtr n2 = findSet(y);

    if (n1->data == n2->data)
        return n1;

    SetPtr s1 = n1->parent;
    SetPtr s2 = n2->parent;

    if (s1->length < s2->length) {
        SetPtr aux = s1;
        s1 = s2;
        s2 = aux;
    }

    s1->tail->next = s2->head;
    s1->tail = s2->tail;
    s1->length += s2->length;

    NodePtr p = s2->head;
    while (p) {
        p->parent = s1;
        p = p->next;
    }

    return s1->head;
}

bool StringEquivalence::add(const string& data) {
    if (map.find(data) != map.end())
        return false;

    map[data] = makeSet(data);
    return true;
}

NodePtr StringEquivalence::find(const string& x) {
    return findSet(map[x]);
}

bool StringEquivalence::unite(const string& x, const string& y) {
    if(map.find(x) == map.end() || map.find(y) == map.end()) {
        return false;
    }

    unionSet(map[x], map[y]);
    return true;
}

string StringEquivalence::toString() {
    stringstream ss;

    for (const auto& entry : map) {
        ss << entry.first << " -> " << entry.second->parent->toString() << "; ";
    }

    return ss.str();
}

IndexEquivalencePtr StringEquivalence::toIndexEquivalence(const StringToIndexMap& params) {
    IndexEquivalencePtr match = make_shared<IndexEquivalence>();

    for(int i = 0; i < params.size(); i++) {
        match->add();
    }

    for(const auto& paramEntry : params) {
        const string& name = paramEntry.first;
        unsigned long pos = paramEntry.second;

        NodePtr p = map[name]->parent->head;
        while(p) {
            if(params.find(p->data) != params.end()) {
                match->unite(pos, params.at(p->data));
            }
            p = p->next;
        }
    }

    return match;
}
