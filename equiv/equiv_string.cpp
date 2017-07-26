#include "equiv_string.h"

#include <sstream>

using namespace std;
using namespace equiv;

void Set::init(string data) {
    sptr_t<Node> null;
    head = make_shared<Node>(data, null, shared_from_this());
    tail = head;
    length = 1;
}

string Set::toString() {
    stringstream ss;
    ss << "{";

    bool first = true;
    sptr_t<Node> p = head;
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

sptr_t<Node> StringEquivalence::makeSet(string data) {
    sptr_t<Set> set = make_shared<Set>();
    set->init(data);

    return set->head;
}

sptr_t<Node> StringEquivalence::findSet(sptr_t<Node> x) {
    return x->parent->head;
}

sptr_t<Node> StringEquivalence::unionSet(sptr_t<Node> x, sptr_t<Node> y) {
    sptr_t<Node> n1 = findSet(x);
    sptr_t<Node> n2 = findSet(y);

    if (n1->data == n2->data)
        return n1;

    sptr_t<Set> s1 = n1->parent;
    sptr_t<Set> s2 = n2->parent;

    if (s1->length < s2->length) {
        sptr_t<Set> aux = s1;
        s1 = s2;
        s2 = aux;
    }

    s1->tail->next = s2->head;
    s1->tail = s2->tail;
    s1->length += s2->length;

    sptr_t<Node> p = s2->head;
    while (p) {
        p->parent = s1;
        p = p->next;
    }

    return s1->head;
}

bool StringEquivalence::add(string data) {
    if (map.find(data) != map.end())
        return false;

    map[data] = makeSet(data);
    return true;
}

sptr_t<Node> StringEquivalence::find(string x) {
    return findSet(map[x]);
}

bool StringEquivalence::unite(string x, string y) {
    if(map.find(x) == map.end() || map.find(y) == map.end()) {
        return false;
    }

    unionSet(map[x], map[y]);
    return true;
}

string StringEquivalence::toString() {
    stringstream ss;

    for(auto it = map.begin(); it != map.end(); it++) {
        ss << (*it).first << " -> " << (*it).second->parent->toString() << "; ";
    }

    return ss.str();
}

sptr_t<IndexEquivalence> StringEquivalence::toIndexEquivalence(umap<string, unsigned long> params) {
    sptr_t<IndexEquivalence> match = make_shared<IndexEquivalence>();

    for(int i = 0; i < params.size(); i++) {
        match->add();
    }

    for(auto it = params.begin(); it != params.end(); it++) {
        string name = (*it).first;
        unsigned long pos = (*it).second;

        sptr_t<Node> p = map[name]->parent->head;
        while(p) {
            if(params.find(p->data) != params.end()) {
                match->unite(pos, params[p->data]);
            }
            p = p->next;
        }
    }

    return match;
}