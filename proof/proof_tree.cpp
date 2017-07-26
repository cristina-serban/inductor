#include "proof_tree.h"

#include "util/global_values.h"

#include <sstream>

using namespace std;
using namespace proof;
using namespace smtlib;



/* ===================================== ProofNode ===================================== */
sptr_t<ProofNode> ProofNode::getRoot() {
    if(!parent) {
        return shared_from_this();
    } else {
        sptr_t<ProofNode> root = parent;
        while(root->parent) {
            root = root->parent;
        }
        return root;
    }
}

vector<size_t> ProofNode::getPath() {
    vector<size_t> path;
    if(parent) {
        sptr_t<ProofNode> current = shared_from_this();
        sptr_t<ProofNode> par = dynamic_pointer_cast<PairNode>(parent);

        while(par) {
            sptr_t<PairNode> pnode = dynamic_pointer_cast<PairNode>(par);

            for(size_t i = 0, n = pnode->children.size(); i < n; i++) {
                if(pnode->children[i] == current) {
                    path.insert(path.begin(), i);
                    break;
                }
            }

            current = par;
            par = par->parent;
        }
    }

    return path;
}

/* ===================================== TrueNode ===================================== */
sptr_t<ProofNode> TrueLeaf::clone() {
    return make_shared<TrueLeaf>();
}

string TrueLeaf::toString() {
    return PROOF_TRUE;
}

string TrueLeaf::toLatexString() {
    stringstream ss;

    if(!parent) {
        ss << "\\[";
    }

    ss << "\\mathbf{" << PROOF_TRUE << "}";

    if(!parent) {
        ss << "\\]";
    }

    return ss.str();
}

bool TrueLeaf::isClosed() {
    return true;
}

bool TrueLeaf::isProof() {
    return true;
}

/* ===================================== FalseLeaf ==================================== */
sptr_t<ProofNode> FalseLeaf::clone() {
    return make_shared<FalseLeaf>();
}

string FalseLeaf::toString() {
    return PROOF_FALSE;
}

string FalseLeaf::toLatexString() {
    stringstream ss;

    if(!parent) {
        ss << "\\[";
    }

    ss << "\\mathbf{" << PROOF_FALSE << "}";

    if(!parent) {
        ss << "\\]";
    }

    return ss.str();
}

bool FalseLeaf::isClosed() {
    return true;
}

bool FalseLeaf::isProof() {
    return false;
}

/* =================================== InductionLeaf ================================== */
sptr_t<ProofNode> InductionLeaf::clone() {
    return make_shared<InductionLeaf>();
}

string InductionLeaf::toString() {
    return PROOF_IND;
}

string InductionLeaf::toLatexString() {
    stringstream ss;

    if(!parent) {
        ss << "\\[";
    }

    ss << "\\mathbf{" << PROOF_IND << "}";

    if(!parent) {
        ss << "\\]";
    }

    return ss.str();
}

bool InductionLeaf::isClosed() {
    return true;
}

bool InductionLeaf::isProof() {
    return true;
}

/* ===================================== PairNode ===================================== */
PairNode::PairNode(sptr_t<Pair> pair, Rule rule, sptr_v<ProofNode> children)
    : pair(pair), rule(rule) {
    this->children.insert(this->children.begin(), children.begin(), children.end());
}

void PairNode::add(sptr_t<ProofNode> child) {
    child->parent = shared_from_this();
    children.push_back(child);
}

void PairNode::add(sptr_v<ProofNode> children) {
    for(size_t i = 0, n = children.size(); i < n; i++) {
        children[i]->parent = shared_from_this();
        children.push_back(children[i]);
    }
}

sptr_t<ProofNode> PairNode::clone() {
    sptr_t<PairNode> newNode = make_shared<PairNode>(pair, rule);

    for(auto it = children.begin(); it != children.end(); it++) {
        sptr_t<ProofNode> newChild = (*it)->clone();
        newChild->parent = newNode;
        newNode->children.push_back(newChild);
    }

    return newNode;
}

string PairNode::toString() {
    stringstream ss;
    ss << pair->toString() << endl;

    for(auto it = children.begin(); it != children.end(); it++) {
        ss << (*it)->toString() << endl;
    }

    return ss.str();
}

string PairNode::toLatexString() {
    stringstream ss;

    if(!parent) {
        ss << "\\[";
    }

    ss << "\\inferrule*[Left=" << proof::toString(rule) << ", rightskip=-1em]{";

    // Children
    bool first = true;
    for(auto it = children.begin(); it != children.end(); it++) {
        if(first) {
            first = false;
        } else {
            ss << " \\\\ ";
        }
        ss << (*it)->toLatexString();
    }

    ss << "} {";

    // Current pair
    ss << "\\texttt{" << pair->left->toString() << "} \\vdash ";

    if(pair->right.empty())
        ss << "\\{ \\}";

    first = true;
    for(auto it = pair->right.begin(); it != pair->right.end(); it++) {
        if(first) {
            first = false;
        } else {
            ss << " \\lor ";
        }
        ss << "\\texttt{" << (*it)->toString() << "}";
    }

    ss << "}";

    if(!parent) {
        ss << "\\]";
    }

    return ss.str();
}

sptr_t<ProofNode> PairNode::getNode(vector<size_t> path) {
    sptr_t<ProofNode> null;
    sptr_t<ProofNode> result = shared_from_this();

    if(path.empty()) {
        return result;
    }

    size_t i = 0;
    while(i < path.size()) {
        sptr_t<PairNode> pairNode = dynamic_pointer_cast<PairNode>(result);
        if (path[i] >= pairNode->children.size())
            return null;

        result = pairNode->children[path[i]];
        i++;
    }

    return result;
}

bool PairNode::isClosed() {
    for(size_t i = 0, n = children.size(); i < n; i++) {
        if(!children[i]->isClosed())
            return false;
    }

    return true;
}

bool PairNode::isProof() {
    if(!isClosed()) {
        return false;
    }

    for(size_t i = 0, n = children.size(); i < n; i++) {
        if(!children[i]->isProof())
            return false;
    }

    return true;
}