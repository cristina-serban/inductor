#include "proof_tree.h"

#include "util/global_values.h"

#include <sstream>

using namespace std;
using namespace proof;
using namespace smtlib;


/* ===================================== ProofNode ===================================== */
ProofNodePtr ProofNode::getRoot() {
    if (!parent) {
        return shared_from_this();
    }

    ProofNodePtr root = parent;
    while (root->parent) {
        root = root->parent;
    }
    return root;

}

vector<size_t> ProofNode::getPath() {
    vector<size_t> path;

    if (parent) {
        ProofNodePtr current = shared_from_this();
        ProofNodePtr par = dynamic_pointer_cast<PairNode>(parent);

        while (par) {
            PairNodePtr pnode = dynamic_pointer_cast<PairNode>(par);

            for (size_t i = 0, n = pnode->children.size(); i < n; i++) {
                if (pnode->children[i] == current) {
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
ProofNodePtr TrueLeaf::clone() {
    return make_shared<TrueLeaf>();
}

string TrueLeaf::toString() {
    return PROOF_TRUE;
}

string TrueLeaf::toLatexString() {
    stringstream ss;

    if (!parent) {
        ss << "\\[";
    }

    ss << "\\mathbf{" << PROOF_TRUE << "}";

    if (!parent) {
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
ProofNodePtr FalseLeaf::clone() {
    return make_shared<FalseLeaf>();
}

string FalseLeaf::toString() {
    return PROOF_FALSE;
}

string FalseLeaf::toLatexString() {
    stringstream ss;

    if (!parent) {
        ss << "\\[";
    }

    ss << "\\mathbf{" << PROOF_FALSE << "}";

    if (!parent) {
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
ProofNodePtr InfDescentLeaf::clone() {
    return make_shared<InfDescentLeaf>();
}

string InfDescentLeaf::toString() {
    return PROOF_IND;
}

string InfDescentLeaf::toLatexString() {
    stringstream ss;

    if (!parent) {
        ss << "\\[";
    }

    ss << "\\mathbf{" << PROOF_IND << "}";

    if (!parent) {
        ss << "\\]";
    }

    return ss.str();
}

bool InfDescentLeaf::isClosed() {
    return true;
}

bool InfDescentLeaf::isProof() {
    return true;
}

/* ===================================== PairNode ===================================== */
PairNode::PairNode(const PairPtr& pair, Rule rule, const vector<ProofNodePtr>& children)
        : pair(pair), rule(rule) {
    this->children.insert(this->children.begin(), children.begin(), children.end());
}

void PairNode::add(const ProofNodePtr& child) {
    child->parent = shared_from_this();
    children.push_back(child);
}

void PairNode::add(const vector<ProofNodePtr>& children) {
    for (const auto& child : children) {
        child->parent = shared_from_this();
        this->children.push_back(child);
    }
}

ProofNodePtr PairNode::clone() {
    PairNodePtr newNode = make_shared<PairNode>(pair, rule);

    for (const auto& child : children) {
        ProofNodePtr newChild = child->clone();
        newChild->parent = newNode;
        newNode->children.push_back(newChild);
    }

    return newNode;
}

string PairNode::toString() {
    stringstream ss;
    ss << pair->toString() << endl;

    for (const auto& child : children) {
        ss << child->toString() << endl;
    }

    return ss.str();
}

string PairNode::toLatexString() {
    stringstream ss;

    if (!parent) {
        ss << "\\[";
    }

    ss << "\\inferrule*[Left=" << proof::toString(rule) << ", rightskip=-1em]{";

    // Children
    for (size_t i = 0, sz = children.size(); i < sz; i++) {
        if (i != 0) {
            ss << " \\\\ ";
        }

        ss << children[i]->toLatexString();
    }

    ss << "} {";

    // Current pair
    ss << "\\texttt{" << pair->left->toString() << "} \\vdash ";

    if (pair->right.empty())
        ss << "\\{ \\}";

    for (size_t i = 0, sz = pair->right.size(); i < sz; i++) {
        if (i != 0) {
            ss << " \\lor ";
        }
        ss << "\\texttt{" << pair->right[i]->toString() << "}";
    }

    ss << "}";

    if (!parent) {
        ss << "\\]";
    }

    return ss.str();
}

ProofNodePtr PairNode::getNodeFromPath(const vector<size_t>& path) {
    ProofNodePtr null;
    ProofNodePtr result = shared_from_this();

    if (path.empty()) {
        return result;
    }

    size_t i = 0;
    while (i < path.size()) {
        PairNodePtr pairNode = dynamic_pointer_cast<PairNode>(result);
        if (path[i] >= pairNode->children.size())
            return null;

        result = pairNode->children[path[i]];
        i++;
    }

    return result;
}

bool PairNode::isClosed() {
    for (const auto& child : children) {
        if (!child->isClosed())
            return false;
    }

    return true;
}

bool PairNode::isProof() {
    if (!isClosed()) {
        return false;
    }

    for (const auto& child : children) {
        if (!child->isProof())
            return false;
    }

    return true;
}
