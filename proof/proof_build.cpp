#include "proof_build.h"

#include <sstream>

using namespace std;
using namespace proof;

/* =================================== TrueStmtLeaf =================================== */

sptr_t<ProofNode> TrueStmtLeaf::toProofNode() {
    return make_shared<TrueLeaf>();
}

bool TrueStmtLeaf::isRoot() {
    return false;
}

bool TrueStmtLeaf::isClosed() {
    return true;
}

bool TrueStmtLeaf::isProof() {
    return true;
}

bool TrueStmtLeaf::isFailed() {
    return false;
}

std::string TrueStmtLeaf::toString(int indent) {
    stringstream ss;
    ss << "\n";
    for (int i = 0; i < indent; ++i) {
        ss << "    ";
    }
    ss << "True";
    return ss.str();
}

/* ================================== FalseStmtLeaf =================================== */

sptr_t<ProofNode> FalseStmtLeaf::toProofNode() {
    return make_shared<FalseLeaf>();
}

bool FalseStmtLeaf::isRoot() {
    return false;
}

bool FalseStmtLeaf::isClosed() {
    return true;
}

bool FalseStmtLeaf::isProof() {
    return false;
}

bool FalseStmtLeaf::isFailed() {
    return true;
}

std::string FalseStmtLeaf::toString(int indent) {
    stringstream ss;
    ss << "\n";
    for (int i = 0; i < indent; ++i) {
        ss << "    ";
    }
    ss << "False";
    return ss.str();
}

/* ================================ InductionStmtLeaf ================================= */

sptr_t<ProofNode> InductionStmtLeaf::toProofNode() {
    return make_shared<InductionLeaf>();
}

bool InductionStmtLeaf::isRoot() {
    return false;
}

bool InductionStmtLeaf::isClosed() {
    return true;
}

bool InductionStmtLeaf::isProof() {
    return true;
}

bool InductionStmtLeaf::isFailed() {
    return false;
}

std::string InductionStmtLeaf::toString(int indent) {
    stringstream ss;
    ss << "\n";
    for (int i = 0; i < indent; ++i) {
        ss << "    ";
    }
    ss << "*";
    return ss.str();
}

/* =================================== PairStmtNode =================================== */

PairStmtNode::PairStmtNode(sptr_t<Pair> pair, sptr_v<Pair> &workset) : pair(pair) {
    this->workset.insert(this->workset.begin(), workset.begin(), workset.end());
}

PairStmtNode::PairStmtNode(sptr_t<Pair> pair, sptr_v<Pair> &workset, sptr_t<RuleNode> parent)
    : pair(pair), parent(parent) {
    this->workset.insert(this->workset.begin(), workset.begin(), workset.end());
}

PairStmtNode::PairStmtNode(sptr_t<Pair> pair, sptr_v<Pair> &workset,
                           sptr_t<RuleNode> parent, sptr_v<RuleNode> &children)
    : pair(pair), parent(parent) {
    this->workset.insert(this->workset.begin(), workset.begin(), workset.end());
    this->children.insert(this->children.begin(), children.begin(), children.end());
}

sptr_t<ProofNode> PairStmtNode::toProofNode() {
    // fixme Placeholder, not how this should work
    return make_shared<PairNode>(pair);
}

bool PairStmtNode::isRoot() {
    return !parent;
}

bool PairStmtNode::isClosed() {
    if(children.empty())
        return false;

    for(size_t i = 0, n = children.size(); i < n; i++) {
        if(!children[i]->isClosed())
            return false;
    }

    return true;
}

bool PairStmtNode::isProof() {
    if(children.empty())
        return false;

    for(size_t i = 0, n = children.size(); i < n; i++) {
        if(!children[i]->isProof())
            return false;
    }

    return true;
}

bool PairStmtNode::isFailed() {
    if(children.empty())
        return false;

    for(size_t i = 0, n = children.size(); i < n; i++) {
        if(children[i]->isFailed())
            return true;
    }

    return false;
}

std::string PairStmtNode::toString(int indent) {
    stringstream ss;
    ss << "\n";
    for (int i = 0; i < indent; ++i) {
        ss << "    ";
    }
    ss << pair->toString();
    for (size_t i = 0, n = children.size(); i < n; ++i) {
        ss << children[i]->toString(indent + 1);
    }
    return ss.str();
}

/* ===================================== RuleNode ===================================== */

bool RuleNode::isClosed() {
    for(size_t i = 0, n = children.size(); i < n; i++) {
        if(children[i]->isClosed())
            return true;
    }

    return false;
}

bool RuleNode::isProof() {
    for(size_t i = 0, n = children.size(); i < n; i++) {
        if(children[i]->isProof())
            return true;
    }

    return false;
}

bool RuleNode::isFailed() {
    for(size_t i = 0, n = children.size(); i < n; i++) {
        if(!children[i]->isFailed())
            return false;
    }

    return true;
}

std::string RuleNode::toString(int indent) {
    stringstream ss;
    ss << "\n";
    for (int i = 0; i < indent; ++i) {
        ss << "    ";
    }
    ss << proof::toString(rule);
    for (size_t i = 0, n = children.size(); i < n; ++i) {
        ss << children[i]->toString(indent + 1);
    }
    return ss.str();
}