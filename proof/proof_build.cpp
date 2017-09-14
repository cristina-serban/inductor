#include "proof_build.h"

#include <sstream>

using namespace std;
using namespace proof;

/* =================================== TrueStmtLeaf =================================== */

ProofNodePtr TrueStmtLeaf::toProofNode() {
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

std::string TrueStmtLeaf::toString(size_t indent) {
    stringstream ss;
    ss << "\n";

    for (size_t i = 0; i < indent; ++i) {
        ss << "    ";
    }

    ss << "True";
    return ss.str();
}

/* ================================== FalseStmtLeaf =================================== */

ProofNodePtr FalseStmtLeaf::toProofNode() {
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

std::string FalseStmtLeaf::toString(size_t indent) {
    stringstream ss;
    ss << "\n";

    for (size_t i = 0; i < indent; ++i) {
        ss << "    ";
    }

    ss << "False";
    return ss.str();
}

/* ================================ InfDescentStmtLeaf ================================ */

ProofNodePtr InfDescentStmtLeaf::toProofNode() {
    return make_shared<InfDescentLeaf>();
}

bool InfDescentStmtLeaf::isRoot() {
    return false;
}

bool InfDescentStmtLeaf::isClosed() {
    return true;
}

bool InfDescentStmtLeaf::isProof() {
    return true;
}

bool InfDescentStmtLeaf::isFailed() {
    return false;
}

std::string InfDescentStmtLeaf::toString(size_t indent) {
    stringstream ss;
    ss << "\n";

    for (size_t i = 0; i < indent; ++i) {
        ss << "    ";
    }

    ss << "*";
    return ss.str();
}

/* =================================== PairStmtNode =================================== */

PairStmtNode::PairStmtNode(const PairPtr& pair,
                           const std::vector<PairPtr>& workset)
        : pair(pair) {
    this->workset.insert(this->workset.begin(), workset.begin(), workset.end());
}

PairStmtNode::PairStmtNode(const PairPtr& pair,
                           const std::vector<PairPtr>& workset,
                           const RuleNodePtr& parent)
        : pair(pair), parent(parent) {
    this->workset.insert(this->workset.begin(), workset.begin(), workset.end());
}

PairStmtNode::PairStmtNode(const PairPtr& pair,
                           const std::vector<PairPtr>& workset,
                           const RuleNodePtr& parent,
                           const std::vector<RuleNodePtr>& children)
        : pair(pair), parent(parent) {
    this->workset.insert(this->workset.begin(), workset.begin(), workset.end());
    this->children.insert(this->children.begin(), children.begin(), children.end());
}

ProofNodePtr PairStmtNode::toProofNode() {
    // fixme Placeholder, not how this should work
    return make_shared<PairNode>(pair);
}

bool PairStmtNode::isRoot() {
    return !parent;
}

bool PairStmtNode::isClosed() {
    if (children.empty())
        return false;

    for (const auto& child : children) {
        if (!child->isClosed())
            return false;
    }

    return true;
}

bool PairStmtNode::isProof() {
    if (children.empty())
        return false;

    for (const auto& child : children) {
        if (!child->isProof())
            return false;
    }

    return true;
}

bool PairStmtNode::isFailed() {
    if (children.empty())
        return false;

    for (auto& child : children) {
        if (child->isFailed())
            return true;
    }

    return false;
}

std::string PairStmtNode::toString(size_t indent) {
    stringstream ss;
    ss << "\n";

    for (size_t i = 0; i < indent; ++i) {
        ss << "    ";
    }

    ss << pair->toString();

    for (const auto& child : children) {
        ss << child->toString(indent + 1);
    }

    return ss.str();
}

/* ===================================== RuleNode ===================================== */

bool RuleNode::isClosed() {
    for (size_t i = 0, n = children.size(); i < n; i++) {
        if (children[i]->isClosed())
            return true;
    }

    return false;
}

bool RuleNode::isProof() {
    for (size_t i = 0, n = children.size(); i < n; i++) {
        if (children[i]->isProof())
            return true;
    }

    return false;
}

bool RuleNode::isFailed() {
    for (size_t i = 0, n = children.size(); i < n; i++) {
        if (!children[i]->isFailed())
            return false;
    }

    return true;
}

std::string RuleNode::toString(size_t indent) {
    stringstream ss;
    ss << "\n";

    for (size_t i = 0; i < indent; ++i) {
        ss << "    ";
    }

    ss << proof::toString(rule);

    for (const auto& child : children) {
        ss << child->toString(indent + 1);
    }

    return ss.str();
}
