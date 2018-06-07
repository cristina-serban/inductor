#include "proof_tree.h"

#include <sstream>

using namespace std;
using namespace proof;

/* ===================================== StmtNode ===================================== */
void StmtNode::statusUpdate(Status status) {
    if(this->status != status) {
        this->status = status;

        if(parent) {
            parent->statusUpdate();
        }
    }
}

/* =================================== TrueStmtLeaf =================================== */
void TrueStmtLeaf::statusUpdate() {
    StmtNode::statusUpdate(Status::VALID);
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

bool TrueStmtLeaf::isUnfinished() {
    return false;
}

size_t TrueStmtLeaf::height() {
    return 1;
}

size_t TrueStmtLeaf::heightUnfoldLeft() {
    return 0;
}

size_t TrueStmtLeaf::heightSplit() {
    return 0;
}

size_t TrueStmtLeaf::count() {
    return 1;
}

size_t TrueStmtLeaf::rcount() {
    return 0;
}

size_t TrueStmtLeaf::scount() {
    return 1;
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
void FalseStmtLeaf::statusUpdate() {
    StmtNode::statusUpdate(Status::INVALID);
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

bool FalseStmtLeaf::isUnfinished() {
    return false;
}

size_t FalseStmtLeaf::height() {
    return 0;
}

size_t FalseStmtLeaf::heightUnfoldLeft() {
    return 0;
}

size_t FalseStmtLeaf::heightSplit() {
    return 0;
}

size_t FalseStmtLeaf::count() {
    return 0;
}

size_t FalseStmtLeaf::rcount() {
    return 0;
}

size_t FalseStmtLeaf::scount() {
    return 0;
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
void InfDescentStmtLeaf::statusUpdate() {
    StmtNode::statusUpdate(Status::VALID);
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

bool InfDescentStmtLeaf::isUnfinished() {
    return false;
}

size_t InfDescentStmtLeaf::height() {
    return 1;
}

size_t InfDescentStmtLeaf::heightUnfoldLeft() {
    return 0;
}

size_t InfDescentStmtLeaf::heightSplit() {
    return 0;
}

size_t InfDescentStmtLeaf::count() {
    return 1;
}

size_t InfDescentStmtLeaf::rcount() {
    return 0;
}

size_t InfDescentStmtLeaf::scount() {
    return 1;
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
void PairStmtNode::statusUpdate() {
    bool allChildrenInvalid = true;
    bool allChildrenUnfinished = true;

    for(const auto& child : children) {
        if(child->status == Status::VALID) {
            StmtNode::statusUpdate(Status::VALID);
            return;
        }

        if (child->status == Status::INVALID) {
            allChildrenUnfinished = false;
        }

        if (child->status == Status::UNKNOWN) {
            allChildrenInvalid = false;
            allChildrenUnfinished = false;
        }
    }

    if(allChildrenInvalid) {
        StmtNode::statusUpdate(Status::INVALID);
    } else if(allChildrenUnfinished) {
        StmtNode::statusUpdate(Status::UNFINISHED);
    } else {
        StmtNode::statusUpdate(Status::UNKNOWN);
    }
}

void PairStmtNode::markFailed() {
    StmtNode::statusUpdate(Status::INVALID);
}

void PairStmtNode::markUnfinished() {
    StmtNode::statusUpdate(Status::UNFINISHED);
}

bool PairStmtNode::isRoot() {
    return !parent;
}

bool PairStmtNode::isClosed() {
    return status == Status::VALID || status == Status::INVALID;
}

bool PairStmtNode::isProof() {
    return status == Status::VALID;
}

bool PairStmtNode::isFailed() {
    return status == Status::INVALID;
}

bool PairStmtNode::isUnfinished() {
    return status == Status::UNFINISHED;
}

void PairStmtNode::extractProof() {
    if (!isProof())
        return;

    size_t pos = children.size();
    for (size_t i = 0, sz = children.size(); i < sz; i++) {
        if (children[i]->isProof()) {
            pos = i;
            break;
        }
    }

    if (pos >= children.size())
        return;

    for (size_t i = 0; i < pos; i++) {
        children.erase(children.begin());
    }

    for (size_t i = 1, sz = children.size(); i < sz; i++) {
        children.erase(children.begin() + 1);
    }

    children[0]->extractProof();
}

void PairStmtNode::extractFailedBranches() {
    for (size_t i = 0, sz = children.size(); i < sz; i++) {
        if (!children[i]->isFailed()) {
            children.erase(children.begin() + i);
            i--;
            sz--;
        } else {
            children[i]->extractFailedBranches();
        }
    }
}

void PairStmtNode::extractCounterexample() {
    if (!this->isFailed()) {
        return;
    }

    for (RuleNodePtr& rule : children) {
        if (rule->isFailed()) {
            rule->extractCounterexample();
            cex.insert(cex.begin(), rule->cex.begin(), rule->cex.end());
        }
    }
}

size_t PairStmtNode::height() {
    size_t height = 1;

    if (!children.empty()) {
        height += children[0]->height();
    }

    for (const auto& child : children) {
        size_t newHeight = 1 + child->height();
        if (newHeight > height) {
            height = newHeight;
        }
    }

    return height;
}

size_t PairStmtNode::heightUnfoldLeft() {
    size_t heightLU = 0;

    if (!children.empty()) {
        heightLU += children[0]->heightLeftUnfold();
    }

    for (const auto& child : children) {
        size_t newHeightLU = child->heightLeftUnfold();
        if (newHeightLU > heightLU) {
            heightLU = newHeightLU;
        }
    }

    return heightLU;
}

size_t PairStmtNode::heightSplit() {
    size_t heightSP = 0;

    if (!children.empty()) {
        heightSP += children[0]->heightSplit();
    }

    for (const auto& child : children) {
        size_t newHeightSP = child->heightSplit();
        if (newHeightSP > heightSP) {
            heightSP = newHeightSP;
        }
    }

    return heightSP;
}

size_t PairStmtNode::count() {
    size_t count = 1;

    for (const auto& child : children) {
        count += child->count();
    }

    return count;
}

size_t PairStmtNode::rcount() {
    size_t count = 0;

    for (const auto& child : children) {
        count += child->rcount();
    }

    return count;
}

size_t PairStmtNode::scount() {
    size_t count = 1;

    for (const auto& child : children) {
        count += child->scount();
    }

    return count;
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
void RuleNode::statusUpdate(Status status) {
    if(this->status != status) {
        this->status = status;

        if(parent) {
            parent->statusUpdate();
        }
    }
}

void RuleNode::statusUpdate() {
    bool allChildrenValid = true;
    bool someChildrenUnfinished = false;

    for(const auto& child : children) {
        if(child->status == Status::INVALID) {
            statusUpdate(Status::INVALID);
            return;
        }

        if (child->status == Status::UNFINISHED) {
            allChildrenValid = false;
            someChildrenUnfinished = true;
        }

        if (child->status == Status::UNKNOWN) {
            allChildrenValid = false;
        }
    }

    if(allChildrenValid) {
        statusUpdate(Status::VALID);
    } else if(someChildrenUnfinished) {
        statusUpdate(Status::UNFINISHED);
    } else {
        statusUpdate(Status::UNKNOWN);
    }
}

bool RuleNode::isClosed() {
    return status == Status::VALID || status == Status::INVALID;
}

bool RuleNode::isProof() {
    return status == Status::VALID;
}

bool RuleNode::isFailed() {
    return status == Status::INVALID;
}

bool RuleNode::isUnfinished() {
    return status == Status::UNFINISHED;
}

void RuleNode::extractProof() {
    for (const auto& child : children) {
        child->extractProof();
    }
}

void RuleNode::extractFailedBranches() {
    if (!isFailed())
        return;

    for (size_t i = 0, sz = children.size(); i < sz; i++) {
        if (!children[i]->isFailed()) {
            children.erase(children.begin() + i);
            i--;
            sz--;
        } else {
            children[i]->extractFailedBranches();
        }
    }
}

void RuleNode::extractCounterexample() {
    if (!isFailed()) {
        return;
    }

    if (rule == Rule::COUNTEREXAMPLE) {
        StatePtr state = parent->pair->left->clone();
        std::vector<StatePtr> v;
        v.push_back(state);

        cex.push_back(v);
    } else if (rule == Rule::RIGHT_UNFOLD) {
        children[0]->extractCounterexample();
        cex.insert(cex.begin(), children[0]->cex.begin(), children[0]->cex.end());
    } else if (rule == Rule::LEFT_UNFOLD) {
        for (const StmtNodePtr& child : children) {
            if (child->isFailed()) {
                child->extractCounterexample();
                cex.insert(cex.begin(), child->cex.begin(), child->cex.end());
            }
        }
    } else if (rule == Rule::REDUCE) {
        StatePtr state = parent->pair->left->clone();
        state->calls.clear();

        children[0]->extractCounterexample();

        for (const vector<StatePtr>& v : children[0]->cex) {
            vector<StatePtr> newv(v);
            newv.insert(newv.begin(), state);
            cex.push_back(newv);
        }
    } else if (rule == Rule::SPLIT) {
        for (const StmtNodePtr& child : children) {
            if (child->isFailed()) {
                child->extractCounterexample();
                cex.insert(cex.begin(), child->cex.begin(), child->cex.end());
            }
        }
    }
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

size_t RuleNode::height() {
    if(rule == Rule::COUNTEREXAMPLE)
        return 0;

    size_t height = 0;

    if (!children.empty()) {
        height += children[0]->height();
    }

    for (const auto& child : children) {
        size_t newHeight = 0 + child->height();
        if (newHeight > height) {
            height = newHeight;
        }
    }

    return height;
}

size_t RuleNode::heightLeftUnfold() {
    size_t heightLU = 0;
    size_t addsToLU = 0;

    if(rule == Rule::LEFT_UNFOLD)
        addsToLU = 1;

    if (!children.empty()) {
        heightLU = addsToLU + children[0]->heightUnfoldLeft();
    }

    for (const auto& child : children) {
        size_t newHeightLU = addsToLU + child->heightUnfoldLeft();
        if (newHeightLU > heightLU) {
            heightLU = newHeightLU;
        }
    }

    return heightLU;
}

size_t RuleNode::heightSplit() {
    size_t heightSP = 0;
    size_t addsToSP = 0;

    if(rule == Rule::SPLIT)
        addsToSP = 1;

    if (!children.empty()) {
        heightSP = addsToSP + children[0]->heightSplit();
    }

    for (const auto& child : children) {
        size_t newHeightSP = addsToSP + child->heightSplit();
        if (newHeightSP > heightSP) {
            heightSP = newHeightSP;
        }
    }

    return heightSP;
}

size_t RuleNode::count() {
    if(rule == Rule::COUNTEREXAMPLE)
        return 0;

    size_t count = 1;

    for (const auto& child : children) {
        count += child->count();
    }

    return count;
}

size_t RuleNode::rcount() {
    if(rule == Rule::COUNTEREXAMPLE)
        return 0;

    size_t count = 1;

    for (const auto& child : children) {
        count += child->rcount();
    }

    return count;
}

size_t RuleNode::scount() {
    if(rule == Rule::COUNTEREXAMPLE)
        return 0;

    size_t count = 0;

    for (const auto& child : children) {
        count += child->scount();
    }

    return count;
}
