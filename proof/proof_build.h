#ifndef INDUCTOR_PROOF_BUILD_H
#define INDUCTOR_PROOF_BUILD_H

#include "proof_tree.h"

#include "strat/proof_strategy.h"
#include "util/global_typedef.h"

namespace proof {
    struct RuleNode;

    /* ===================================== StmtNode ===================================== */
    struct StmtNode {
        virtual sptr_t<ProofNode> toProofNode() = 0;

        virtual bool isRoot() = 0;

        virtual bool isClosed() = 0;

        virtual bool isProof() = 0;

        virtual bool isFailed() = 0;

        virtual std::string toString(int indent = 0) = 0;
    };

    /* =================================== TrueStmtLeaf =================================== */
    struct TrueStmtLeaf : public StmtNode {
        inline TrueStmtLeaf() { }

        virtual sptr_t<ProofNode> toProofNode();

        virtual bool isRoot();

        virtual bool isClosed();

        virtual bool isProof();

        virtual bool isFailed();

        virtual std::string toString(int indent);
    };

    /* ================================== FalseStmtLeaf =================================== */
    struct FalseStmtLeaf : public StmtNode {
        inline FalseStmtLeaf() { }

        virtual sptr_t<ProofNode> toProofNode();

        virtual bool isRoot();

        virtual bool isClosed();

        virtual bool isProof();

        virtual bool isFailed();

        virtual std::string toString(int indent);
    };

    /* ================================ InductionStmtLeaf ================================= */
    struct InductionStmtLeaf : public StmtNode {
        inline InductionStmtLeaf() { }

        virtual sptr_t<ProofNode> toProofNode();

        virtual bool isRoot();

        virtual bool isClosed();

        virtual bool isProof();

        virtual bool isFailed();

        virtual std::string toString(int indent);
    };

    /* =================================== PairStmtNode =================================== */
    struct PairStmtNode : public StmtNode {
        sptr_t<Pair> pair;
        sptr_v<Pair> workset;

        sptr_t<RuleNode> parent;
        sptr_v<RuleNode> children;

        strat::StateList stratStates;

        inline PairStmtNode() { }

        inline PairStmtNode(sptr_t<Pair> pair) : pair(pair) { }

        PairStmtNode(sptr_t<Pair> pair, sptr_v<Pair> &workset);

        PairStmtNode(sptr_t<Pair> pair, sptr_v<Pair> &workset, sptr_t<RuleNode> parent);

        PairStmtNode(sptr_t<Pair> pair, sptr_v<Pair> &workset, sptr_t<RuleNode> parent, sptr_v<RuleNode> &children);

        virtual sptr_t<ProofNode> toProofNode();

        virtual bool isRoot();

        virtual bool isClosed();

        virtual bool isProof();

        virtual bool isFailed();

        virtual std::string toString(int indent);
    };

    /* ===================================== RuleNode ===================================== */
    struct RuleNode {
        Rule rule;

        sptr_t<PairStmtNode> parent;
        sptr_v<StmtNode> children;

        inline RuleNode(Rule rule, sptr_t<PairStmtNode> parent) : rule(rule), parent(parent) { }

        virtual bool isClosed();

        virtual bool isProof();

        virtual bool isFailed();

        virtual std::string toString(int indent);
    };
}

#endif //INDUCTOR_PROOF_BUILD_H
