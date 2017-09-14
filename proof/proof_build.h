#ifndef INDUCTOR_PROOF_BUILD_H
#define INDUCTOR_PROOF_BUILD_H

#include "proof_tree.h"

#include "strat/proof_strategy.h"
#include "util/global_typedef.h"

namespace proof {
    class RuleNode;

    /* ===================================== StmtNode ===================================== */
    class StmtNode {
    public:
        virtual ProofNodePtr toProofNode() = 0;

        virtual bool isRoot() = 0;

        virtual bool isClosed() = 0;

        virtual bool isProof() = 0;

        virtual bool isFailed() = 0;

        virtual std::string toString(size_t indent) = 0;

        inline std::string toString() { return toString(0); }
    };

    typedef std::shared_ptr<StmtNode> StmtNodePtr;

    /* =================================== TrueStmtLeaf =================================== */
    class TrueStmtLeaf : public StmtNode {
    public:
        inline TrueStmtLeaf() = default;

        ProofNodePtr toProofNode() override;

        bool isRoot() override;

        bool isClosed() override;

        bool isProof() override;

        bool isFailed() override;

        std::string toString(size_t indent) override;
    };

    typedef std::shared_ptr<TrueStmtLeaf> TrueStmtLeafPtr;

    /* ================================== FalseStmtLeaf =================================== */
    class FalseStmtLeaf : public StmtNode {
    public:
        inline FalseStmtLeaf() = default;

        ProofNodePtr toProofNode() override;

        bool isRoot() override;

        bool isClosed() override;

        bool isProof() override;

        bool isFailed() override;

        std::string toString(size_t indent) override;
    };

    typedef std::shared_ptr<FalseStmtLeaf> FalseStmtLeafPtr;

    /* ================================ InfDescentStmtLeaf ================================ */
    class InfDescentStmtLeaf : public StmtNode {
    public:
        inline InfDescentStmtLeaf() = default;

        ProofNodePtr toProofNode() override;

        bool isRoot() override;

        bool isClosed() override;

        bool isProof() override;

        bool isFailed() override;

        std::string toString(size_t indent) override;
    };

    typedef std::shared_ptr<InfDescentStmtLeaf> InfDescentStmtLeafPtr;

    /* =================================== PairStmtNode =================================== */
    class PairStmtNode : public StmtNode {
    public:
        PairPtr pair;
        std::vector<PairPtr> workset;

        RuleNodePtr parent;
        sptr_v<RuleNode> children;

        strat::StateList stratStates;

        inline PairStmtNode() = default;

        inline explicit PairStmtNode(const PairPtr& pair) : pair(pair) {}

        PairStmtNode(const PairPtr& pair,
                     const std::vector<PairPtr>& workset);

        PairStmtNode(const PairPtr& pair,
                     const std::vector<PairPtr>& workset,
                     const RuleNodePtr& parent);

        PairStmtNode(const PairPtr& pair,
                     const std::vector<PairPtr>& workset,
                     const RuleNodePtr& parent,
                     const std::vector<RuleNodePtr>& children);

        ProofNodePtr toProofNode() override;

        bool isRoot() override;

        bool isClosed() override;

        bool isProof() override;

        bool isFailed() override;

        std::string toString(size_t indent) override;
    };

    typedef std::shared_ptr<PairStmtNode> PairStmtNodePtr;

    /* ===================================== RuleNode ===================================== */
    class RuleNode {
    public:
        Rule rule;

        PairStmtNodePtr parent;
        sptr_v<StmtNode> children;

        inline RuleNode(Rule rule, const PairStmtNodePtr& parent)
                : rule(rule), parent(parent) {}

        bool isClosed();

        bool isProof();

        bool isFailed();

        std::string toString(size_t indent);
    };

    typedef std::shared_ptr<RuleNode> RuleNodePtr;
}

#endif //INDUCTOR_PROOF_BUILD_H
