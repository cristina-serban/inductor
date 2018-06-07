#ifndef INDUCTOR_PROOF_BUILD_H
#define INDUCTOR_PROOF_BUILD_H

#include "proof_state.h"

#include "strat/proof_strategy.h"
#include "util/global_typedef.h"

namespace proof {
    /** Types of proof rules */
    enum Status {
        UNKNOWN = 0,
        VALID,
        INVALID,
        UNFINISHED
    };

    class RuleNode;
    typedef std::shared_ptr<RuleNode> RuleNodePtr;

    /* ===================================== StmtNode ===================================== */
    class StmtNode {
    protected:
        void statusUpdate(Status status);
    public:
        RuleNodePtr parent;
        Status status{Status::UNKNOWN};

        std::vector<std::vector<StatePtr>> cex;

        inline StmtNode() = default;

        inline explicit StmtNode(RuleNodePtr parent)
                : parent(std::move(parent)) {}

        virtual void statusUpdate() = 0;

        virtual bool isRoot() = 0;
        virtual bool isClosed() = 0;
        virtual bool isProof() = 0;
        virtual bool isFailed() = 0;
        virtual bool isUnfinished() = 0;

        virtual void extractProof() = 0;
        virtual void extractFailedBranches() = 0;
        virtual void extractCounterexample() = 0;

        virtual size_t height() = 0;
        virtual size_t heightUnfoldLeft() = 0;
        virtual size_t heightSplit() = 0;
        virtual size_t count() = 0;
        virtual size_t rcount() = 0;
        virtual size_t scount() = 0;

        virtual std::string toString(size_t indent) = 0;
        inline std::string toString() { return toString(0); }
    };

    typedef std::shared_ptr<StmtNode> StmtNodePtr;

    /* =================================== TrueStmtLeaf =================================== */
    class TrueStmtLeaf : public StmtNode {
    public:
        inline TrueStmtLeaf() = default;

        inline explicit TrueStmtLeaf(RuleNodePtr parent)
                : StmtNode(std::move(parent)) {}

        void statusUpdate() override;

        bool isRoot() override;
        bool isClosed() override;
        bool isProof() override;
        bool isFailed() override;
        bool isUnfinished() override;

        void extractProof() override {}
        void extractFailedBranches() override {}
        void extractCounterexample() override {}

        size_t height() override;
        size_t heightUnfoldLeft() override;
        size_t heightSplit() override;
        size_t count() override;
        size_t rcount() override;
        size_t scount() override;

        std::string toString(size_t indent) override;
    };

    typedef std::shared_ptr<TrueStmtLeaf> TrueStmtLeafPtr;

    /* ================================== FalseStmtLeaf =================================== */
    class FalseStmtLeaf : public StmtNode {
    public:
        inline FalseStmtLeaf() = default;

        inline explicit FalseStmtLeaf(RuleNodePtr parent)
                : StmtNode(std::move(parent)) {}

        void statusUpdate() override;

        bool isRoot() override;
        bool isClosed() override;
        bool isProof() override;
        bool isFailed() override;
        bool isUnfinished() override;

        void extractProof() override {}
        void extractFailedBranches() override {}
        void extractCounterexample() override {}

        size_t height() override;
        size_t heightUnfoldLeft() override;
        size_t heightSplit() override;
        size_t count() override;
        size_t rcount() override;
        size_t scount() override;

        std::string toString(size_t indent) override;
    };

    typedef std::shared_ptr<FalseStmtLeaf> FalseStmtLeafPtr;

    /* ================================ InfDescentStmtLeaf ================================ */
    class InfDescentStmtLeaf : public StmtNode {
    public:
        inline InfDescentStmtLeaf() = default;

        inline explicit InfDescentStmtLeaf(RuleNodePtr parent)
                : StmtNode(std::move(parent)) {}

        void statusUpdate() override;

        bool isRoot() override;
        bool isClosed() override;
        bool isProof() override;
        bool isFailed() override;
        bool isUnfinished() override;

        void extractProof() override {}
        void extractFailedBranches() override {}
        void extractCounterexample() override {}

        size_t height() override;
        size_t heightUnfoldLeft() override;
        size_t heightSplit() override;
        size_t count() override;
        size_t rcount() override;
        size_t scount() override;

        std::string toString(size_t indent) override;
    };

    typedef std::shared_ptr<InfDescentStmtLeaf> InfDescentStmtLeafPtr;

    /* =================================== PairStmtNode =================================== */
    class PairStmtNode : public StmtNode {
    public:
        PairPtr pair;
        std::vector<RuleNodePtr> children;
        strat::StateList stratStates;

        inline PairStmtNode() = default;

        inline explicit PairStmtNode(PairPtr pair)
                : pair(std::move(pair)) {}

        PairStmtNode(PairPtr pair, RuleNodePtr parent)
                : pair(std::move(pair))
                , StmtNode(std::move(parent)) {}

        PairStmtNode(PairPtr pair,
                     RuleNodePtr parent,
                     std::vector<RuleNodePtr> children)
                : pair(std::move(pair))
                , StmtNode(std::move(parent))
                , children(std::move(children)) {}

        void statusUpdate() override;
        void markFailed();
        void markUnfinished();

        bool isRoot() override;
        bool isClosed() override;
        bool isProof() override;
        bool isFailed() override;
        bool isUnfinished() override;

        void extractProof() override;
        void extractFailedBranches() override;
        void extractCounterexample() override;

        size_t height() override;
        size_t heightUnfoldLeft() override;
        size_t heightSplit() override;
        size_t count() override;
        size_t rcount() override;
        size_t scount() override;

        std::string toString(size_t indent) override;
    };

    typedef std::shared_ptr<PairStmtNode> PairStmtNodePtr;

    /* ===================================== RuleNode ===================================== */
    class RuleNode {
    private:
        void statusUpdate(Status status);
    public:
        Rule rule;
        PairStmtNodePtr parent;
        PairStmtNodePtr pivot;
        std::vector<StmtNodePtr> children;

        Status status{Status::UNKNOWN};
        std::vector<std::vector<StatePtr>> cex;

        inline RuleNode(Rule rule, PairStmtNodePtr parent)
                : rule(rule)
                , parent(std::move(parent)) {}

        void statusUpdate();

        bool isClosed();
        bool isProof();
        bool isFailed();
        bool isUnfinished();
        void extractProof();

        void extractFailedBranches();
        void extractCounterexample();

        size_t height();
        size_t heightLeftUnfold();
        size_t heightSplit();
        size_t count();
        size_t rcount();
        size_t scount();

        std::string toString(size_t indent);
    };
}

#endif //INDUCTOR_PROOF_BUILD_H
