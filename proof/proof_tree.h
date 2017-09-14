/**
 * \file proof_tree.h
 * \brief Proof tree data structures.
 */

#ifndef INDUCTOR_PROOF_SPLIT_TREE_H
#define INDUCTOR_PROOF_SPLIT_TREE_H

#include "proof_rule.h"
#include "proof_state.h"

#include "util/global_typedef.h"

#include <string>

namespace proof {
    /* ===================================== ProofNode ===================================== */
    class ProofNode;
    typedef std::shared_ptr<ProofNode> ProofNodePtr;

    class ProofNode : public std::enable_shared_from_this<ProofNode> {
    public:
        ProofNodePtr parent;

        ProofNodePtr getRoot();

        virtual std::vector<size_t> getPath();

        virtual ProofNodePtr clone() = 0;

        virtual bool isClosed() = 0;

        virtual bool isProof() = 0;

        virtual std::string toString() = 0;

        virtual std::string toLatexString() = 0;
    };

    /* ===================================== TrueLeaf ===================================== */
    /** Leaf node with 'True' value */
    class TrueLeaf : public ProofNode {
    public:
        inline TrueLeaf() = default;

        ProofNodePtr clone() override;

        bool isClosed() override;

        bool isProof() override;

        std::string toString() override;

        std::string toLatexString() override;
    };

    typedef std::shared_ptr<TrueLeaf> TrueLeafPtr;

    /* ===================================== FalseLeaf ==================================== */
    /** Leaf node with 'False' value */
    class FalseLeaf : public ProofNode {
    public:
        inline FalseLeaf() = default;

        ProofNodePtr clone() override;

        bool isClosed() override;

        bool isProof() override;

        std::string toString() override;

        std::string toLatexString() override;
    };

    typedef std::shared_ptr<FalseLeaf> FalseLeafPtr;

    /* ================================== InfDescentLeaf ================================== */
    /** Leaf node indicating induction */
    class InfDescentLeaf : public ProofNode {
    public:
        inline InfDescentLeaf() = default;

        ProofNodePtr clone() override;

        bool isClosed() override;

        bool isProof() override;

        std::string toString() override;

        std::string toLatexString() override;
    };

    typedef std::shared_ptr<InfDescentLeaf> InfDescentLeafPtr;

    /* ===================================== PairNode ===================================== */
    /** Node containing an implication pair */
    class PairNode : public ProofNode {
    public:
        PairPtr pair;
        Rule rule;
        std::vector<ProofNodePtr> children;

        inline explicit PairNode(const PairPtr& pair) : pair(pair), rule(NONE) { }

        inline PairNode(const PairPtr& pair, Rule rule) : pair(pair), rule(rule) { }

        PairNode(const PairPtr& pair, Rule rule, const std::vector<ProofNodePtr>& children);

        void add(const ProofNodePtr& child);

        void add(const std::vector<ProofNodePtr>& children);

        ProofNodePtr getNodeFromPath(const std::vector<size_t>& path);

        ProofNodePtr clone() override;

        bool isClosed() override;

        bool isProof() override;

        std::string toString() override;

        std::string toLatexString() override;
    };

    typedef std::shared_ptr<PairNode> PairNodePtr;
}

#endif //INDUCTOR_PROOF_SPLIT_TREE_H
