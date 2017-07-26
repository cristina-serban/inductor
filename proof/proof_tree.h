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
    struct ProofNode : public std::enable_shared_from_this<ProofNode> {
        sptr_t<ProofNode> parent;

        sptr_t<ProofNode> getRoot();

        virtual std::vector<size_t> getPath();

        virtual sptr_t<ProofNode> clone() = 0;

        virtual bool isClosed() = 0;

        virtual bool isProof() = 0;

        virtual std::string toString() = 0;

        virtual std::string toLatexString() = 0;
    };

    /* ===================================== TrueLeaf ===================================== */
    /** Leaf node with 'True' value */
    struct TrueLeaf : public ProofNode {
        inline TrueLeaf() { }

        virtual sptr_t<ProofNode> clone();

        virtual bool isClosed();

        virtual bool isProof();

        virtual std::string toString();

        virtual std::string toLatexString();
    };

    /* ===================================== FalseLeaf ==================================== */
    /** Leaf node with 'False' value */
    struct FalseLeaf : public ProofNode {
        inline FalseLeaf() { }

        virtual sptr_t<ProofNode> clone();

        virtual bool isClosed();

        virtual bool isProof();

        virtual std::string toString();

        virtual std::string toLatexString();
    };

    /* =================================== InductionLeaf ================================== */
    /** Leaf node indicating induction */
    struct InductionLeaf : public ProofNode {
        inline InductionLeaf() { }

        virtual sptr_t<ProofNode> clone();

        virtual bool isClosed();

        virtual bool isProof();

        virtual std::string toString();

        virtual std::string toLatexString();
    };

    /* ===================================== PairNode ===================================== */
    /** Node containing an implication pair */
    struct PairNode : public ProofNode {
        sptr_t<Pair> pair;
        Rule rule;
        sptr_v<ProofNode> children;

        inline PairNode(sptr_t<Pair> pair) : pair(pair), rule(NONE) { }

        inline PairNode(sptr_t<Pair> pair, Rule rule) : pair(pair), rule(rule) { }

        PairNode(sptr_t<Pair> pair, Rule rule, sptr_v<ProofNode> children);

        void add(sptr_t<ProofNode> child);

        void add(sptr_v<ProofNode> children);

        virtual sptr_t<ProofNode> clone();

        sptr_t<ProofNode> getNode(std::vector<size_t> path);

        virtual bool isClosed();

        virtual bool isProof();

        virtual std::string toString();

        virtual std::string toLatexString();
    };
}

#endif //INDUCTOR_PROOF_SPLIT_TREE_H
