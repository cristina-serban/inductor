/**
 * \file equiv_string.h
 * \brief Equivalence relation implementation for strings.
 */

#ifndef INDUCTOR_EQUIV_DATA_H
#define INDUCTOR_EQUIV_DATA_H

#include "equiv_index.h"

#include <string>
#include <unordered_map>

namespace equiv {
    typedef std::unordered_map<std::string, unsigned long> StringToIndexMap;

    /* ======================================= Node ======================================= */
    struct Node;
    struct Set;

    typedef std::shared_ptr<Node> NodePtr;
    typedef std::shared_ptr<Set> SetPtr;

    /** Node for an equivalence set */
    struct Node : public std::enable_shared_from_this<Node> {
        std::string data;
        NodePtr next;
        SetPtr parent;

        Node(std::string data, NodePtr next, SetPtr parent)
                : data(std::move(data))
                , next(std::move(next))
                , parent(std::move(parent)) {}
    };

    /* ======================================= Set ======================================== */
    /** Equivalence set */
    struct Set : public std::enable_shared_from_this<Set> {
        NodePtr head;
        NodePtr tail;
        unsigned long length{0};

        Set() = default;

        /** Create a first node with the given string */
        void init(const std::string& data);

        /** Textual representation of the set */
        std::string toString();
    };

    /* ================================ StringEquivalence ================================= */
    /** Equivalence relation for strings */
    class StringEquivalence {
    private:
        std::unordered_map<std::string, NodePtr> map;

    public:
        /**
         * Make a set consisting of a single node with the given string
         * \return Head of the new set
         */
        NodePtr makeSet(const std::string& data);

        /**
         * Find the set in which node x belongs
         * \return Head of the set
         */
        NodePtr findSet(const NodePtr& x);

        /**
         * Union of the sets for nodes x and y
         * \return Head of the new set
         */
        NodePtr unionSet(const NodePtr& x, const NodePtr& y);

        /**
         * Add a new node with the given string
         * \return Whether the addition was successful
         */
        bool add(const std::string& data);

        /** Find the node for string x */
        NodePtr find(const std::string& x);

        /**
         * Union of the nodes for strings x and y
         * \return Whether the union was successful
         */
        bool unite(const std::string& x, const std::string& y);

        /** Textual representation of the union-find structure */
        std::string toString();

        /** Transform the structure into one for index equivalence, based on a given order */
        IndexEquivalencePtr toIndexEquivalence(const StringToIndexMap& params);
    };

    typedef std::shared_ptr<StringEquivalence> StringEquivalencePtr;
}

#endif //INDUCTOR_EQUIV_DATA_H
