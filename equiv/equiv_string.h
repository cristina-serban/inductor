/**
 * \file equiv_string.h
 * \brief Equivalence relation implementation for strings.
 */

#ifndef INDUCTOR_EQUIV_DATA_H
#define INDUCTOR_EQUIV_DATA_H

#include "equiv_index.h"

#include "util/global_typedef.h"

#include <string>

namespace equiv {
    struct Set;

    /** Node for an equivalence set */
    struct Node : public std::enable_shared_from_this<Node> {
        std::string data;
        sptr_t<Node> next;
        sptr_t<Set> parent;

        Node(std::string data, sptr_t<Node> next, sptr_t<Set> parent)
            : data(data), next(next), parent(parent) { }
    };

    /** Equivalence set */
    struct Set : public std::enable_shared_from_this<Set> {
        sptr_t<Node> head;
        sptr_t<Node> tail;
        unsigned long length;

        Set() : length(0) { }

        /** Create a first node with the given string */
        void init (std::string data);

        /** Textual representation of the set */
        std::string toString();
    };

    /** Equivalence relation for strings */
    class StringEquivalence {
    private:
        sptr_um2<std::string, Node> map;

    public:
        /**
         * Make a set consisting of a single node with the given string
         * \return Head of the new set
         */
        sptr_t<Node> makeSet(std::string data);

        /**
         * Find the set in which node x belongs
         * \return Head of the set
         */
        sptr_t<Node> findSet(sptr_t<Node> x);

        /**
         * Union of the sets for nodes x and y
         * \return Head of the new set
         */
        sptr_t<Node> unionSet(sptr_t<Node> x, sptr_t<Node> y);

        /**
         * Add a new node with the given string
         * \return Whether the addition was successful
         */
        bool add(std::string data);

        /** Find the node for string x */
        sptr_t<Node> find(std::string x);

        /**
         * Union of the nodes for strings x and y
         * \return Whether the union was successful
         */
        bool unite(std::string x, std::string y);

        /** Textual representation of the union-find structure */
        std::string toString();

        /** Transform the structure into one for index equivalence, based on a given order */
        sptr_t<IndexEquivalence> toIndexEquivalence(umap<std::string, unsigned long> params);
    };
}

#endif //INDUCTOR_EQUIV_DATA_H
