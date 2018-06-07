/**
 * \file reach_string.h
 * \brief Reachability relation implementation for strings.
 */

#ifndef INDUCTOR_REACH_STRING_H
#define INDUCTOR_REACH_STRING_H

#include "reach/reach_index.h"

#include <string>
#include <unordered_map>

namespace reach {
    class StringReachability;
    typedef std::shared_ptr<StringReachability> StringReachabilityPtr;

    typedef std::unordered_map<std::string, std::vector<std::string>> StringReachabilityMap;
    typedef std::unordered_map<std::string, unsigned long> StringToIndexMap;

    /** Reachability relation for strings */
    class StringReachability {
    private:
        StringReachabilityMap map;

        StringReachabilityMap copyMap();

        bool equalsMap(const StringReachabilityMap& other);
    public:
        /**
        * Add a new string
        * \return Whether the addition was successful
        */
        bool add(const std::string& x);

        /**
         * Link string x and y
         * \return Whether the linking was successful
         */
        bool link(const std::string& x, const std::string& y);

        /**
         * Unlink string x and y
         * \return Whether the unlinking was successful
         */
        bool unlink(const std::string& x, const std::string& y);

        /**
         * Link all strings to each other
         * \return Whether the linking was successful
         */
        bool fill(const std::vector<std::string>& vec);

        /** \return Whether x and y are linked */
        bool find(const std::string& x, const std::string& y);

        /** \return Strings linked with x */
        std::vector<std::string> find(const std::string& x);

        /** \return List of all strings */
        std::vector<std::string> keys();

        /** Compute the closure of the reachability relation */
        void close();

        /** Clone reachability relation */
        StringReachabilityPtr clone();

        /** Textual representation of the reachability relation */
        std::string toString();

        /** Transform the structure into one for index reachability, based on a given order */
        IndexReachabilityPtr toIndexReachability(const StringToIndexMap& params);
    };
}

#endif //INDUCTOR_REACH_STRING_H
