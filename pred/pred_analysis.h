#ifndef INDUCTOR_PRED_ANALYSIS_H
#define INDUCTOR_PRED_ANALYSIS_H

#include "pred_definition.h"

#include "equiv/equiv_string.h"
#include "reach/reach_string.h"
#include "sep/sep_variable.h"

#include <memory>
#include <string>
#include <vector>
#include <unordered_map>

namespace pred {
    enum Allocated {
        ALWAYS = 0, MAYBE, NEVER
    };

    /* ================================ IndexEquivAnalysis ================================ */
    typedef std::unordered_map<BaseCasePtr, equiv::IndexEquivalencePtr> IndexEquivBaseMap;
    typedef std::unordered_map<std::string, IndexEquivBaseMap> IndexEquivBaseTable;

    typedef std::unordered_map<InductiveCasePtr, equiv::IndexEquivalencePtr> IndexEquivInductiveMap;
    typedef std::unordered_map<std::string, IndexEquivInductiveMap> IndexEquivInductiveTable;

    struct IndexEquivAnalysis {
        IndexEquivBaseTable base;
        IndexEquivInductiveTable inductive;

        inline void clear() {
            base.clear();
            inductive.clear();
        };
    };

    typedef std::shared_ptr<IndexEquivAnalysis> IndexEquivAnalysisPtr;

    /* ================================== EquivAnalysis =================================== */
    typedef std::unordered_map<BaseCasePtr, equiv::StringEquivalencePtr> StringEquivBaseMap;
    typedef std::unordered_map<std::string, StringEquivBaseMap> StringEquivBaseTable;

    typedef std::unordered_map<InductiveCasePtr, equiv::StringEquivalencePtr> StringEquivInductiveMap;
    typedef std::unordered_map<std::string, StringEquivInductiveMap> StringEquivInductiveTable;

    struct EquivAnalysis {
        StringEquivBaseTable base;
        StringEquivInductiveTable inductive;
        IndexEquivAnalysisPtr index;

        EquivAnalysis() : index(std::make_shared<IndexEquivAnalysis>()) {};

        inline void clear() {
            base.clear();
            inductive.clear();
            index->clear();
        };
    };

    typedef std::shared_ptr<EquivAnalysis> EquivAnalysisPtr;

    /* ================================ IndexAllocAnalysis ================================ */
    struct IndexAllocAnalysis;
    typedef std::shared_ptr<IndexAllocAnalysis> IndexAllocAnalysisPtr;

    typedef std::unordered_map<BaseCasePtr, std::vector<Allocated>> IndexAllocBaseMap;
    typedef std::unordered_map<std::string, IndexAllocBaseMap> IndexAllocBaseTable;

    typedef std::unordered_map<InductiveCasePtr, std::vector<Allocated>> IndexAllocInductiveMap;
    typedef std::unordered_map<std::string, IndexAllocInductiveMap> IndexAllocInductiveTable;

    struct IndexAllocAnalysis {
        IndexAllocBaseTable base;
        IndexAllocInductiveTable inductive;
        std::unordered_map<std::string, std::vector<Allocated>> predicates;

        inline void clear() {
            base.clear();
            inductive.clear();
            predicates.clear();
        };

        IndexAllocAnalysisPtr clone();

        bool equals(const IndexAllocAnalysisPtr& other);
    };

    /* ================================== AllocAnalysis =================================== */
    typedef std::unordered_map<BaseCasePtr, std::unordered_map<std::string, Allocated>> AllocBaseMap;
    typedef std::unordered_map<std::string, AllocBaseMap> AllocBaseTable;

    typedef std::unordered_map<InductiveCasePtr, std::unordered_map<std::string, Allocated>> AllocInductiveMap;
    typedef std::unordered_map<std::string, AllocInductiveMap> AllocInductiveTable;

    struct AllocAnalysis {
        AllocBaseTable base;
        AllocInductiveTable inductive;
        IndexAllocAnalysisPtr index;

        AllocAnalysis() : index(std::make_shared<IndexAllocAnalysis>()) {};

        inline void clear() {
            base.clear();
            inductive.clear();
            index->clear();
        };
    };

    typedef std::shared_ptr<AllocAnalysis> AllocAnalysisPtr;

    /* ================================ IndexReachAnalysis ================================ */
    struct IndexReachAnalysis;
    typedef std::shared_ptr<IndexReachAnalysis> IndexReachAnalysisPtr;

    typedef std::unordered_map<BaseCasePtr, reach::IndexReachabilityPtr> IndexReachBaseMap;
    typedef std::unordered_map<std::string, IndexReachBaseMap> IndexReachBaseTable;

    typedef std::unordered_map<InductiveCasePtr, reach::IndexReachabilityPtr> IndexReachInductiveMap;
    typedef std::unordered_map<std::string, IndexReachInductiveMap> IndexReachInductiveTable;

    struct IndexReachAnalysis {
        IndexReachBaseTable base;
        IndexReachInductiveTable inductive;

        std::unordered_map<std::string, reach::IndexReachabilityPtr> predicates;

        inline void clear() {
            base.clear();
            inductive.clear();
            predicates.clear();
        }

        IndexReachAnalysisPtr clone();

        bool equals(const IndexReachAnalysisPtr& other);
    };

    /* ================================== ReachAnalysis =================================== */
    typedef std::unordered_map<BaseCasePtr, reach::StringReachabilityPtr> ReachBaseMap;
    typedef std::unordered_map<std::string, ReachBaseMap> ReachBaseTable;

    typedef std::unordered_map<InductiveCasePtr, reach::StringReachabilityPtr> ReachInductiveMap;
    typedef std::unordered_map<std::string, ReachInductiveMap> ReachInductiveTable;

    struct ReachAnalysis {
        ReachBaseTable base;
        ReachInductiveTable inductive;
        IndexReachAnalysisPtr index;

        ReachAnalysis() : index(std::make_shared<IndexReachAnalysis>()) {}

        inline void clear() {
            base.clear();
            inductive.clear();
            index->clear();
        }
    };

    typedef std::shared_ptr<ReachAnalysis> ReachAnalysisPtr;

    /* ==================================== Utilities ===================================== */
    /** String representation of an allocation value */
    std::string allocToString(Allocated a);

    /** Computes conjunction of two allocation values */
    Allocated conj(Allocated a1, Allocated a2);

    /** Computes conjunction on a vector of allocation values */
    Allocated conj(const std::vector<Allocated>& vec);

    /** Computes conjunction between two vectors of allocation values */
    std::vector<Allocated> conj(const std::vector<Allocated>& vec1,
                                const std::vector<Allocated>& vec2);

    /** Computes conjunction on several vectors of allocation values */
    std::vector<Allocated> conj(const std::vector<std::vector<Allocated>>& vec);

    /** Computes conjunction between two index reachability objects */
    reach::IndexReachabilityPtr conj(const reach::IndexReachabilityPtr& r1,
                                     const reach::IndexReachabilityPtr& r2);

    /** Computes conjunction on several index reachability objects */
    reach::IndexReachabilityPtr conj(const std::vector<reach::IndexReachabilityPtr>& vec);


    /** Computes disjunction of two allocation values */
    Allocated disj(Allocated a1, Allocated a2);

    /** Computes disjunction on a vector of allocation values */
    Allocated disj(const std::vector<Allocated>& vec);

    /** Computes disjunction between two vectors of allocation values */
    std::vector<Allocated> disj(const std::vector<Allocated>& vec1,
                                const std::vector<Allocated>& vec2);

    /** Computes disjunction on several vectors of allocation values */
    std::vector<Allocated> disj(const std::vector<std::vector<Allocated>>& vec);

    /** Computes disjunction between a string reachability object and an index reachability object */
    reach::StringReachabilityPtr disj(const reach::StringReachabilityPtr& reach,
                                      const reach::IndexReachabilityPtr& idxReach,
                                      const std::vector<smtlib::sep::TermPtr>& args);


    /** Convert allocation maps based on parameter names to allocation vectors based on parameter indices */
    std::vector<std::vector<Allocated>> varToIndex(const std::vector<std::unordered_map<std::string, Allocated>>& cases,
                                                   const std::vector<smtlib::sep::SortedVariablePtr>& params);

    /** Convert a string reachability object to an index reachability object */
    reach::IndexReachabilityPtr varToIndex(const reach::StringReachabilityPtr& reach,
                                           const std::vector<smtlib::sep::SortedVariablePtr>& params);

    /** Convert several string reachability objects to their corresponding index reachability objects */
    std::vector<reach::IndexReachabilityPtr> varToIndex(const std::vector<reach::StringReachabilityPtr>& cases,
                                                        const std::vector<smtlib::sep::SortedVariablePtr>& params);
}

#endif //INDUCTOR_PRED_ANALYSIS_H
