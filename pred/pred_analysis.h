#ifndef INDUCTOR_PRED_ANALYSIS_H
#define INDUCTOR_PRED_ANALYSIS_H

#include "pred/pred_definition.h"

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

    struct IndexEquivAnalysis {
        umap<std::string, sptr_um1<BaseCase, equiv::IndexEquivalence>> base;
        umap<std::string, sptr_um1<InductiveCase, equiv::IndexEquivalence>> ind;

        inline void clear() {
            base.clear();
            ind.clear();
        };
    };

    struct EquivAnalysis {
        umap<std::string, sptr_um1<BaseCase, equiv::StringEquivalence>> base;
        umap<std::string, sptr_um1<InductiveCase, equiv::StringEquivalence>> ind;

        sptr_t<IndexEquivAnalysis> index;

        EquivAnalysis() : index(std::make_shared<IndexEquivAnalysis>()) {};

        inline void clear() {
            base.clear();
            ind.clear();
            index->clear();
        };
    };

    struct IndexAllocAnalysis {
        umap<std::string, sptr_um3<BaseCase, std::vector<Allocated>>> base;
        umap<std::string, sptr_um3<InductiveCase, std::vector<Allocated>>> ind;

        umap<std::string, std::vector<Allocated>> pred;

        inline void clear() {
            base.clear();
            ind.clear();
            pred.clear();
        };

        sptr_t<IndexAllocAnalysis> clone();

        bool equals(sptr_t<IndexAllocAnalysis> other);
    };

    struct AllocAnalysis {
        umap<std::string, sptr_um3<BaseCase, umap<std::string, Allocated>>> base;
        umap<std::string, sptr_um3<InductiveCase, umap<std::string, Allocated>>> ind;

        sptr_t<IndexAllocAnalysis> index;

        AllocAnalysis() : index(std::make_shared<IndexAllocAnalysis>()) {};

        inline void clear() {
            base.clear();
            ind.clear();
            index->clear();
        };
    };

    struct IndexReachAnalysis {
        umap<std::string, sptr_um1<BaseCase, reach::IndexReachability>> base;
        umap<std::string, sptr_um1<InductiveCase, reach::IndexReachability>> ind;

        sptr_um2<std::string, reach::IndexReachability> pred;

        inline void clear() {
            base.clear();
            ind.clear();
            pred.clear();
        }

        sptr_t<IndexReachAnalysis> clone();

        bool equals(sptr_t<IndexReachAnalysis> other);
    };

    struct ReachAnalysis {
        umap<std::string, sptr_um1<BaseCase, reach::StringReachability>> base;
        umap<std::string, sptr_um1<InductiveCase, reach::StringReachability>> ind;

        sptr_t<IndexReachAnalysis> index;

        ReachAnalysis() : index(std::make_shared<IndexReachAnalysis>()) {}

        inline void clear() {
            base.clear();
            ind.clear();
            index->clear();
        }
    };

    Allocated conj(Allocated a1, Allocated a2);
    Allocated conj(std::vector<Allocated> vec);
    std::vector<Allocated> conj(std::vector<Allocated> vec1, std::vector<Allocated> vec2);
    std::vector<Allocated> conj(std::vector<std::vector<Allocated>> vec);

    Allocated disj(Allocated a1, Allocated a2);
    Allocated disj(std::vector<Allocated> vec);
    std::vector<Allocated> disj(std::vector<Allocated> vec1, std::vector<Allocated> vec2);
    std::vector<Allocated> disj(std::vector<std::vector<Allocated>> vec);

    std::vector<std::vector<Allocated>> varToIndex(std::vector<umap<std::string, Allocated>> cases,
                                                   sptr_v<smtlib::sep::SortedVariable> params);

    std::string allocToString(Allocated a);

    sptr_t<reach::IndexReachability> conj(sptr_t<reach::IndexReachability> r1,
                                          sptr_t<reach::IndexReachability> r2);

    sptr_t<reach::IndexReachability> conj(sptr_v<reach::IndexReachability> vec);

    sptr_t<reach::IndexReachability> varToIndex(sptr_t<reach::StringReachability> reach,
                                                sptr_v<smtlib::sep::SortedVariable> params);

    sptr_v<reach::IndexReachability> varToIndex(sptr_v<reach::StringReachability> cases,
                                                sptr_v<smtlib::sep::SortedVariable> params);

    sptr_t<reach::StringReachability> disj(sptr_t<reach::StringReachability> reach,
                                           sptr_t<reach::IndexReachability> idxReach,
                                           sptr_v<smtlib::sep::Term> args);

}

#endif //INDUCTOR_PRED_ANALYSIS_H
