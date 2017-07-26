#ifndef INDUCTOR_PROOF_UTIL_H
#define INDUCTOR_PROOF_UTIL_H

#include "proof_state.h"

#include "pred/pred_table.h"

namespace proof {
    sptr_t<State> toState(sptr_t<pred::PredicateTable> table, sptr_t<smtlib::sep::Term> term);
    sptr_v<State> toState(sptr_t<pred::InductivePredicate> pred);
    sptr_t<State> toState(sptr_t<pred::BaseCase> bcase);
    sptr_t<State> toState(sptr_t<pred::InductiveCase> icase);

    sptr_t<smtlib::sep::Term> getBareTermStarTrue(sptr_t<State> state);

    sptr_t<Pair> removePure(sptr_t<Pair> pair);
    void removePure(sptr_t<State> state);

    std::vector<std::string> getAllocated(sptr_t<State> state);

    void removeEmp(sptr_t<State> state);

    void removeSpatial(sptr_t<State> state);
}

#endif //INDUCTOR_PROOF_UTIL_H
