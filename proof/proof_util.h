/**
 * \file proof_util.h
 * \brief Proof search utilities.
 */

#ifndef INDUCTOR_PROOF_UTIL_H
#define INDUCTOR_PROOF_UTIL_H

#include "proof_state.h"

#include "pred/pred_table.h"

namespace proof {
    /** Converts a term into a state, based on a predicate table */
    StatePtr toState(const pred::PredicateTablePtr& table, const smtlib::sep::TermPtr& term);

    /** Converts all cases of an inductive predicate into states */
    std::vector<StatePtr> toState(const pred::InductivePredicatePtr& pred);

    /** Converts a base case into a state */
    StatePtr toState(const pred::BaseCasePtr& bcase);

    /** Converts an inductive case into a state */
    StatePtr toState(const pred::InductiveCasePtr& icase);

    /** Extracts a list of variables allocated in the constraint of the state */
    std::vector<std::string> getAllocated(const StatePtr& state);

    /** Removes pure constraints from a pair */
    PairPtr removePure(const PairPtr& pair);

    /** Removes pure constraints from a state */
    void removePure(const StatePtr& state);

    /** Removes spatial constraints from a state */
    void removeSpatial(const StatePtr& state);

    /** Removes the 'emp' constraint from a state */
    void removeEmp(const StatePtr& state);
}

#endif //INDUCTOR_PROOF_UTIL_H
