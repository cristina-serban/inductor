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
    StatePtr toState(const smtlib::sep::TermPtr& term,
                     const pred::PredicateTablePtr& table);

    /** Converts all cases of an inductive predicate into states */
    std::vector<StatePtr> toState(const pred::InductivePredicatePtr& pred,
                                  const pred::PredicateTablePtr& table);

    /** Converts a base case into a state */
    StatePtr toState(const pred::BaseCasePtr& bcase,
                     const pred::PredicateTablePtr& table);

    /** Converts an inductive case into a state */
    StatePtr toState(const pred::InductiveCasePtr& icase,
                     const pred::PredicateTablePtr& table);

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

    void normalize(const smtlib::sep::TermPtr& term,
                   std::vector<smtlib::sep::TermPtr>& accumulator);
}

#endif //INDUCTOR_PROOF_UTIL_H
