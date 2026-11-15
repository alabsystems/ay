// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whether a theory conflict holds with no context at all.
//!
//! The fail-closed gate of the search (`verify_conflict_semantic_memoized`)
//! re-derives a conflict together with the query's support literals, samples
//! its EUF re-check, and lets a conflict through wherever it cannot decide.
//! That is the right question for "may this search learn the clause". A
//! caller that wants to use the clause OUTSIDE the search that produced it
//! (`crate::executor::ground_solve_carry`) needs a stronger fact: the literal
//! set is inconsistent in the theory by itself, whatever else is asserted.

use ay_core::{TermStore, TheoryLit};

use super::dispatch::{
    classify_conflict_domain, verify_conflict_semantic_classified, ConflictSemanticVerdict,
    TheoryDomain,
};

/// `true` when a fresh theory solver, given the literals of `conflict` and
/// nothing else, derives a contradiction.
///
/// No support literal is asserted, no memo or scoped re-check gate is
/// consulted, and no re-check is sampled out, so a `true` does not depend on
/// the query, its scope, its instances or the solve that produced the
/// conflict: every free symbol is unconstrained, the literal set has no model
/// in the theory, and the clause that negates it is valid in the theory.
///
/// Only [`ConflictSemanticVerdict::Reproved`] counts. Every other outcome is
/// `false`: a satisfiable literal set, a fragment the fresh solvers do not
/// decide (nonlinear arithmetic, bit-vectors, strings checked structurally),
/// a split or lemma request, a verifier budget trip, and a re-derivation that
/// needed the array solver (`ReprovedByArrayTheory`), which re-runs the
/// inference under test rather than checking it.
pub(crate) fn conflict_is_refuted_on_its_own(conflict: &[TheoryLit], terms: &TermStore) -> bool {
    if conflict.is_empty() || has_complementary_literals(conflict) {
        return false;
    }
    let verdict = match classify_conflict_domain(terms, conflict) {
        // The dispatcher's EUF arm samples the fresh congruence closure; this
        // check must run it every time.
        TheoryDomain::Euf => super::euf::reprove_euf_conflict(conflict, terms, &[]),
        _ => verify_conflict_semantic_classified(conflict, terms, &[], None, None),
    };
    matches!(verdict, Ok(ConflictSemanticVerdict::Reproved))
}

/// A literal set that asserts one atom both ways negates to a tautology:
/// nothing a later solve could use. (The dispatcher answers `Reproved` for
/// it without solving anything.)
fn has_complementary_literals(conflict: &[TheoryLit]) -> bool {
    let mut sorted = conflict.to_vec();
    sorted.sort_unstable();
    sorted
        .windows(2)
        .any(|pair| pair[0].term == pair[1].term && pair[0].value != pair[1].value)
}

#[cfg(test)]
#[path = "standalone_tests.rs"]
mod tests;
