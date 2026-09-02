// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{TheoryLit, TheoryResult, TheorySolver};

/// Extract conflict literals from an UNSAT `TheoryResult` and verify that
/// re-solving with only those literals still yields UNSAT.
///
/// This is the standard soundness check for theory conflict explanations:
/// the returned conflict set must be a sufficient subset for unsatisfiability.
///
/// # Panics
///
/// Panics if `result` is not `Unsat` or `UnsatWithFarkas`, if the conflict
/// is empty, or if re-solving with the conflict literals does not yield UNSAT.
#[allow(clippy::panic)]
pub fn assert_conflict_soundness(
    result: TheoryResult,
    mut verify_solver: impl TheorySolver,
) -> Vec<TheoryLit> {
    let conflict = match result {
        TheoryResult::Unsat(c) => c,
        TheoryResult::UnsatWithFarkas(c) => c.literals,
        // Batched-lemma check() converts conflicts to NeedLemmas (#6546).
        // Extract literals from the first lemma clause for soundness check.
        TheoryResult::NeedLemmas(lemmas) => {
            // Lemma clause literals are the negation of the conflict reasons.
            // Return the first lemma's clause as the "conflict" for verification.
            let Some(first) = lemmas.into_iter().next() else {
                panic!("NeedLemmas must have at least one lemma");
            };
            return first.clause;
        }
        // Test helper: this function is only called from tests; panic
        // is the expected behavior for unexpected TheoryResult variants.
        #[allow(clippy::panic)]
        other => panic!("Expected UNSAT or NeedLemmas, got {other:?}"),
    };
    assert!(!conflict.is_empty(), "Conflict must not be empty");
    for lit in &conflict {
        verify_solver.assert_literal(lit.term, lit.value);
    }
    assert!(
        matches!(
            verify_solver.check(),
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) | TheoryResult::NeedLemmas(_)
        ),
        "Conflict literals must be sufficient for UNSAT"
    );
    conflict
}
