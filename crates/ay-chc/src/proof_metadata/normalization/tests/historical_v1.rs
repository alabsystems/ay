// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

// Exact byte oracle from AY 48c98a43, not a copy of the new shared policy.
mod oracle;

#[test]
fn historical_policy_matches_original_complete_ast_oracle_without_changing_v2() {
    for problem in [ChcProblem::new(), rich_problem()] {
        let current = input(&problem);
        let historical = problem
            .normalized_input_v1_with_progress(&mut || true)
            .unwrap();
        assert_eq!(historical, oracle::normalized_chc_input(&problem));
        assert_eq!(
            crate::proof_metadata::sha256_hex(historical.as_bytes()),
            oracle::normalized_chc_input_sha256(&problem)
        );
        assert_eq!(input(&problem), current);
        assert_oracle(&problem);
        assert!(historical.starts_with("ay.chc.normalized-input/v1\n"));
        if !problem.datatype_defs().is_empty() {
            assert!(current.starts_with("ay.chc.normalized-input/v2\n"));
            assert_ne!(current, historical);
        } else {
            assert_eq!(current, historical);
            assert_eq!(
                ordered_hash(&problem),
                oracle::ordered_chc_clause_sequence_sha256(&problem)
            );
        }
    }
}

#[test]
fn every_historical_traversal_and_final_poll_refuses_without_partial_identity() {
    let problem = rich_problem();
    let current = input(&problem);
    let mut total = 0;
    let expected = problem
        .normalized_input_v1_with_progress(&mut || {
            total += 1;
            true
        })
        .unwrap();
    assert!(total > 100);
    for cut in 1..=total {
        let mut calls = 0;
        let refused = problem.normalized_input_v1_with_progress(&mut || {
            calls += 1;
            calls != cut
        });
        assert!(refused.is_none(), "cut {cut}/{total}");
        assert_eq!(calls, cut, "no fallback or retry after refusal");
    }
    assert_eq!(input(&problem), current);
    assert_eq!(
        problem.normalized_input_v1_with_progress(&mut || true),
        Some(expected)
    );
}

#[test]
fn historical_identity_retains_unused_registry_and_actual_clause_mutations() {
    let original = rich_problem();
    let before = original
        .normalized_input_v1_with_progress(&mut || true)
        .unwrap();
    let mut registry_changed = original.clone();
    registry_changed.add_datatype_def("A".to_owned(), vec![("Changed".to_owned(), Vec::new())]);
    let mut clause_changed = original.clone();
    clause_changed.clauses_mut()[0].body.constraint = Some(ChcExpr::Bool(false));
    for changed in [registry_changed, clause_changed] {
        let after = changed
            .normalized_input_v1_with_progress(&mut || true)
            .unwrap();
        assert_ne!(after, before);
        assert_eq!(after, oracle::normalized_chc_input(&changed));
    }
}

#[test]
fn final_historical_observer_panic_cannot_publish_bytes_or_change_current_identity() {
    let problem = rich_problem();
    let current = input(&problem);
    let mut total = 0;
    assert!(problem
        .normalized_input_v1_with_progress(&mut || {
            total += 1;
            true
        })
        .is_some());
    assert!(total > 100);
    let mut calls = 0;
    let stopped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        problem.normalized_input_v1_with_progress(&mut || {
            calls += 1;
            assert_ne!(
                calls, total,
                "BUG: original historical identity observer panic"
            );
            true
        })
    }));
    assert!(stopped.is_err());
    assert_eq!(calls, total);
    assert_eq!(input(&problem), current);
}
