// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
use super::*;
use crate::counted_storage::test_owner;
use crate::literal::Variable;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmissionError};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

#[path = "tests/originals.rs"]
mod originals;
#[path = "tests/resources.rs"]
mod resources;

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}

fn rows(trace: &ClauseTrace) -> Vec<(u64, Vec<Literal>, bool, Vec<u64>)> {
    trace
        .entries()
        .iter()
        .map(|e| {
            (
                e.id,
                e.clause.to_vec(),
                e.is_original,
                e.resolution_hints.to_vec(),
            )
        })
        .collect()
}

fn fixture() -> ClauseTrace {
    let mut trace = ClauseTrace::new();
    for id in 1..=4 {
        trace.add_clause_with_hint_slices(id, &[pos(id as u32)], true, &[]);
    }
    trace
}

fn add(trace: &mut ClauseTrace, owner: &CountedAdmission) -> Result<()> {
    trace
        .prepare_counted_add(9, &[pos(0), pos(1)], false, &[4, 2, 4, 1], owner)?
        .commit();
    owner.check()
}

#[test]
fn exact_borrowed_payload_and_replacement_capacities_match_ordinary() {
    let mut expected = fixture();
    expected.add_clause_with_hint_slices(9, &[pos(0), pos(1)], false, &[4, 2, 4, 1]);
    let mut actual = fixture();
    let owner = test_owner(1_000_000, 1_000_000);
    add(&mut actual, &owner).unwrap();
    assert_eq!(rows(&actual), rows(&expected));
    assert_eq!(actual.used_bytes(), expected.used_bytes());
    assert_eq!(
        ArenaCapacities::current(&actual),
        ArenaCapacities::current(&expected)
    );
    assert_eq!(
        actual.entries().last().unwrap().resolution_hints,
        [4, 2, 4, 1]
    );
    assert!(owner.usage().unwrap().storage_admitted > 0);
}

#[test]
fn abandoned_preparation_has_no_row_unsat_marker_or_provenance_mutation() {
    let mut trace = fixture();
    let before = rows(&trace);
    trace.solver_num_vars = Some((5, vec![pos(2)]));
    let owner = test_owner(1_000_000, 1_000_000);
    trace
        .prepare_counted_add(9, &[], false, &[1], &owner)
        .unwrap();
    assert_eq!(rows(&trace), before);
    assert!(!trace.has_empty_clause());
    assert!(trace.solver_num_vars.is_some());
    assert!(owner.usage().unwrap().work_admitted > 0);
}

#[test]
fn commit_invokes_no_callback_and_invalidates_old_provenance() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }),
    )
    .unwrap();
    let mut trace = fixture();
    trace.solver_num_vars = Some((5, vec![pos(2)]));
    let token = trace
        .prepare_counted_add(9, &[], false, &[1, 2], &owner)
        .unwrap();
    let before = calls.load(Ordering::SeqCst);
    token.commit();
    assert_eq!(calls.load(Ordering::SeqCst), before);
    assert_eq!(trace.entries().last().unwrap().resolution_hints, [1, 2]);
    assert!(trace.has_empty_clause());
    assert!(trace.solver_num_vars.is_none());
}

#[test]
fn duplicate_and_zero_ids_are_sticky_refusals_without_publishing() {
    for id in [0, 1, 4] {
        let mut trace = fixture();
        let before = rows(&trace);
        let owner = test_owner(1_000_000, 1_000_000);
        assert!(trace
            .prepare_counted_add(id, &[pos(0)], false, &[], &owner)
            .is_err());
        assert_eq!(rows(&trace), before);
        assert!(!trace.has_empty_clause());
        let receipt = owner.usage().unwrap();
        assert!(add(&mut trace, &owner).is_err());
        assert_eq!(owner.usage().unwrap(), receipt);
    }
}

#[test]
fn actual_peak_budget_refuses_before_any_row_or_pool_length_changes() {
    let mut trace = fixture();
    let before = rows(&trace);
    trace.budget_bytes = trace.used_bytes();
    let owner = test_owner(1_000_000, 1_000_000);
    assert!(add(&mut trace, &owner).is_err());
    assert_eq!(rows(&trace), before);
    assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
}

#[test]
fn resource_admission_is_not_proof_authority_independent_checker_still_decides() {
    for (opposed, hints, exact_valid) in [
        (true, vec![1, 2], true),
        (true, vec![1], false),
        (true, vec![2], false),
        (false, vec![1], false),
    ] {
        let mut trace = ClauseTrace::new();
        trace.add_clause_with_hint_slices(1, &[pos(0)], true, &[]);
        if opposed {
            trace.add_clause_with_hint_slices(2, &[pos(0).negated()], true, &[]);
        }
        let owner = test_owner(1_000_000, 1_000_000);
        trace
            .prepare_counted_add(3, &[], false, &hints, &owner)
            .unwrap()
            .commit();
        assert_eq!(owner.check(), Ok(()));
        assert!(owner.usage().unwrap().work_admitted > 0);
        assert_eq!(trace.entries().last().unwrap().resolution_hints, hints);
        assert_eq!(
            crate::test_util::strict_lrat_trace_replay(&trace, 1),
            exact_valid,
            "resource admission must not certify an incomplete or invalid exact proof"
        );
        // This separate converter deliberately repairs missing hints when
        // the authenticated originals really are contradictory. It still
        // cannot prove the satisfiable one-original control.
        let result = crate::validate_clause_trace_resolution(
            &trace,
            1,
            &crate::ResolutionValidationLimits::unbounded(),
        );
        assert_eq!(result.is_ok(), opposed, "{result:?}");
    }
}

#[test]
fn strict_replay_does_not_borrow_a_later_original_premise() {
    for late in [false, true] {
        let mut trace = ClauseTrace::new();
        trace.add_clause_with_hint_slices(1, &[pos(0)], true, &[]);
        if !late {
            trace.add_clause_with_hint_slices(2, &[pos(0).negated()], true, &[]);
        }
        let owner = test_owner(1_000_000, 1_000_000);
        trace
            .prepare_counted_add(3, &[], false, &[1, 2], &owner)
            .unwrap()
            .commit();
        if late {
            trace
                .prepare_counted_add(2, &[pos(0).negated()], true, &[], &owner)
                .unwrap()
                .commit();
        }
        assert_eq!(owner.check(), Ok(()));
        assert_eq!(crate::test_util::strict_lrat_trace_replay(&trace, 1), !late);
    }
}
