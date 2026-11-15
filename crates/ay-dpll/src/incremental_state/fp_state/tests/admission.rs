// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn admission_requires_the_entire_current_fp_root_set_not_an_anchor() {
    let mut terms = TermStore::new();
    let anchor = terms.mk_var("anchor", Sort::Bool);
    let left = fp_root(&mut terms, "left");
    let right = fp_root(&mut terms, "right");
    let mut state = IncrementalFpState::new();
    state.record_incremental_entry(&[anchor]);
    assert_eq!(
        observe(&mut state, &terms, &[anchor]),
        FpIncrementalAdmission::Defer
    );
    assert_eq!(
        observe(&mut state, &terms, &[anchor]),
        FpIncrementalAdmission::Defer
    );
    assert_eq!(
        observe(&mut state, &terms, &[anchor, left]),
        FpIncrementalAdmission::Defer
    );
    assert_eq!(
        observe(&mut state, &terms, &[anchor, left, right]),
        FpIncrementalAdmission::Defer
    );
    assert_eq!(
        observe(&mut state, &terms, &[anchor, left, right]),
        FpIncrementalAdmission::Admit
    );
    state.solves = 1;
    state.encoded_assertions.insert(left, 1);
    state.encoded_assertions.insert(right, 2);
    assert_eq!(
        observe(&mut state, &terms, &[right]),
        FpIncrementalAdmission::Admit
    );
}

#[test]
fn active_novel_roots_reset_complete_encoding_then_allow_exact_readmission() {
    let mut terms = TermStore::new();
    let left = fp_root(&mut terms, "left");
    let right = fp_root(&mut terms, "right");
    let mut state = IncrementalFpState::new();
    state.push();
    state.solves = 1;
    state.persistent_sat = Some(SatSolver::new(2));
    state.encoded_assertions.insert(left, 1);
    state.fp_cache.bool_input_lits.insert(left, 1);
    assert_eq!(
        observe(&mut state, &terms, &[left, right]),
        FpIncrementalAdmission::Defer
    );
    assert!(state.persistent_sat.is_none());
    assert!(state.encoded_assertions.is_empty());
    assert!(state.fp_cache.bool_input_lits.is_empty());
    assert_eq!((state.scope_depth, state.pending_pushes), (1, 1));
    assert!(!state.disabled);
    assert_eq!(
        observe(&mut state, &terms, &[left, right]),
        FpIncrementalAdmission::Admit
    );
}

fn nested_roots(terms: &mut TermStore) -> Vec<TermId> {
    let mut root = fp_root(terms, "deep");
    for _ in 0..8 {
        root = terms.mk_app(Symbol::named("opaque_bool"), [root], Sort::Bool);
    }
    vec![root, fp_root(terms, "other")]
}

#[test]
fn every_admission_checkpoint_including_final_poll_refuses_without_committing_a_trial() {
    let mut terms = TermStore::new();
    let roots = nested_roots(&mut terms);
    let mut baseline = IncrementalFpState::new();
    baseline.record_incremental_entry(&roots);
    let mut total = 0;
    assert_eq!(
        baseline.observe_live_assertion_reuse_with_control(&terms, &roots, &mut || {
            total += 1;
            Ok(())
        }),
        Ok(FpIncrementalAdmission::Admit)
    );
    assert!(total > 32, "the test must traverse the nested DAG");
    for stop_at in 1..=total {
        let mut state = IncrementalFpState::new();
        state.record_incremental_entry(&roots);
        let mut trial = state.take_for_update();
        let mut calls = 0;
        let result = trial.observe_live_assertion_reuse_with_control(&terms, &roots, &mut || {
            calls += 1;
            if calls == stop_at {
                Err(UnknownOrigin::MemoryBudget)
            } else {
                Ok(())
            }
        });
        assert_eq!(result, Err(UnknownOrigin::MemoryBudget));
        assert_eq!(calls, stop_at);
        drop(trial);
        empty_encoding(&state);
        // A fresh attempt has no half-observed admission. One complete
        // observation defers; its exact repeat can genuinely re-admit.
        assert_eq!(
            observe(&mut state, &terms, &roots),
            FpIncrementalAdmission::Defer
        );
        assert_eq!(
            observe(&mut state, &terms, &roots),
            FpIncrementalAdmission::Admit
        );
    }
}

#[test]
fn caught_admission_callback_panic_leaves_no_reusable_partial_scan() {
    let mut terms = TermStore::new();
    let roots = nested_roots(&mut terms);
    let mut state = IncrementalFpState::new();
    state.record_incremental_entry(&roots);
    state.push();
    let mut calls = 0;
    let caught = catch_unwind(AssertUnwindSafe(|| {
        let mut trial = state.take_for_update();
        let _ = trial.observe_live_assertion_reuse_with_control(&terms, &roots, &mut || {
            calls += 1;
            assert!(calls < 12, "callback panic after real source traversal");
            Ok(())
        });
    }));
    assert!(caught.is_err());
    assert_eq!(calls, 12);
    empty_encoding(&state);
    assert_eq!((state.scope_depth, state.pending_pushes), (1, 1));
    assert_eq!(
        observe(&mut state, &terms, &roots),
        FpIncrementalAdmission::Defer
    );
    assert_eq!(
        observe(&mut state, &terms, &roots),
        FpIncrementalAdmission::Admit
    );
}
