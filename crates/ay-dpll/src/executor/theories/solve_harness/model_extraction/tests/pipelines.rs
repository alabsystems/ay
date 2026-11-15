// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::fixture::{setup, Counts};
use super::*;
use std::cell::Cell;
use std::sync::{atomic::Ordering, Arc};

fn assert_no_candidate(exec: &Executor) {
    assert!(exec.last_result().is_none());
    assert!(exec.last_model.is_none());
    assert!(!exec.last_model_validated);
    assert!(exec.last_sat_certificate.is_none());
}

#[test]
fn lazy_refusal_pops_temporary_frame_and_restores_incremental_state() {
    let mut exec = setup();
    let roots = exec.ctx.assertions.clone();
    let extracts = Cell::new(0);
    assert_terminal(
        exec.checked_lra_lazy(&extracts, QueryError::Exhausted),
        QueryError::Exhausted,
    );
    assert_eq!(extracts.get(), 1);
    assert_eq!(exec.ctx.assertions, roots);
    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("lazy state restored");
    assert_eq!(
        state.persistent_sat.as_ref().unwrap().scope_depth(),
        state.scope_depth
    );
    assert_no_candidate(&exec);
}

#[test]
fn assumption_refusal_pops_temporary_frame_and_restores_incremental_state() {
    let mut exec = setup();
    let roots = exec.ctx.assertions.clone();
    let extracts = Cell::new(0);
    assert_terminal(
        exec.checked_lra_assumptions(&extracts, QueryError::Interrupted(StopReason::Deadline)),
        QueryError::Interrupted(StopReason::Deadline),
    );
    assert_eq!(extracts.get(), 1);
    assert_eq!(exec.ctx.assertions, roots);
    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("assumption state restored");
    assert_eq!(
        state.persistent_sat.as_ref().unwrap().scope_depth(),
        state.scope_depth
    );
    assert_no_candidate(&exec);
}

#[test]
fn incremental_refusal_extracts_once_and_never_stores_a_candidate() {
    let mut exec = setup();
    let counts = Arc::new(Counts::default());
    let roots = exec.ctx.assertions.clone();
    assert_terminal(
        exec.checked_mock_incremental(&counts, || Err(QueryError::Exhausted)),
        QueryError::Exhausted,
    );
    assert_eq!(counts.checks.load(Ordering::SeqCst), 1);
    assert_eq!(counts.extracts.load(Ordering::SeqCst), 1);
    assert_eq!(counts.drops.load(Ordering::SeqCst), 1);
    assert_eq!(exec.ctx.assertions, roots);
    assert!(exec.incr_theory_state.is_some());
    assert_no_candidate(&exec);
}

#[test]
fn persistent_incremental_refusal_unsets_terms_and_preserves_state() {
    let mut exec = setup();
    let counts = Arc::new(Counts::default());
    let roots = exec.ctx.assertions.clone();
    assert_terminal(
        exec.checked_mock_persistent(&counts, || {
            Err(QueryError::Interrupted(StopReason::Deadline))
        }),
        QueryError::Interrupted(StopReason::Deadline),
    );
    assert_eq!(counts.extracts.load(Ordering::SeqCst), 1);
    assert_eq!(counts.unsets.load(Ordering::SeqCst), 1);
    assert_eq!(exec.ctx.assertions, roots);
    assert!(exec
        .incr_theory_state
        .as_ref()
        .unwrap()
        .persistent_sat
        .is_some());
    assert_no_candidate(&exec);
}

#[test]
fn warm_persistent_refusal_restores_theory_custody_after_unset() {
    let mut exec = setup();
    let counts = Arc::new(Counts::default());
    let _warm = crate::warm_theory_flag::WarmTheoryGuard::new(true);
    assert_terminal(
        exec.checked_mock_persistent(&counts, || {
            Err(QueryError::Invalid("unsupported owned cohort"))
        }),
        QueryError::Invalid("unsupported owned cohort"),
    );
    assert_eq!(counts.extracts.load(Ordering::SeqCst), 1);
    assert_eq!(counts.unsets.load(Ordering::SeqCst), 1);
    assert_eq!(counts.drops.load(Ordering::SeqCst), 0);
    assert!(exec
        .incr_theory_state
        .as_ref()
        .unwrap()
        .persist_theory
        .is_some());
    assert_no_candidate(&exec);
    drop(exec);
    assert_eq!(counts.drops.load(Ordering::SeqCst), 1);
}

#[test]
fn eager_persistent_refusal_bypasses_model_blocking_and_restores_owned_state() {
    let mut exec = setup();
    let roots = exec.ctx.assertions.clone();
    let extracts = Cell::new(0);
    let _warm = crate::warm_theory_flag::WarmTheoryGuard::new(true);
    assert_terminal(
        exec.checked_lra_split(&extracts, QueryError::Exhausted),
        QueryError::Exhausted,
    );
    assert_eq!(extracts.get(), 1);
    assert_eq!(exec.ctx.assertions, roots);
    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("owned state restored");
    assert!(state.persistent_sat.is_some());
    assert!(state.persist_theory.is_some());
    assert_eq!(
        state.persistent_sat.as_ref().unwrap().scope_depth(),
        state.scope_depth
    );
    assert_no_candidate(&exec);
    assert_eq!(exec.last_statistics.get_int("dpll.rebuilds"), Some(0));
}

#[test]
fn eager_nonpersistent_refusal_keeps_the_existing_restore_epilogue() {
    let mut exec = setup();
    let roots = exec.ctx.assertions.clone();
    let extracts = Cell::new(0);
    assert_terminal(
        exec.checked_lra_eager(&extracts, QueryError::Interrupted(StopReason::Cancelled)),
        QueryError::Interrupted(StopReason::Cancelled),
    );
    assert_eq!(extracts.get(), 1);
    assert_eq!(exec.ctx.assertions, roots);
    assert!(exec
        .incr_theory_state
        .as_ref()
        .unwrap()
        .persistent_sat
        .is_some());
    assert_no_candidate(&exec);
    assert_eq!(exec.last_statistics.get_int("dpll.rebuilds"), Some(0));
}
