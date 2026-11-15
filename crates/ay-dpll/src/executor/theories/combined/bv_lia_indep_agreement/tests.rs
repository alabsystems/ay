// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use ay_core::resource::{enter_check_stop, Guard};

use super::{AtomLane, CandidateOwner, Executor, Model, SolveResult, UnknownReason};

#[test]
fn a_semantically_rejected_candidate_does_not_forbid_an_alternative() {
    for reason in [
        UnknownReason::SelfCheckRejected,
        UnknownReason::ProofTrusted,
    ] {
        let mut exec = Executor::new();
        let root = exec.ctx.terms.mk_bool(true);
        exec.last_unknown_reason = Some(reason);
        let result =
            exec.finish_indep_bv_lia_after_unknown(Some(Model::empty()), false, &[root], &[]);
        assert!(matches!(result, Ok(SolveResult::Sat)), "{reason:?}");
        assert!(exec.evaluation_stop_origin().is_none());
    }
}

#[test]
fn semantic_refusal_remains_typed_when_no_alternative_succeeds() {
    let mut exec = Executor::new();
    let root = exec.ctx.terms.mk_bool(false);
    exec.last_unknown_reason = Some(UnknownReason::SelfCheckRejected);
    let result = exec.finish_indep_bv_lia_after_unknown(Some(Model::empty()), false, &[root], &[]);
    assert!(matches!(result, Ok(SolveResult::Unknown)));
    assert_eq!(
        exec.last_unknown_reason,
        Some(UnknownReason::SelfCheckRejected)
    );
    assert!(exec.last_model.is_none());
}

#[test]
fn a_typed_original_budget_refusal_never_attempts_an_alternative() {
    for reason in [
        UnknownReason::Timeout,
        UnknownReason::ResourceLimit,
        UnknownReason::MemoryLimit,
        UnknownReason::Interrupted,
    ] {
        let mut exec = Executor::new();
        let root = exec.ctx.terms.mk_bool(true);
        exec.last_unknown_reason = Some(reason);
        let result = exec.finish_indep_bv_lia_sat(Some(Model::empty()), false, &[root], &[]);
        assert!(matches!(result, Ok(SolveResult::Unknown)), "{reason:?}");
        assert_eq!(exec.last_unknown_reason, Some(reason));
        assert_eq!(exec.evaluation_stop_origin(), Some(reason.origin()));
        assert!(exec.last_model.is_none());
    }
}

#[test]
fn both_pin_directions_charge_one_retained_original_guard() {
    let mut exec = Executor::new();
    let root = exec.ctx.terms.mk_bool(true);
    let mut guard = Guard::new();
    guard.set_rlimit(Some(5));
    let scope = guard.enter();
    let mut owner = CandidateOwner::capture(&exec).expect("original allowance");
    drop(scope);
    assert!(exec
        .indep_atom_literals(&Model::empty(), &[root], AtomLane::BitVec, &mut owner)
        .is_ok());
    assert!(exec
        .indep_atom_literals(&Model::empty(), &[root], AtomLane::Arithmetic, &mut owner)
        .is_err());
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(crate::executor_types::UnknownOrigin::DeterministicResourceBudget)
    );
}

#[test]
fn stopped_pin_scan_is_not_a_successfully_empty_pin_set() {
    let mut exec = Executor::new();
    let root = exec.ctx.terms.mk_bool(true);
    let polls = Arc::new(AtomicUsize::new(0));
    let count = Arc::clone(&polls);
    let _scope = enter_check_stop(Arc::new(move || count.fetch_add(1, Ordering::SeqCst) == 4));
    let mut owner = CandidateOwner::capture(&exec).expect("initial healthy checks");
    assert!(exec
        .indep_atom_literals(&Model::empty(), &[root], AtomLane::Arithmetic, &mut owner)
        .is_err());
    assert!(exec.evaluation_stop_origin().is_some());
}
