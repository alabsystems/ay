// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_core::resource::{enter_check_stop, Guard};

use super::{CandidateOwner, Executor, UnknownOrigin};

#[test]
fn captured_callback_and_oneshot_refusal_survive_scope_replacement() {
    let exec = Executor::new();
    let stop = Arc::new(AtomicBool::new(false));
    let signal = Arc::clone(&stop);
    let scope = enter_check_stop(Arc::new(move || signal.swap(false, Ordering::SeqCst)));
    let mut owner = CandidateOwner::capture(&exec).expect("healthy original");
    drop(scope);
    let _replacement = enter_check_stop(Arc::new(|| false));
    stop.store(true, Ordering::SeqCst);
    assert_eq!(owner.poll(), Err(UnknownOrigin::IncompleteSolverLane));
    assert_eq!(owner.pay(0, 0), Err(UnknownOrigin::IncompleteSolverLane));
}

#[test]
fn caught_callback_unwind_cannot_revive_a_live_owner() {
    let exec = Executor::new();
    let panic_next = Arc::new(AtomicBool::new(false));
    let signal = Arc::clone(&panic_next);
    let _scope = enter_check_stop(Arc::new(move || {
        assert!(!signal.swap(false, Ordering::SeqCst), "callback unwind");
        false
    }));
    let mut owner = CandidateOwner::capture(&exec).expect("healthy original");
    panic_next.store(true, Ordering::SeqCst);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| owner.poll())).is_err());
    assert_eq!(owner.poll(), Err(UnknownOrigin::IncompleteSolverLane));
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
}

#[test]
fn callback_recording_an_attempt_refusal_cannot_return_false_to_hide_it() {
    let exec = Executor::new();
    let record_next = Arc::new(AtomicBool::new(false));
    let signal = Arc::clone(&record_next);
    let attempt = exec.evaluation_attempt();
    let _scope = enter_check_stop(Arc::new(move || {
        if signal.swap(false, Ordering::SeqCst) {
            attempt.record_stop(UnknownOrigin::MemoryBudget);
        }
        false
    }));
    let mut owner = CandidateOwner::capture(&exec).expect("healthy original");
    record_next.store(true, Ordering::SeqCst);
    assert_eq!(owner.poll(), Err(UnknownOrigin::MemoryBudget));
}

#[test]
fn separate_owners_never_replenish_the_original_guard() {
    let exec = Executor::new();
    let mut guard = Guard::new();
    guard.set_rlimit(Some(10));
    let scope = guard.enter();
    let mut first = CandidateOwner::capture(&exec).expect("first");
    let mut second = CandidateOwner::capture(&exec).expect("same grant");
    drop(scope);
    first.pay(6, 0).expect("six original ticks");
    assert_eq!(
        second.pay(4, 0),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    assert_eq!(
        first.pay(0, 0),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    assert_eq!(guard.ticks(), 10);
}

#[test]
fn original_scratch_ledger_counts_simultaneous_owners() {
    let mut exec = Executor::new();
    let source = exec.ctx.terms.true_memory_bytes();
    exec.set_term_memory_limit(Some(source + 200));
    let mut first = CandidateOwner::capture(&exec).expect("first");
    let mut second = CandidateOwner::capture(&exec).expect("second");
    first.pay(0, 128).expect("first live scratch");
    assert_eq!(second.pay(0, 128), Err(UnknownOrigin::MemoryBudget));
    drop(second);
    assert_eq!(first.pay(0, 0), Err(UnknownOrigin::MemoryBudget));
}

#[test]
fn nested_bv_oneshot_refusal_remains_in_the_original_candidate_attempt() {
    use crate::executor::theories::bv::BvSolveConfig;
    use crate::executor_types::{SolveResult, UnknownReason};

    let mut exec = Executor::new();
    let input = "(set-logic QF_BV) (declare-const x (_ BitVec 8))
        (assert (= (bvadd x #x01) #x02))";
    exec.execute_all(&ay_frontend::parse(input).expect("tiny BV query"))
        .expect("load query without solving");
    let stop = Arc::new(AtomicBool::new(false));
    let signal = Arc::clone(&stop);
    let original: ay_core::resource::CheckStop =
        Arc::new(move || signal.swap(false, Ordering::SeqCst));
    let _outer = enter_check_stop(Arc::clone(&original));
    let mut owner = CandidateOwner::capture(&exec).expect("healthy original attempt");
    {
        let _nested = owner.enter_nested();
        stop.store(true, Ordering::SeqCst);
        assert_eq!(
            exec.solve_bv_core(BvSolveConfig::qf_bv(), &[])
                .expect("bounded nested refusal"),
            SolveResult::Unknown,
        );
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Incomplete));
    }
    assert!(
        !stop.load(Ordering::SeqCst),
        "the nested encoder consumed the one-shot"
    );
    assert!(Arc::ptr_eq(
        &original,
        &ay_core::resource::current_check_stop()
            .expect("TLS accessible")
            .expect("restored original"),
    ));
    assert_eq!(owner.poll(), Err(UnknownOrigin::IncompleteSolverLane));
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
    assert_eq!(owner.pay(0, 0), Err(UnknownOrigin::IncompleteSolverLane));
}

#[test]
fn semantic_incomplete_does_not_latch_a_nonexistent_caller_refusal() {
    use crate::executor_types::{SolveResult, UnknownReason};

    let mut exec = Executor::new();
    let _outer = enter_check_stop(Arc::new(|| false));
    let mut owner = CandidateOwner::capture(&exec).expect("healthy original attempt");
    let _nested = owner.enter_nested();
    assert_eq!(
        exec.abort_bv_encoding().expect("semantic decline"),
        SolveResult::Unknown
    );
    assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Incomplete));
    assert_eq!(owner.poll(), Ok(()));
    assert!(exec.evaluation_stop_origin().is_none());
}

#[test]
fn nested_callback_unwind_is_latched_before_control_returns_to_owner() {
    let exec = Executor::new();
    let panic_next = Arc::new(AtomicBool::new(false));
    let signal = Arc::clone(&panic_next);
    let _outer = enter_check_stop(Arc::new(move || {
        assert!(
            !signal.swap(false, Ordering::SeqCst),
            "nested callback unwind"
        );
        false
    }));
    let mut owner = CandidateOwner::capture(&exec).expect("healthy original attempt");
    let _nested = owner.enter_nested();
    panic_next.store(true, Ordering::SeqCst);
    assert!(std::panic::catch_unwind(ay_core::resource::check_stop_requested).is_err());
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
    assert_eq!(owner.poll(), Err(UnknownOrigin::IncompleteSolverLane));
}

#[test]
fn reentrant_nested_poll_is_terminal_even_when_outer_callback_returns_false() {
    let exec = Executor::new();
    let reenter = Arc::new(AtomicBool::new(false));
    let signal = Arc::clone(&reenter);
    let _outer = enter_check_stop(Arc::new(move || {
        if signal.swap(false, Ordering::SeqCst) {
            assert!(ay_core::resource::check_stop_requested());
        }
        false
    }));
    let mut owner = CandidateOwner::capture(&exec).expect("healthy original attempt");
    let _nested = owner.enter_nested();
    reenter.store(true, Ordering::SeqCst);
    assert!(ay_core::resource::check_stop_requested());
    assert_eq!(owner.poll(), Err(UnknownOrigin::IncompleteSolverLane));
}
