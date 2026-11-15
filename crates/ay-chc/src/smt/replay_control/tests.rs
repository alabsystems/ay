// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::{current_thread_solve_deadline, ScopedSolveDeadline};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::{atomic::AtomicBool, Arc};
use std::time::Duration;

#[test]
fn every_requested_or_ambient_clock_can_be_the_original_minimum() {
    let now = Instant::now();
    for (request, solve, smt) in [(10, 20, 30), (30, 10, 20), (20, 30, 10)] {
        let solve = now + Duration::from_secs(solve);
        let smt = now + Duration::from_secs(smt);
        let _solve = ScopedSolveDeadline::new(Some(solve));
        let _smt = ScopedSmtDeadline::install_until(smt);
        {
            let control =
                ScopedReplayControl::install_until(now + Duration::from_secs(request), None);
            assert_eq!(control.deadline(), now + Duration::from_secs(10));
            let _replacement = ScopedSolveDeadline::new(None);
            assert_eq!(effective_thread_deadline(), Some(control.deadline()));
        }
        assert_eq!(current_thread_solve_deadline(), Some(solve));
        assert_eq!(super::super::deadline::current_smt_deadline(), Some(smt));
    }
}

#[test]
fn both_caller_and_ambient_parent_observations_survive_resets() {
    for cancel_ambient in [false, true] {
        let caller = CancellationToken::new();
        let ambient = CancellationToken::new();
        let _outer = ScopedLaneCancellation::install(ambient.child(), None);
        let control = ScopedReplayControl::install_until(
            Instant::now() + Duration::from_secs(60),
            Some(&caller.child().child()),
        );
        let nested = current_lane_token().unwrap().child().child();
        let parent = if cancel_ambient { &ambient } else { &caller };
        parent.cancel();
        assert!(nested.is_cancelled());
        parent.reset();
        nested.reset();
        assert!(!parent.is_cancelled());
        assert!(nested.is_cancelled());
        assert!(!control.open());
        assert!(!control
            .cancellation()
            .unwrap()
            .interrupt_flag()
            .load(std::sync::atomic::Ordering::Relaxed));
    }
}

#[test]
fn nested_own_flag_refusal_does_not_cancel_the_owner_or_caller() {
    let caller = CancellationToken::new();
    let control =
        ScopedReplayControl::install_until(Instant::now() + Duration::from_secs(60), Some(&caller));
    let child = control.cancellation().unwrap().child();
    child.cancel();
    assert!(child.is_cancelled());
    assert!(control.open());
    assert!(!caller.is_cancelled());
}

#[test]
fn absent_tokens_stay_absent_and_precancel_is_latched_before_reset() {
    let deadline = Instant::now() + Duration::from_secs(60);
    {
        let control = ScopedReplayControl::install_until(deadline, None);
        assert!(control.cancellation().is_none());
        assert!(current_lane_token().is_none());
    }
    let caller = CancellationToken::new();
    caller.cancel();
    let control = ScopedReplayControl::install_until(deadline, Some(&caller));
    caller.reset();
    assert!(!control.open());
    assert!(!caller.is_cancelled());
}

#[test]
fn refusal_restores_original_deadline_and_interrupt_identity() {
    let outer_deadline = Instant::now() + Duration::from_secs(60);
    let ambient = CancellationToken::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    let _deadline = ScopedSmtDeadline::install_until(outer_deadline);
    let _lane = ScopedLaneCancellation::install(ambient.clone(), Some(interrupt.clone()));
    {
        let control = ScopedReplayControl::install_until(Instant::now(), None);
        assert!(!control.open());
        assert!(Arc::ptr_eq(&lane_interrupt_flag().unwrap(), &interrupt));
    }
    assert_eq!(effective_thread_deadline(), Some(outer_deadline));
    assert!(Arc::ptr_eq(&lane_interrupt_flag().unwrap(), &interrupt));
    ambient.cancel();
    assert!(current_lane_token().unwrap().is_cancelled());
    ambient.reset();
    assert!(!current_lane_token().unwrap().is_cancelled());
}

#[test]
fn unwind_restores_scope_and_fresh_attempt_does_not_inherit_old_refusal() {
    let caller = CancellationToken::new();
    let outer = Instant::now() + Duration::from_secs(60);
    let _deadline = ScopedSmtDeadline::install_until(outer);
    let before = current_lane_token();
    assert!(catch_unwind(AssertUnwindSafe(|| {
        let control = ScopedReplayControl::install_until(outer, Some(&caller));
        caller.cancel();
        assert!(!control.open());
        caller.reset();
        panic!("injected replay unwind");
    }))
    .is_err());
    assert_eq!(effective_thread_deadline(), Some(outer));
    assert_eq!(current_lane_token().is_some(), before.is_some());
    let fresh = ScopedReplayControl::install_until(outer, Some(&caller));
    assert!(fresh.open());
}
