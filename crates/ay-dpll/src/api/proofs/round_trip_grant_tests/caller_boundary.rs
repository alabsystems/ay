// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The certification envelope may predate the caller's tighter resource
//! scope. Match open_check_node's parent choice rather than jumping above it.

use super::*;
use ay_core::resource::{enter_work_ceiling, work_ceiling_reached, ChildSpec, Exhausted, Guard};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[test]
fn a_caller_grant_entered_after_controls_bounds_both_shares() {
    for share in [EffortShare::Guard, EffortShare::Pool] {
        let controls = controls();
        let caller = enter_work_grant(2);
        assert_eq!(round_trips_until_spent(&controls, share, 10_000), Some(3));
        assert_eq!(caller.spent_round_trips(), 3);
        assert!(
            work_grant_spent(),
            "the caller remains spent after the lane"
        );
        drop(caller);
        assert!(!work_grant_spent());
    }
}

#[test]
fn a_caller_grant_inside_certify_is_not_replaced_by_its_ancestor() {
    let controls = controls();
    let certify = controls.certify().expect("certification node");
    let _inside = certify.enter();
    let caller = enter_work_grant(2);
    assert_eq!(
        round_trips_until_spent(&controls, EffortShare::Guard, 10_000),
        Some(3)
    );
    assert_eq!(caller.spent_round_trips(), 3);
    assert!(work_grant_spent());
}

#[test]
fn an_envelope_without_certify_keeps_the_current_caller_grant() {
    let controls = TrustClauseDischargeControls::default();
    let caller = enter_work_grant(2);
    assert_eq!(
        round_trips_until_spent(&controls, EffortShare::Pool, 10_000),
        Some(3)
    );
    assert_eq!(caller.spent_round_trips(), 3);
}

#[test]
fn a_caller_work_ceiling_entered_after_controls_is_still_charged() {
    let controls = controls();
    let caller = enter_work_ceiling(Some(2));
    controls.in_round_trip_grant(EffortShare::Guard, || {
        work().add_sat_work(2, 0);
        assert!(work_ceiling_reached());
    });
    assert!(caller.spent());
    assert!(work_ceiling_reached());
}

#[test]
fn a_later_caller_cancellation_remains_visible_inside_the_lane() {
    let controls = controls();
    let certify = controls.certify().expect("certification node");
    let flag = Arc::new(AtomicBool::new(false));
    let spec = ChildSpec::new(NodeLabel::Share).with_external(Arc::clone(&flag));
    for caller in [certify.child(spec.clone()), Guard::root_child(spec)] {
        let _inside = caller.enter();
        controls.in_round_trip_grant(EffortShare::Pool, || {
            let current = current_guard().expect("lane grant");
            assert!(current.is_within(&caller));
            flag.store(true, Ordering::Relaxed);
            assert_eq!(current.cancelled(), Some(Exhausted::Cancelled));
            flag.store(false, Ordering::Relaxed);
        });
        assert!(current_guard().expect("caller restored").is_within(&caller));
    }
}

#[test]
fn an_actual_pool_solve_keeps_a_later_callers_tighter_grant() {
    let mut exec = crate::Executor::new();
    exec.ctx = long_unsat_executor().ctx;
    let controls = controls();
    let caller = enter_work_grant(2);
    let before = thread_round_trips();
    assert_eq!(
        run_pool_lane(&controls, &mut exec, "entailment-lane"),
        Some(false)
    );
    assert_eq!(thread_round_trips() - before, 3);
    assert_eq!(caller.spent_round_trips(), 3);
    assert!(work_grant_spent());
    assert_eq!(controls.decline_stop(), None);
}

#[test]
fn unwinding_a_lane_restores_the_original_callers_grant() {
    let controls = controls();
    let caller = enter_work_grant(2);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        controls.in_round_trip_grant(EffortShare::Guard, || {
            work().note_round_trip();
            panic!("injected lane unwind");
        });
    }));
    assert!(outcome.is_err());
    assert_eq!(caller.spent_round_trips(), 1);
    assert!(!work_grant_spent());
    work().note_round_trip();
    work().note_round_trip();
    assert!(work_grant_spent());
}
