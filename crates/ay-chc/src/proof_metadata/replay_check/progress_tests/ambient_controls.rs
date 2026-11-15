// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::deadline::{current_lane_token, effective_thread_deadline};
use crate::smt::{ScopedLaneCancellation, ScopedSmtDeadline, ScopedSolveDeadline};
use crate::CancellationToken;

#[test]
fn expired_ambient_wall_refuses_before_callback_and_binding() {
    let run = truth_run();
    let before = run.metadata().to_json_value();
    let deadline = Instant::now() - Duration::from_secs(1);
    let _outer = ScopedSmtDeadline::install_until(deadline);
    assert_interrupted(run.run_checked_replay_with_binding_factory(
        Instant::now(),
        BUDGET,
        &mut || panic!("expired callback"),
        None,
        || panic!("expired binding"),
    ));
    assert_eq!(run.metadata().to_json_value(), before);
    assert_eq!(effective_thread_deadline(), Some(deadline));
}

#[test]
fn binding_and_nested_solvers_share_minimum_wall_then_restore() {
    let run = truth_run();
    let expected = Mode::Bound(Format::GroundDerivationV1)
        .legacy(&run)
        .unwrap();
    let now = Instant::now();
    let smt = now + Duration::from_secs(60);
    let solve = now + Duration::from_secs(40);
    let _smt = ScopedSmtDeadline::install_until(smt);
    let _solve = ScopedSolveDeadline::new(Some(solve));
    let actual = run
        .run_checked_replay_with_binding_factory(now, BUDGET, &mut || true, None, || {
            assert_eq!(effective_thread_deadline(), Some(solve));
            let _nested = ScopedSolveDeadline::new(None);
            assert_eq!(effective_thread_deadline(), Some(solve));
            binding(&run, Format::GroundDerivationV1)
        })
        .unwrap();
    assert_same(&actual, &expected);
    assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(smt));
    assert_eq!(crate::smt::current_thread_solve_deadline(), Some(solve));
}

#[test]
fn cancellation_observed_during_binding_cannot_resume_after_parent_reset() {
    let run = truth_run();
    let before = run.metadata().to_json_value();
    for cancelled_ambient in [false, true] {
        let caller = CancellationToken::new();
        let ambient = CancellationToken::new();
        let _lane = ScopedLaneCancellation::install(ambient.clone(), None);
        assert_interrupted(run.run_checked_replay_with_binding_factory(
            Instant::now(),
            BUDGET,
            &mut || true,
            Some(&caller.child()),
            || {
                let nested = current_lane_token().unwrap().child();
                let parent = if cancelled_ambient { &ambient } else { &caller };
                parent.cancel();
                assert!(nested.is_cancelled());
                parent.reset();
                assert!(nested.is_cancelled());
                binding(&run, Format::GroundDerivationV1)
            },
        ));
        assert!(!caller.is_cancelled());
        assert!(!ambient.is_cancelled());
        assert!(!current_lane_token().unwrap().is_cancelled());
        assert_eq!(run.metadata().to_json_value(), before);
    }
}
