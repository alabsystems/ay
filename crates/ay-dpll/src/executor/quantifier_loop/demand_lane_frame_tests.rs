// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::panic::{catch_unwind, AssertUnwindSafe};

use ay_core::kani_compat::DetHashSet;
use ay_core::TermId;

use crate::executor::Executor;
use crate::quantifier_manager::QuantifierManager;

/// Arm `manager`'s lane on one gated family and park `parked` instances of
/// it. They are never instantiated here, so their ids need not name real
/// terms.
fn arm_with_parked(manager: &mut QuantifierManager, parked: u32) {
    let quantifier = TermId::new(1);
    let mut gated = DetHashSet::<u32>::default();
    gated.insert(quantifier.0);
    manager.demand_arm(gated, 3);
    for argument in 0..parked {
        manager.demand_park_for_test(
            quantifier,
            vec![TermId::new(2 + argument)],
            vec!["x".to_string()],
            5,
            "P".to_string(),
        );
    }
}

fn lane_state(exec: &Executor) -> (bool, usize) {
    let manager = exec
        .quantifier_manager
        .as_ref()
        .unwrap_or_else(|| panic!("the executor has a quantifier manager"));
    (manager.demand_active(), manager.demand_parked_len())
}

/// A lane armed inside the frame is gone after it, whether or not a manager
/// existed before.
#[test]
fn a_lane_armed_inside_the_frame_ends_with_it() {
    for manager_before in [false, true] {
        let mut exec = Executor::new();
        if manager_before {
            exec.quantifier_manager = Some(QuantifierManager::new());
        }
        exec.with_demand_lane_frame(|exec| {
            let manager = exec
                .quantifier_manager
                .get_or_insert_with(QuantifierManager::new);
            arm_with_parked(manager, 1);
            assert!(exec.demand_lane_armed());
        });
        assert_eq!(
            lane_state(&exec),
            (false, 0),
            "manager before the frame: {manager_before}"
        );
        assert!(!exec.demand_lane_armed());
    }
}

/// A nested solve starts with an inert lane and hands the enclosing solve's
/// lane back as it found it, parked instance included.
#[test]
fn a_nested_frame_restores_the_enclosing_lane() {
    let mut exec = Executor::new();
    exec.with_demand_lane_frame(|exec| {
        arm_with_parked(
            exec.quantifier_manager
                .get_or_insert_with(QuantifierManager::new),
            1,
        );
        exec.with_demand_lane_frame(|exec| {
            assert_eq!(
                lane_state(exec),
                (false, 0),
                "the nested solve starts inert"
            );
            arm_with_parked(
                exec.quantifier_manager
                    .get_or_insert_with(QuantifierManager::new),
                2,
            );
        });
        assert_eq!(
            lane_state(exec),
            (true, 1),
            "the enclosing lane is back, with its own parked instance only"
        );
    });
    assert_eq!(lane_state(&exec), (false, 0));
}

/// A panic inside the frame still leaves the lane inert for the next solve.
#[test]
fn a_panic_inside_the_frame_does_not_leave_a_lane_behind() {
    let mut exec = Executor::new();
    let unwound = catch_unwind(AssertUnwindSafe(|| {
        exec.with_demand_lane_frame(|exec| {
            arm_with_parked(
                exec.quantifier_manager
                    .get_or_insert_with(QuantifierManager::new),
                1,
            );
            panic!("solve failed inside the frame");
        });
    }));
    assert!(unwound.is_err(), "the panic propagates out of the frame");
    assert_eq!(lane_state(&exec), (false, 0));
}
