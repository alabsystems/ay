// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Cumulative constraint propagator.

use super::*;
use crate::encoder::IntegerEncoder;
use crate::trail::IntegerTrail;
use ay_sat::Solver as SatSolver;

/// Helper: register a singleton-domain variable (constant) in the trail.
fn const_var(trail: &mut IntegerTrail, val: i64) -> IntVarId {
    trail.register(val, val)
}

#[test]
fn test_cumulative_creation() {
    let mut trail = IntegerTrail::new();
    let s0 = trail.register(0, 10);
    let s1 = trail.register(0, 10);
    let d0 = const_var(&mut trail, 3);
    let d1 = const_var(&mut trail, 2);
    let r0 = const_var(&mut trail, 1);
    let r1 = const_var(&mut trail, 1);

    let prop = Cumulative::new(vec![s0, s1], vec![d0, d1], vec![r0, r1], 1);
    assert_eq!(prop.name(), "cumulative");
    // starts (2) + durations (2) + demands (2) = 6 unique vars
    assert!(prop.variables().len() >= 2);
    assert_eq!(prop.priority(), PropagatorPriority::Global);
}

#[test]
fn test_cumulative_no_compulsory_parts() {
    let mut trail = IntegerTrail::new();
    let mut sat = SatSolver::new(0);
    let mut encoder = IntegerEncoder::new();

    // Tasks with wide domains: no compulsory parts
    let s0 = trail.register(0, 10);
    let _ = encoder.register_var(0, 10);
    let s1 = trail.register(0, 10);
    let _ = encoder.register_var(0, 10);
    let d0 = const_var(&mut trail, 3);
    let _ = encoder.register_var(3, 3);
    let d1 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    let r0 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    let r1 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    encoder.pre_allocate_all(&mut sat);

    let mut prop = Cumulative::new(vec![s0, s1], vec![d0, d1], vec![r0, r1], 3);
    let result = prop.propagate(&trail, &encoder);
    assert!(
        matches!(result, PropagationResult::NoChange),
        "no propagation when no compulsory parts"
    );
}

#[test]
fn test_cumulative_overload_conflict() {
    let mut trail = IntegerTrail::new();
    let mut sat = SatSolver::new(0);
    let mut encoder = IntegerEncoder::new();

    // Two tasks that must overlap: both have tight domains
    // Task 0: start ∈ [0, 1], dur=3, demand=2
    // Task 1: start ∈ [0, 1], dur=3, demand=2
    // Capacity = 3
    // Compulsory parts: [1, 3) for both (lst=1, ect=0+3=3)
    // At t=1: load = 2+2 = 4 > 3
    let s0 = trail.register(0, 1);
    let _ = encoder.register_var(0, 1);
    let s1 = trail.register(0, 1);
    let _ = encoder.register_var(0, 1);
    let d0 = const_var(&mut trail, 3);
    let _ = encoder.register_var(3, 3);
    let d1 = const_var(&mut trail, 3);
    let _ = encoder.register_var(3, 3);
    let r0 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    let r1 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    encoder.pre_allocate_all(&mut sat);

    let mut prop = Cumulative::new(vec![s0, s1], vec![d0, d1], vec![r0, r1], 3);
    let result = prop.propagate(&trail, &encoder);
    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "should detect overload conflict, got {result:?}"
    );
}

#[test]
fn test_cumulative_feasible_with_tight_bounds() {
    let mut trail = IntegerTrail::new();
    let mut sat = SatSolver::new(0);
    let mut encoder = IntegerEncoder::new();

    // Two tasks that don't overlap when properly scheduled
    // Task 0: start ∈ [0, 0], dur=2, demand=1 → runs [0, 2)
    // Task 1: start ∈ [2, 2], dur=2, demand=1 → runs [2, 4)
    // Capacity = 1
    // No overlap, no conflict
    let s0 = trail.register(0, 0);
    let _ = encoder.register_var(0, 0);
    let s1 = trail.register(2, 2);
    let _ = encoder.register_var(2, 2);
    let d0 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    let d1 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    let r0 = const_var(&mut trail, 1);
    let _ = encoder.register_var(1, 1);
    let r1 = const_var(&mut trail, 1);
    let _ = encoder.register_var(1, 1);
    encoder.pre_allocate_all(&mut sat);

    let mut prop = Cumulative::new(vec![s0, s1], vec![d0, d1], vec![r0, r1], 1);
    let result = prop.propagate(&trail, &encoder);
    assert!(
        matches!(result, PropagationResult::NoChange),
        "sequential tasks should be feasible, got {result:?}"
    );
}

#[test]
fn test_cumulative_bounds_propagation() {
    let mut trail = IntegerTrail::new();
    let mut sat = SatSolver::new(0);
    let mut encoder = IntegerEncoder::new();

    // Task 0: start ∈ [0, 0], dur=3, demand=2 → compulsory [0, 3), fixed
    // Task 1: start ∈ [0, 5], dur=2, demand=2
    // Capacity = 3
    // Task 0's compulsory part [0, 3) uses demand 2
    // Task 1 with demand 2 can't start at 0, 1 (would cause 4 > 3)
    // Task 1 must start >= 3 (after task 0's compulsory part ends)
    let s0 = trail.register(0, 0);
    let _ = encoder.register_var(0, 0);
    let s1 = trail.register(0, 5);
    let _ = encoder.register_var(0, 5);
    let d0 = const_var(&mut trail, 3);
    let _ = encoder.register_var(3, 3);
    let d1 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    let r0 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    let r1 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    encoder.pre_allocate_all(&mut sat);

    let mut prop = Cumulative::new(vec![s0, s1], vec![d0, d1], vec![r0, r1], 3);
    let result = prop.propagate(&trail, &encoder);

    // Task 1's est should be pushed to 3 (can't start at 0, 1)
    match result {
        PropagationResult::Propagated(clauses) => {
            assert!(
                !clauses.is_empty(),
                "should have propagation clauses for task 1"
            );
        }
        other => panic!("expected propagation, got {other:?}"),
    }
}

/// Test with variable durations: task with duration range [2, 5].
#[test]
fn test_cumulative_variable_duration() {
    let mut trail = IntegerTrail::new();
    let mut sat = SatSolver::new(0);
    let mut encoder = IntegerEncoder::new();

    // Task 0: start ∈ [0, 0], dur ∈ [3, 3] (constant), demand=1
    // Task 1: start ∈ [0, 5], dur ∈ [2, 5] (variable), demand=1
    // Capacity = 1
    // Task 0 compulsory part: [0, 3) (est=0, lst=0, ect=0+3=3)
    // Task 1 with lb(dur)=2 can't start during [0, 3) due to overlap
    let s0 = trail.register(0, 0);
    let _ = encoder.register_var(0, 0);
    let s1 = trail.register(0, 5);
    let _ = encoder.register_var(0, 5);
    let d0 = const_var(&mut trail, 3);
    let _ = encoder.register_var(3, 3);
    let d1 = trail.register(2, 5); // variable duration!
    let _ = encoder.register_var(2, 5);
    let r0 = const_var(&mut trail, 1);
    let _ = encoder.register_var(1, 1);
    let r1 = const_var(&mut trail, 1);
    let _ = encoder.register_var(1, 1);
    encoder.pre_allocate_all(&mut sat);

    let mut prop = Cumulative::new(vec![s0, s1], vec![d0, d1], vec![r0, r1], 1);
    let result = prop.propagate(&trail, &encoder);

    // Task 1 should have its lower bound tightened (can't start in [0, 2])
    match result {
        PropagationResult::Propagated(clauses) => {
            assert!(!clauses.is_empty(), "should propagate task 1 start bound");
        }
        other => panic!("expected propagation with variable duration, got {other:?}"),
    }
}

/// Test with variable demands.
#[test]
fn test_cumulative_variable_demand() {
    let mut trail = IntegerTrail::new();
    let mut sat = SatSolver::new(0);
    let mut encoder = IntegerEncoder::new();

    // Task 0: start ∈ [0, 0], dur=3, demand ∈ [2, 4] (variable)
    // Task 1: start ∈ [0, 1], dur=3, demand=2
    // Capacity = 3
    // Task 0 compulsory part: [0, 3), demand lb=2
    // Task 1 compulsory part: [1, 3) (lst=1, ect=0+3=3), demand=2
    // At t=1: load = lb(dem_0) + dem_1 = 2+2 = 4 > 3 → conflict
    let s0 = trail.register(0, 0);
    let _ = encoder.register_var(0, 0);
    let s1 = trail.register(0, 1);
    let _ = encoder.register_var(0, 1);
    let d0 = const_var(&mut trail, 3);
    let _ = encoder.register_var(3, 3);
    let d1 = const_var(&mut trail, 3);
    let _ = encoder.register_var(3, 3);
    let r0 = trail.register(2, 4); // variable demand!
    let _ = encoder.register_var(2, 4);
    let r1 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    encoder.pre_allocate_all(&mut sat);

    let mut prop = Cumulative::new(vec![s0, s1], vec![d0, d1], vec![r0, r1], 3);
    let result = prop.propagate(&trail, &encoder);
    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "should detect overload with variable demand lb, got {result:?}"
    );
}

/// Test that zero-duration variable tasks are correctly skipped.
#[test]
fn test_cumulative_zero_lb_duration_skipped() {
    let mut trail = IntegerTrail::new();
    let mut sat = SatSolver::new(0);
    let mut encoder = IntegerEncoder::new();

    // Task 0: start ∈ [0, 0], dur ∈ [0, 5] (might be zero), demand=2
    // Task 1: start ∈ [0, 0], dur=3, demand=2
    // Capacity = 3
    // Task 0 has lb(dur)=0, so no compulsory part → no conflict
    let s0 = trail.register(0, 0);
    let _ = encoder.register_var(0, 0);
    let s1 = trail.register(0, 0);
    let _ = encoder.register_var(0, 0);
    let d0 = trail.register(0, 5); // lb=0 means task might not execute
    let _ = encoder.register_var(0, 5);
    let d1 = const_var(&mut trail, 3);
    let _ = encoder.register_var(3, 3);
    let r0 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    let r1 = const_var(&mut trail, 2);
    let _ = encoder.register_var(2, 2);
    encoder.pre_allocate_all(&mut sat);

    let mut prop = Cumulative::new(vec![s0, s1], vec![d0, d1], vec![r0, r1], 3);
    let result = prop.propagate(&trail, &encoder);
    assert!(
        matches!(result, PropagationResult::NoChange),
        "zero-lb duration task should be skipped, got {result:?}"
    );
}

#[test]
fn test_cumulative_extreme_endpoint_and_load_conflict() {
    let mut trail = IntegerTrail::new();
    let mut sat = SatSolver::new(0);
    let mut encoder = IntegerEncoder::new();

    // Both tasks occupy [i64::MAX, i64::MAX + 1) in mathematical time and
    // together consume 2*i64::MAX resources. Neither total fits in i64, but
    // the cumulative semantics and the expected conflict are unambiguous.
    let s0 = const_var(&mut trail, i64::MAX);
    let _ = encoder.register_var(i64::MAX, i64::MAX);
    let s1 = const_var(&mut trail, i64::MAX);
    let _ = encoder.register_var(i64::MAX, i64::MAX);
    let d0 = const_var(&mut trail, 1);
    let _ = encoder.register_var(1, 1);
    let d1 = const_var(&mut trail, 1);
    let _ = encoder.register_var(1, 1);
    let r0 = const_var(&mut trail, i64::MAX);
    let _ = encoder.register_var(i64::MAX, i64::MAX);
    let r1 = const_var(&mut trail, i64::MAX);
    let _ = encoder.register_var(i64::MAX, i64::MAX);
    encoder.pre_allocate_all(&mut sat);

    let mut prop = Cumulative::new(vec![s0, s1], vec![d0, d1], vec![r0, r1], i64::MAX);
    let result = prop.propagate(&trail, &encoder);
    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "wide endpoint/load arithmetic should detect overload, got {result:?}"
    );
}
