// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

#[test]
fn test_alldiff_creation() {
    let vars = vec![IntVarId(0), IntVarId(1), IntVarId(2)];
    let prop = AllDifferentBounds::new(vars);
    assert_eq!(prop.variables().len(), 3);
    assert_eq!(prop.name(), "alldifferent_bounds");
}

#[test]
fn test_alldiff_detects_duplicate_fixed() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(5, 5); // fixed to 5
    let y = trail.register(5, 5); // fixed to 5 — conflict!
    let z = trail.register(1, 10);

    let mut enc = IntegerEncoder::new();
    enc.register_var(5, 5);
    enc.register_var(5, 5);
    enc.register_var(1, 10);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = AllDifferentBounds::new(vec![x, y, z]);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "should detect two vars fixed to same value"
    );
}

#[test]
fn test_alldiff_hall_interval_propagation() {
    // x ∈ [1,2], y ∈ [1,2], z ∈ [1,3]
    // x,y form Hall interval [1,2], so z must be >= 3
    let mut trail = IntegerTrail::new();
    let x = trail.register(1, 2);
    let y = trail.register(1, 2);
    let z = trail.register(1, 3);

    let mut enc = IntegerEncoder::new();
    enc.register_var(1, 2);
    enc.register_var(1, 2);
    enc.register_var(1, 3);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = AllDifferentBounds::new(vec![x, y, z]);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Propagated(_)),
        "should propagate z >= 3 from Hall interval [1,2]"
    );
}

#[test]
fn test_alldiff_upper_bound_propagation() {
    // x ∈ [2,3], y ∈ [2,3], z ∈ [1,3]
    // x,y form Hall interval [2,3], so z must be <= 1
    let mut trail = IntegerTrail::new();
    let x = trail.register(2, 3);
    let y = trail.register(2, 3);
    let z = trail.register(1, 3);

    let mut enc = IntegerEncoder::new();
    enc.register_var(2, 3);
    enc.register_var(2, 3);
    enc.register_var(1, 3);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = AllDifferentBounds::new(vec![x, y, z]);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Propagated(_)),
        "should propagate z <= 1 from Hall interval [2,3]"
    );
}

#[test]
fn test_alldiff_no_propagation() {
    // x ∈ [1,3], y ∈ [1,3], z ∈ [1,3]
    // No Hall interval — all can take distinct values
    let mut trail = IntegerTrail::new();
    let x = trail.register(1, 3);
    let y = trail.register(1, 3);
    let z = trail.register(1, 3);

    let mut enc = IntegerEncoder::new();
    enc.register_var(1, 3);
    enc.register_var(1, 3);
    enc.register_var(1, 3);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = AllDifferentBounds::new(vec![x, y, z]);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::NoChange),
        "no propagation expected when all domains are wide enough"
    );
}

#[test]
fn test_alldiff_conflict_too_many_vars() {
    // x ∈ [1,2], y ∈ [1,2], z ∈ [1,2] — but only 2 values for 3 vars
    let mut trail = IntegerTrail::new();
    let x = trail.register(1, 2);
    let y = trail.register(1, 2);
    let z = trail.register(1, 2);

    let mut enc = IntegerEncoder::new();
    enc.register_var(1, 2);
    enc.register_var(1, 2);
    enc.register_var(1, 2);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = AllDifferentBounds::new(vec![x, y, z]);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "3 vars in [1,2] should be a conflict"
    );
}
