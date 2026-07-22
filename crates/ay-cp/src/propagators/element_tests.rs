// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_element_creation() {
    let vars = vec![IntVarId(1), IntVarId(2), IntVarId(3)];
    let prop = Element::new(IntVarId(0), vars, IntVarId(4));
    assert_eq!(prop.variables().len(), 5); // index + result + 3 array
    assert_eq!(prop.name(), "element");
}

#[test]
fn test_element_propagates_result_from_index() {
    let mut trail = IntegerTrail::new();
    let index = trail.register(0, 2); // index ∈ [0, 2]
    let a0 = trail.register(10, 20);
    let a1 = trail.register(30, 40);
    let a2 = trail.register(50, 60);
    let result = trail.register(0, 100); // result ∈ [0, 100]

    let mut enc = IntegerEncoder::new();
    enc.register_var(0, 2);
    enc.register_var(10, 20);
    enc.register_var(30, 40);
    enc.register_var(50, 60);
    enc.register_var(0, 100);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    // result = array[index] → result ∈ [10, 60]
    let mut prop = Element::new(index, vec![a0, a1, a2], result);
    let res = prop.propagate(&trail, &enc);
    assert!(
        matches!(res, PropagationResult::Propagated(ref clauses) if !clauses.is_empty()),
        "should propagate result bounds from array elements"
    );
}

#[test]
fn test_element_propagates_index_from_result() {
    let mut trail = IntegerTrail::new();
    let index = trail.register(0, 2); // index ∈ [0, 2]
    let a0 = trail.register(10, 20); // values [10, 20]
    let a1 = trail.register(30, 40); // values [30, 40]
    let a2 = trail.register(50, 60); // values [50, 60]
    let result = trail.register(30, 40); // result ∈ [30, 40]

    let mut enc = IntegerEncoder::new();
    enc.register_var(0, 2);
    enc.register_var(10, 20);
    enc.register_var(30, 40);
    enc.register_var(50, 60);
    enc.register_var(30, 40);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    // result ∈ [30, 40] → only a1 is compatible → index = 1
    let mut prop = Element::new(index, vec![a0, a1, a2], result);
    let res = prop.propagate(&trail, &enc);
    assert!(
        matches!(res, PropagationResult::Propagated(ref clauses) if !clauses.is_empty()),
        "should propagate index bounds from result"
    );
}

#[test]
fn test_element_conflict_no_valid_index() {
    let mut trail = IntegerTrail::new();
    let index = trail.register(0, 1); // index ∈ [0, 1]
    let a0 = trail.register(10, 20);
    let a1 = trail.register(30, 40);
    let result = trail.register(50, 60); // result ∈ [50, 60] — impossible

    let mut enc = IntegerEncoder::new();
    enc.register_var(0, 1);
    enc.register_var(10, 20);
    enc.register_var(30, 40);
    enc.register_var(50, 60);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = Element::new(index, vec![a0, a1], result);
    let res = prop.propagate(&trail, &enc);
    assert!(
        matches!(res, PropagationResult::Conflict(_)),
        "should detect conflict when no array element can match result"
    );
}

#[test]
fn test_element_no_change_when_bounds_loose() {
    let mut trail = IntegerTrail::new();
    let index = trail.register(0, 1);
    let a0 = trail.register(1, 10);
    let a1 = trail.register(1, 10);
    let result = trail.register(1, 10);

    let mut enc = IntegerEncoder::new();
    enc.register_var(0, 1);
    enc.register_var(1, 10);
    enc.register_var(1, 10);
    enc.register_var(1, 10);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = Element::new(index, vec![a0, a1], result);
    let res = prop.propagate(&trail, &enc);
    assert!(
        matches!(res, PropagationResult::NoChange),
        "should not propagate when bounds already match"
    );
}
