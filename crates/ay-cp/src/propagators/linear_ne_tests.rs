// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_linear_ne_creation() {
    let vars = vec![IntVarId(0), IntVarId(1), IntVarId(2)];
    let prop = LinearNotEqual::new(vec![2, -1, 1], vars.clone(), 0);
    assert_eq!(prop.variables(), &vars);
    assert_eq!(prop.name(), "linear_ne");
    assert_eq!(prop.priority(), PropagatorPriority::Binary);
}

#[test]
fn test_linear_ne_no_propagation_when_two_unfixed() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(3, 3); // fixed x=3
    let _y = trail.register(0, 10); // unfixed
    let _z = trail.register(0, 10); // unfixed
                                    // 2*3 - y + z != 5, but y and z both unfixed → no propagation
    let enc = IntegerEncoder::new();
    let mut prop = LinearNotEqual::new(vec![2, -1, 1], vec![x, _y, _z], 5);
    let result = prop.propagate(&trail, &enc);
    assert!(matches!(result, PropagationResult::NoChange));
}

#[test]
fn test_linear_ne_propagation_when_one_unfixed() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(5, 5); // fixed x=5
    let y = trail.register(0, 10); // unfixed
                                   // x - y != 3, x=5 → y cannot be 2

    let mut enc = IntegerEncoder::new();
    enc.register_var(5, 5);
    enc.register_var(0, 10);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = LinearNotEqual::new(vec![1, -1], vec![x, y], 3);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Propagated(ref clauses) if clauses.len() == 1),
        "should propagate one blocking clause"
    );
}

#[test]
fn test_linear_ne_conflict_when_all_fixed() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(5, 5); // fixed x=5
    let y = trail.register(2, 2); // fixed y=2
                                  // x - y != 3, 5-2=3 → conflict

    let mut enc = IntegerEncoder::new();
    enc.register_var(5, 5);
    enc.register_var(2, 2);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = LinearNotEqual::new(vec![1, -1], vec![x, y], 3);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "should detect conflict when all fixed and sum==rhs"
    );
}

#[test]
fn test_linear_ne_no_conflict_when_satisfied() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(5, 5); // fixed x=5
    let y = trail.register(4, 4); // fixed y=4
                                  // x - y != 3, 5-4=1 ≠ 3 → no conflict

    let enc = IntegerEncoder::new();
    let mut prop = LinearNotEqual::new(vec![1, -1], vec![x, y], 3);
    let result = prop.propagate(&trail, &enc);
    assert!(matches!(result, PropagationResult::NoChange));
}

#[test]
fn test_linear_ne_non_divisible_remainder() {
    let mut trail = IntegerTrail::new();
    let _x = trail.register(0, 10); // unfixed
    let y = trail.register(2, 2); // fixed y=2
                                  // 2x + y != 5, y=2 → 2x != 3 → 3/2 not integer → always satisfied

    let enc = IntegerEncoder::new();
    let mut prop = LinearNotEqual::new(vec![2, 1], vec![_x, y], 5);
    let result = prop.propagate(&trail, &enc);
    assert!(matches!(result, PropagationResult::NoChange));
}

#[test]
fn test_linear_ne_forbidden_out_of_domain() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(5, 10); // domain [5, 10]
    let y = trail.register(0, 0); // fixed y=0
                                  // x - y != 3, y=0 → x != 3, but 3 < 5 (outside domain) → no propagation

    let enc = IntegerEncoder::new();
    let mut prop = LinearNotEqual::new(vec![1, -1], vec![x, y], 3);
    let result = prop.propagate(&trail, &enc);
    assert!(matches!(result, PropagationResult::NoChange));
}
