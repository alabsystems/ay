// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_linear_creation() {
    let vars = vec![IntVarId(0), IntVarId(1)];
    let prop = LinearLe::new(vec![1, 1], vars, 10);
    assert_eq!(prop.variables().len(), 2);
    assert_eq!(prop.name(), "linear_le");
}

#[test]
fn minimum_i128_divided_by_negative_one_clamps_exactly() {
    let value = ExactInteger::Small(i128::MIN);
    assert_eq!(value.exact_quotient_i64(-1), None);
    assert_eq!(value.linear_bound(-1), i64::MAX);
}

#[test]
fn test_linear_detects_infeasible() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(10, 20); // min contribution: 10
    let y = trail.register(10, 20); // min contribution: 10
                                    // x + y <= 15, but min(x+y) = 20 → conflict

    let mut enc = IntegerEncoder::new();
    enc.register_var(10, 20);
    enc.register_var(10, 20);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = LinearLe::new(vec![1, 1], vec![x, y], 15);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "should detect infeasible linear constraint"
    );
}

#[test]
fn test_linear_propagates_upper_bound() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(0, 10);
    let y = trail.register(5, 10);
    // x + y <= 12 → x <= 7 (since y >= 5)

    let mut enc = IntegerEncoder::new();
    enc.register_var(0, 10);
    enc.register_var(5, 10);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    let mut prop = LinearLe::new(vec![1, 1], vec![x, y], 12);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Propagated(ref clauses) if !clauses.is_empty()),
        "should propagate tighter upper bound"
    );
}
