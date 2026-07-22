// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcSort;

#[test]
fn test_dual_mbp_pure_lia() {
    // A: x >= 10, y = x + 1
    // B: y <= 5
    // Shared: {y}
    // A ∧ B: x >= 10, y = x + 1, y <= 5 → UNSAT
    // Expected: I(y) such that I ∧ B UNSAT and A → I
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a_constraints = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10)),
        ChcExpr::eq(
            ChcExpr::var(y.clone()),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1)),
        ),
    ];
    let b_constraints = vec![ChcExpr::le(ChcExpr::var(y), ChcExpr::Int(5))];

    let shared: FxHashSet<String> = ["y".to_string()].into_iter().collect();

    let result = compute_dual_mbp_interpolant(&a_constraints, &b_constraints, &shared);
    assert!(
        result.is_some(),
        "Should find interpolant for pure LIA case"
    );
    let interp = result.unwrap();

    // Verify shared-variable locality
    let vars: FxHashSet<String> = interp.vars().into_iter().map(|v| v.name).collect();
    assert!(
        vars.iter().all(|v| shared.contains(v)),
        "Interpolant must only mention shared vars, got: {vars:?}"
    );
}

#[test]
fn test_dual_mbp_mixed_bool_lia() {
    // A: loc = true, x = 0
    // B: loc = false, x > 5
    // Shared: {x, loc}
    // A ∧ B UNSAT because loc = true in A but loc = false in B
    let loc = ChcVar::new("loc", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);

    let a_constraints = vec![
        ChcExpr::var(loc.clone()),
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
    ];
    let b_constraints = vec![
        ChcExpr::not(ChcExpr::var(loc)),
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(5)),
    ];

    let shared: FxHashSet<String> = ["x".to_string(), "loc".to_string()].into_iter().collect();

    let result = compute_dual_mbp_interpolant(&a_constraints, &b_constraints, &shared);
    assert!(
        result.is_some(),
        "Should find interpolant for mixed Bool+LIA"
    );
}

#[test]
fn test_dual_mbp_b_unsat_returns_valid_interpolant() {
    // B is UNSAT by itself: x > 5 ∧ x < 3 ∧ y >= 0 (y is B-private)
    // AllSAT on B produces no models, so projections is empty → I = true
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a_constraints = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0))];
    let b_constraints = vec![
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(5)),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(3)),
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::Int(0)),
    ];

    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    let result = compute_dual_mbp_interpolant(&a_constraints, &b_constraints, &shared);
    assert!(result.is_some(), "B UNSAT should yield a valid interpolant");
    assert_eq!(result.unwrap(), ChcExpr::Bool(true));
}

#[test]
fn test_dual_mbp_with_private_vars() {
    // A: x >= 10, z = x * 2  (z is A-private)
    // B: y = x + 1, y <= 5   (y is B-private)
    // Shared: {x}
    // A ∧ B UNSAT: x >= 10 but y = x+1 and y <= 5 → x <= 4
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let a_constraints = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10)),
        ChcExpr::eq(
            ChcExpr::var(z),
            ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::Int(2)),
        ),
    ];
    let b_constraints = vec![
        ChcExpr::eq(
            ChcExpr::var(y.clone()),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1)),
        ),
        ChcExpr::le(ChcExpr::var(y), ChcExpr::Int(5)),
    ];

    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    let result = compute_dual_mbp_interpolant(&a_constraints, &b_constraints, &shared);
    assert!(
        result.is_some(),
        "Should project out B-private var y and produce interpolant over x"
    );
    let interp = result.unwrap();
    let vars: FxHashSet<String> = interp.vars().into_iter().map(|v| v.name).collect();
    assert!(
        vars.iter().all(|v| shared.contains(v)),
        "Interpolant must only mention shared var x, got: {vars:?}"
    );
}
