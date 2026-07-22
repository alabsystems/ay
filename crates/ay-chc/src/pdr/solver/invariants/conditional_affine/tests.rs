// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcSort;

fn model(pairs: &[(&str, i128)]) -> FxHashMap<String, i128> {
    pairs.iter().map(|(k, v)| ((*k).to_string(), *v)).collect()
}

#[test]
fn affine_kernel_map_skips_models_missing_vars() {
    let vars = vec![
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("y", ChcSort::Int),
    ];
    let mut name_to_idx: FxHashMap<&str, usize> = FxHashMap::default();
    for (idx, v) in vars.iter().enumerate() {
        name_to_idx.insert(v.name.as_str(), idx);
    }

    let m1 = model(&[("x", 1), ("y", 0)]);
    let m2 = model(&[("x", 2)]);
    let models = vec![&m1, &m2];
    assert!(compute_affine_kernel_map(&vars, &name_to_idx, &models).is_empty());
}

#[test]
fn discovers_parity_conditional_kernel_invariant() {
    // Data points satisfy:
    // odd z:  2*x - y = 5
    // even z: 2*x - y = 3
    let vars = vec![
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("y", ChcSort::Int),
        ChcVar::new("z", ChcSort::Int),
    ];

    let models = vec![
        model(&[("x", 3), ("y", 1), ("z", 5)]),
        model(&[("x", 4), ("y", 3), ("z", 5)]),
        model(&[("x", 3), ("y", 3), ("z", 4)]),
        model(&[("x", 4), ("y", 5), ("z", 4)]),
    ];

    let invs = discover_conditional_affine_invariants(&vars, &models);
    let inv = invs
        .iter()
        .find(|inv| {
            inv.parity_var_idx == 2
                && inv.coefficients == vec![2, -1, 0]
                && inv.k_even == 3
                && inv.k_odd == 5
        })
        .unwrap_or_else(|| panic!("expected conditional invariant; got {invs:?}"));

    let expr = inv.to_expr(&vars);

    let lhs = ChcExpr::add(
        ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(vars[0].clone())),
        ChcExpr::neg(ChcExpr::var(vars[1].clone())),
    );
    let parity = ChcExpr::mod_op(ChcExpr::var(vars[2].clone()), ChcExpr::int(2));
    let rhs = ChcExpr::add(ChcExpr::int(3), ChcExpr::mul(ChcExpr::int(2), parity));
    let expected = ChcExpr::eq(lhs, rhs);

    assert_eq!(expr, expected);
}

#[test]
fn discovered_invariants_are_sorted_deterministically() {
    // Data supports multiple conditional invariants across different parity variables:
    // - partition by z mod 2 yields: x = 1 when z even, x = 3 when z odd
    // - partition by w mod 2 yields: y = 2 when w even, y = 4 when w odd
    let vars = vec![
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("y", ChcSort::Int),
        ChcVar::new("z", ChcSort::Int),
        ChcVar::new("w", ChcSort::Int),
    ];

    let models = vec![
        model(&[("x", 1), ("y", 2), ("z", 0), ("w", 0)]),
        model(&[("x", 1), ("y", 4), ("z", 0), ("w", 1)]),
        model(&[("x", 3), ("y", 2), ("z", 1), ("w", 0)]),
        model(&[("x", 3), ("y", 4), ("z", 1), ("w", 1)]),
    ];

    let invs = discover_conditional_affine_invariants(&vars, &models);
    assert!(
        invs.len() >= 2,
        "expected multiple invariants; got {invs:?}"
    );

    // The key property: output is deterministically sorted.
    let mut sorted = invs.clone();
    sorted.sort_by(|a, b| {
        a.parity_var_idx
            .cmp(&b.parity_var_idx)
            .then_with(|| a.coefficients.cmp(&b.coefficients))
            .then_with(|| a.k_even.cmp(&b.k_even))
            .then_with(|| a.k_odd.cmp(&b.k_odd))
    });
    assert_eq!(
        invs, sorted,
        "invariants should be sorted deterministically"
    );
}

#[test]
fn normalize_affine_handles_i64_min_coefficients() {
    let mut coeffs = vec![i128::from(i64::MIN), 0];
    let mut k = 0;
    normalize_affine(&mut coeffs, &mut k).unwrap();
    assert_eq!(coeffs, vec![1, 0]);
    assert_eq!(k, 0);
}

/// i128::MIN's magnitude (2^127) cannot be represented as an i128 gcd;
/// normalize_affine must fail closed rather than wrap.
#[test]
fn normalize_affine_fails_closed_on_i128_min_coefficients() {
    let mut coeffs = vec![i128::MIN, 0];
    let mut k = 0;
    assert!(normalize_affine(&mut coeffs, &mut k).is_none());
}

// ========================================================================
// collect_linear overflow edge case tests (#1965)
// ========================================================================

/// Test overflow path: scale.checked_mul(*n) in Int handling (line 244)
/// Large constant multiplied by large scale should return None.
#[test]
fn collect_linear_overflow_large_constant_times_scale() {
    let x = ChcVar::new("x", ChcSort::Int);
    let _vars = [x];
    let name_to_idx: FxHashMap<&str, usize> = [("x", 0)].into_iter().collect();

    // expr = i128::MAX (a large constant)
    let expr = ChcExpr::Int(i128::MAX);
    let mut coeffs = vec![0i128];
    let mut constant = 0i128;

    // scale = 2 would cause overflow: 2 * i128::MAX > i128::MAX
    let result = collect_linear(&expr, 2, &name_to_idx, &mut coeffs, &mut constant);
    assert!(result.is_none(), "expected None on overflow, got Some");
}

/// Test overflow path: constant.checked_add() in Int handling (line 244)
/// Adding to an already large constant should return None.
#[test]
fn collect_linear_overflow_constant_accumulation() {
    let x = ChcVar::new("x", ChcSort::Int);
    let _vars = [x];
    let name_to_idx: FxHashMap<&str, usize> = [("x", 0)].into_iter().collect();

    let expr = ChcExpr::Int(1);
    let mut coeffs = vec![0i128];
    let mut constant = i128::MAX; // Already at max

    // Adding 1 * 1 = 1 should overflow
    let result = collect_linear(&expr, 1, &name_to_idx, &mut coeffs, &mut constant);
    assert!(result.is_none(), "expected None on overflow, got Some");
}

/// Test overflow path: coeffs[idx].checked_add(scale) in Var handling (line 249)
/// Repeated variable occurrences accumulating coefficients should return None.
#[test]
fn collect_linear_overflow_coefficient_accumulation() {
    let x = ChcVar::new("x", ChcSort::Int);
    let _vars = [x.clone()];
    let name_to_idx: FxHashMap<&str, usize> = [("x", 0)].into_iter().collect();

    // expr = x (the variable)
    let expr = ChcExpr::var(x);
    let mut coeffs = vec![i128::MAX]; // Already at max
    let mut constant = 0i128;

    // Adding scale=1 to i128::MAX should overflow
    let result = collect_linear(&expr, 1, &name_to_idx, &mut coeffs, &mut constant);
    assert!(result.is_none(), "expected None on overflow, got Some");
}

/// Test overflow path: scale.checked_neg() in Neg/Sub handling (lines 253, 262)
/// Negating i64::MIN should return None (cannot represent as positive i64).
#[test]
fn collect_linear_overflow_negate_i64_min() {
    let x = ChcVar::new("x", ChcSort::Int);
    let _vars = [x.clone()];
    let name_to_idx: FxHashMap<&str, usize> = [("x", 0)].into_iter().collect();

    // expr = -x (negation of variable)
    let expr = ChcExpr::neg(ChcExpr::var(x));
    let mut coeffs = vec![0i128];
    let mut constant = 0i128;

    // scale = i128::MIN, then checked_neg() would overflow
    let result = collect_linear(&expr, i128::MIN, &name_to_idx, &mut coeffs, &mut constant);
    assert!(result.is_none(), "expected None on overflow, got Some");
}

/// Test overflow path: scale.checked_mul(*k) in Mul handling (line 268)
/// Large scale multiplied by large coefficient literal should return None.
#[test]
fn collect_linear_overflow_scale_times_literal() {
    let x = ChcVar::new("x", ChcSort::Int);
    let _vars = [x.clone()];
    let name_to_idx: FxHashMap<&str, usize> = [("x", 0)].into_iter().collect();

    // expr = i128::MAX * x
    let expr = ChcExpr::mul(ChcExpr::Int(i128::MAX), ChcExpr::var(x));
    let mut coeffs = vec![0i128];
    let mut constant = 0i128;

    // scale = 2 would cause overflow: 2 * i128::MAX > i128::MAX
    let result = collect_linear(&expr, 2, &name_to_idx, &mut coeffs, &mut constant);
    assert!(result.is_none(), "expected None on overflow, got Some");
}

/// Test non-overflow case: normal linear expression works correctly.
#[test]
fn collect_linear_normal_case_works() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let _vars = [x.clone(), y.clone()];
    let name_to_idx: FxHashMap<&str, usize> = [("x", 0), ("y", 1)].into_iter().collect();

    // expr = 2*x + 3 - y = 2*x + (-1)*y + 3
    let expr = ChcExpr::sub(
        ChcExpr::add(
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x)),
            ChcExpr::Int(3),
        ),
        ChcExpr::var(y),
    );
    let mut coeffs = vec![0i128, 0i128];
    let mut constant = 0i128;

    let result = collect_linear(&expr, 1, &name_to_idx, &mut coeffs, &mut constant);
    assert!(result.is_some(), "expected Some for valid expression");
    assert_eq!(coeffs, vec![2, -1], "coefficients mismatch");
    assert_eq!(constant, 3, "constant mismatch");
}
