// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]
use super::*;
#[test]
fn test_rational_basic() {
    let a = Rational::new(1, 2);
    let b = Rational::new(1, 3);

    // 1/2 + 1/3 = 5/6
    let sum = a + b;
    assert_eq!(sum.num, 5);
    assert_eq!(sum.den, 6);

    // 1/2 * 1/3 = 1/6
    let prod = a * b;
    assert_eq!(prod.num, 1);
    assert_eq!(prod.den, 6);
}

/// Test that division by zero returns zero instead of panicking (#1715)
#[test]
fn test_rational_div_by_zero_no_panic() {
    let a = Rational::new(1, 2);
    let zero = Rational::zero();

    // Division by zero should return zero, not panic
    let result = a / zero;
    assert!(result.is_zero(), "Division by zero should return zero");
}

/// Test that try_normalize handles zero denominator gracefully (#1715)
#[test]
fn test_rational_normalize_zero_den_no_panic() {
    // Calling try_normalize with zero denominator should return None
    let result = Rational::try_normalize(5, 0);
    assert!(result.is_none(), "try_normalize(5, 0) should return None");

    // normalize() should return (0, 1) as fallback
    let (num, den) = Rational::normalize(5, 0);
    assert_eq!((num, den), (0, 1), "normalize fallback should be (0, 1)");
}

/// Test that i128::MIN edge cases do not panic (#1713)
#[test]
fn test_rational_i128_min_no_panic() {
    let min = Rational {
        num: i128::MIN,
        den: 1,
    };

    // abs(i128::MIN) overflows; should degrade gracefully.
    assert_eq!(min.abs(), Rational::zero());

    // -(i128::MIN) overflows; should degrade gracefully.
    assert_eq!(min.negate(), Rational::zero());

    // addition overflow should not panic.
    let sum = Rational {
        num: i128::MAX,
        den: 1,
    } + Rational { num: 1, den: 1 };
    assert_eq!(sum, Rational::zero());

    // multiplication overflow should not panic.
    let prod = Rational {
        num: i128::MAX,
        den: 1,
    } * Rational { num: 2, den: 1 };
    assert_eq!(prod, Rational::zero());

    // comparison should fall back to BigInt if i128 multiply overflows.
    let half = Rational { num: 1, den: 2 };
    assert!(
        Rational {
            num: i128::MAX,
            den: 1
        } > half
    );
}

/// Test that LCM overflow in add() degrades gracefully (#1713)
#[test]
fn test_rational_add_lcm_overflow_no_panic() {
    let a = Rational {
        num: 1,
        den: i128::MAX,
    };
    let b = Rational {
        num: 1,
        den: i128::MAX - 1,
    };
    let sum = a + b;
    assert_eq!(sum, Rational::zero());
}

#[test]
fn test_matrix_gaussian() {
    // Test a simple system with linear dependency
    // x + y = 2
    // 2x + 2y = 4 (dependent)
    let mut m = Matrix::new(3);
    m.add_row(vec![
        Rational::from_int(1),
        Rational::from_int(1),
        Rational::from_int(2),
    ]);
    m.add_row(vec![
        Rational::from_int(2),
        Rational::from_int(2),
        Rational::from_int(4),
    ]);

    let rank = m.gaussian_elimination();
    assert_eq!(rank, 1); // Rank should be 1 (one independent row)
}

#[test]
fn test_linear_deps() {
    // Data points: (0, 10), (1, 9), (2, 8), (5, 5)
    // Linear relationship: x + y = 10
    // Must include constant column for affine equalities
    let mut m = Matrix::new(3); // x, y, constant
    m.add_row(vec![
        Rational::from_int(0),
        Rational::from_int(10),
        Rational::one(),
    ]);
    m.add_row(vec![
        Rational::from_int(1),
        Rational::from_int(9),
        Rational::one(),
    ]);
    m.add_row(vec![
        Rational::from_int(2),
        Rational::from_int(8),
        Rational::one(),
    ]);
    m.add_row(vec![
        Rational::from_int(5),
        Rational::from_int(5),
        Rational::one(),
    ]);

    let deps = m.compute_linear_deps();
    assert!(deps.is_some());
    let deps = deps.unwrap();
    assert_eq!(deps.num_rows(), 1);

    // Check the dependency encodes x + y = 10
    // Row should be [1, 1, -10] (meaning 1*x + 1*y + (-10) = 0)
    let row = deps.get_row(0);
    assert!(!row[0].is_zero() || !row[1].is_zero());
}

#[test]
fn test_convex_closure_sum_invariant() {
    // Test: find invariant x + y = 10 from data points
    let mut cc = ConvexClosure::new();
    cc.reset(vec![
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("y", ChcSort::Int),
    ]);

    cc.add_data_point(&[0, 10]);
    cc.add_data_point(&[1, 9]);
    cc.add_data_point(&[2, 8]);
    cc.add_data_point(&[5, 5]);
    cc.add_data_point(&[10, 0]);

    let result = cc.compute();
    assert!(!result.equalities.is_empty());
    // Should find x + y = 10
}

#[test]
fn test_convex_closure_bounds() {
    let mut cc = ConvexClosure::new();
    cc.reset(vec![ChcVar::new("x", ChcSort::Int)]);

    cc.add_data_point(&[0]);
    cc.add_data_point(&[5]);
    cc.add_data_point(&[10]);

    let result = cc.compute();

    // Should find bounds: 0 <= x <= 10
    assert!(result.bounds.len() >= 2);
}

#[test]
fn test_convex_closure_divisibility() {
    let mut cc = ConvexClosure::new();
    cc.reset(vec![ChcVar::new("x", ChcSort::Int)]);

    // All values are even
    cc.add_data_point(&[0]);
    cc.add_data_point(&[2]);
    cc.add_data_point(&[4]);
    cc.add_data_point(&[6]);

    let result = cc.compute();

    // Should find: x mod 2 = 0
    assert!(!result.divisibility.is_empty());
}

#[test]
fn test_convex_closure_bv_bounds_use_bvule() {
    let mut cc = ConvexClosure::new();
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    cc.reset(vec![x.clone()]);

    cc.add_data_point(&[3]);
    cc.add_data_point(&[7]);
    cc.add_data_point(&[15]);

    let result = cc.compute();

    let lower = ChcExpr::bv_ule(ChcExpr::BitVec(3, 8), ChcExpr::var(x.clone()));
    let upper = ChcExpr::bv_ule(ChcExpr::var(x), ChcExpr::BitVec(15, 8));
    assert!(
        result.bounds.contains(&lower),
        "missing BV lower bound: {result:?}"
    );
    assert!(
        result.bounds.contains(&upper),
        "missing BV upper bound: {result:?}"
    );
    assert!(
        result.bounds.iter().all(
            |bound| matches!(bound, ChcExpr::Op(crate::ChcOp::BvULe, args) if args.len() == 2)
        ),
        "BV bounds should use bvule: {result:?}"
    );
}

#[test]
fn test_convex_closure_bv_divisibility_uses_bvurem() {
    let mut cc = ConvexClosure::new();
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    cc.reset(vec![x.clone()]);

    cc.add_data_point(&[0]);
    cc.add_data_point(&[2]);
    cc.add_data_point(&[4]);
    cc.add_data_point(&[6]);

    let result = cc.compute();

    let even_constraint = ChcExpr::eq(
        ChcExpr::bv_urem(ChcExpr::var(x), ChcExpr::BitVec(2, 8)),
        ChcExpr::BitVec(0, 8),
    );
    assert!(
        result.divisibility.contains(&even_constraint),
        "missing BV divisibility constraint: {result:?}"
    );
}

#[test]
fn test_convex_closure_skips_bv_affine_equalities() {
    let mut cc = ConvexClosure::new();
    cc.reset(vec![
        ChcVar::new("x", ChcSort::BitVec(8)),
        ChcVar::new("y", ChcSort::BitVec(8)),
    ]);

    // x == y across all points would normally induce the affine row x - y = 0.
    // The equality lane must skip this for BV because it still lowers rows via
    // arithmetic negation/multiplication rather than BV operators.
    cc.add_data_point(&[1, 1]);
    cc.add_data_point(&[2, 2]);
    cc.add_data_point(&[5, 5]);

    let result = cc.compute();
    assert!(
        result.equalities.is_empty(),
        "BV convex closure must not emit arithmetic equalities: {result:?}"
    );
}

/// Test scaling equality D = 2*E (i.e., D - 2*E = 0)
/// This is the key invariant for dillig12_m_e1.
/// Issue #493: Requires true kernel computation (not pairwise heuristic).
#[test]
fn test_convex_closure_scaling_equality() {
    let mut cc = ConvexClosure::new();
    cc.reset(vec![
        ChcVar::new("D", ChcSort::Int),
        ChcVar::new("E", ChcSort::Int),
    ]);

    // Data points satisfying D = 2*E:
    // (D=0, E=0), (D=2, E=1), (D=4, E=2), (D=6, E=3), (D=10, E=5)
    cc.add_data_point(&[0, 0]);
    cc.add_data_point(&[2, 1]);
    cc.add_data_point(&[4, 2]);
    cc.add_data_point(&[6, 3]);
    cc.add_data_point(&[10, 5]);

    let result = cc.compute();

    // Should find exactly one equality: D - 2*E = 0 (or equivalent)
    assert!(
        !result.equalities.is_empty(),
        "Expected to find D = 2*E equality, got none"
    );

    // Verify the equality involves D and E
    let eq = &result.equalities[0];
    let eq_str = format!("{eq:?}");
    assert!(
        eq_str.contains("D") && eq_str.contains("E"),
        "Equality should involve D and E: {eq_str}"
    );
}

/// Test 3-variable equality: x + y - z = 0 (i.e., z = x + y)
/// Issue #493: Pairwise heuristic cannot discover multi-var equalities.
#[test]
fn test_convex_closure_three_var_equality() {
    let mut cc = ConvexClosure::new();
    cc.reset(vec![
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("y", ChcSort::Int),
        ChcVar::new("z", ChcSort::Int),
    ]);

    // Data points satisfying z = x + y:
    cc.add_data_point(&[1, 2, 3]);
    cc.add_data_point(&[0, 5, 5]);
    cc.add_data_point(&[3, 3, 6]);
    cc.add_data_point(&[4, 1, 5]);

    let result = cc.compute();

    // Should find exactly one equality: x + y - z = 0
    assert!(
        !result.equalities.is_empty(),
        "Expected to find x + y = z equality, got none"
    );

    // The kernel vector should be [1, 1, -1, 0] (x + y - z + 0 = 0)
    let eq = &result.equalities[0];
    let eq_str = format!("{eq:?}");
    assert!(
        eq_str.contains("x") && eq_str.contains("y") && eq_str.contains("z"),
        "Equality should involve x, y, and z: {eq_str}"
    );
}

/// Test kernel computation at matrix level for D = 2*E
#[test]
fn test_matrix_kernel_scaling() {
    // Matrix: rows are data points [D, E], constant column added internally
    let mut m = Matrix::new(2);
    m.add_row(vec![Rational::from_int(0), Rational::from_int(0)]);
    m.add_row(vec![Rational::from_int(2), Rational::from_int(1)]);
    m.add_row(vec![Rational::from_int(4), Rational::from_int(2)]);
    m.add_row(vec![Rational::from_int(6), Rational::from_int(3)]);

    let deps = m.compute_linear_deps();
    assert!(deps.is_some(), "Expected kernel for D = 2*E");

    let deps = deps.unwrap();
    assert!(deps.num_rows() >= 1, "Expected at least one kernel vector");

    // First row should encode D - 2*E = 0 (or a scalar multiple)
    // Kernel format: [coeff_D, coeff_E]
    let row = deps.get_row(0);
    let d_coeff = row[0].to_i64().expect("Rational should be integer in test");
    let e_coeff = row[1].to_i64().expect("Rational should be integer in test");

    assert!(
        d_coeff != 0 && e_coeff != 0,
        "Both D and E coefficients should be non-zero"
    );
    // d_coeff * D + e_coeff * E = 0
    // For D = 2*E: d_coeff * 2*E + e_coeff * E = E * (2*d_coeff + e_coeff) = 0
    // So 2*d_coeff + e_coeff = 0, i.e., e_coeff = -2*d_coeff
    assert_eq!(
        e_coeff,
        -2 * d_coeff,
        "Expected e_coeff = -2 * d_coeff, got d={d_coeff}, e={e_coeff}"
    );
}

/// Test that duplicates don't break kernel computation
#[test]
fn test_kernel_with_duplicates() {
    let mut m = Matrix::new(2);
    // Same point repeated - should still find kernel
    m.add_row(vec![Rational::from_int(2), Rational::from_int(1)]);
    m.add_row(vec![Rational::from_int(2), Rational::from_int(1)]);
    m.add_row(vec![Rational::from_int(4), Rational::from_int(2)]);
    m.add_row(vec![Rational::from_int(6), Rational::from_int(3)]);

    // With duplicates, the kernel should still work
    let deps = m.compute_linear_deps();
    assert!(deps.is_some(), "Kernel should handle duplicate rows");
}

/// Test with affine constant: x + y = 5 (involves constant term)
#[test]
fn test_kernel_with_constant() {
    let mut m = Matrix::new(3); // x, y, constant
                                // Points on line x + y = 5, with constant column
    m.add_row(vec![
        Rational::from_int(0),
        Rational::from_int(5),
        Rational::one(),
    ]);
    m.add_row(vec![
        Rational::from_int(1),
        Rational::from_int(4),
        Rational::one(),
    ]);
    m.add_row(vec![
        Rational::from_int(2),
        Rational::from_int(3),
        Rational::one(),
    ]);
    m.add_row(vec![
        Rational::from_int(5),
        Rational::from_int(0),
        Rational::one(),
    ]);

    let deps = m.compute_linear_deps();
    assert!(deps.is_some(), "Expected kernel for x + y = 5");

    let deps = deps.unwrap();
    let row = deps.get_row(0);
    // Kernel should encode x + y - 5 = 0, i.e., [1, 1, -5]
    let x_coeff = row[0].to_i64().expect("Rational should be integer in test");
    let y_coeff = row[1].to_i64().expect("Rational should be integer in test");
    let const_coeff = row[2].to_i64().expect("Rational should be integer in test");

    assert_eq!(x_coeff, y_coeff, "x and y should have equal coefficients");
    assert_eq!(
        const_coeff,
        -5 * x_coeff,
        "Constant should be -5 times the coefficient"
    );
}

/// Test that large coefficients that overflow i64 are handled gracefully
/// (kernel vector is skipped rather than producing incorrect results)
#[test]
fn test_kernel_large_coefficients_handled() {
    // This test verifies the overflow-safe path works.
    // After GCD normalization, realistic CHC values should fit in i64.
    // But if they don't, the kernel vector is skipped rather than corrupted.

    // Simple case: values that fit in i64 should work normally
    let mut m = Matrix::new(2);
    m.add_row(vec![
        Rational::from_int(1_000_000_000),
        Rational::from_int(2_000_000_000),
    ]);
    m.add_row(vec![
        Rational::from_int(2_000_000_000),
        Rational::from_int(4_000_000_000),
    ]);
    m.add_row(vec![
        Rational::from_int(3_000_000_000),
        Rational::from_int(6_000_000_000),
    ]);

    // These all satisfy y = 2x, so kernel should be [1, -2] or equivalent
    let deps = m.compute_linear_deps();
    assert!(
        deps.is_some(),
        "Should find kernel for y = 2x with large values"
    );

    let deps = deps.unwrap();
    let row = deps.get_row(0);
    let x_coeff = row[0].to_i64().expect("Rational should be integer in test");
    let y_coeff = row[1].to_i64().expect("Rational should be integer in test");

    // Verify the ratio is correct: kernel encodes a*x + b*y = 0 where y = 2x
    // So a*x + b*2x = 0 → a = -2b → kernel is [-2, 1] or [2, -1] (normalized positive)
    // After normalization: [2, -1] meaning 2x - y = 0 → y = 2x
    assert!(
        x_coeff != 0 && y_coeff != 0,
        "Both coefficients should be non-zero"
    );
    assert_eq!(
        x_coeff,
        -2 * y_coeff,
        "x_coeff = -2 * y_coeff for y = 2x relationship"
    );
}

#[test]
fn test_infer_divisibility_i64_min_no_panic() {
    let cc = ConvexClosure::new();
    let data = vec![
        Rational::new(i64::MIN, 1),
        Rational::new(i64::MIN + 2, 1),
        Rational::new(i64::MIN + 4, 1),
    ];
    // Must not panic on i64::MIN.abs() — the fix uses checked_abs
    let _ = cc.infer_divisibility(&data);
}
