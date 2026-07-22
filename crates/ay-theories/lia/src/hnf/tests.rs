// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::cutter::HnfCutter;
use super::matrix::IntMatrix;
use super::{compute_hnf, determinant_of_rectangular_matrix, divide_r_by_diagonal};
use ay_core::extended_gcd_bigint;
use num_bigint::BigInt;
use num_traits::{One, Zero};

#[test]
fn test_extended_gcd() {
    let (d, u, v) = extended_gcd_bigint(&BigInt::from(12), &BigInt::from(8));
    assert_eq!(d, BigInt::from(4));
    assert_eq!(&u * 12 + &v * 8, d);

    let (d, u, v) = extended_gcd_bigint(&BigInt::from(35), &BigInt::from(15));
    assert_eq!(d, BigInt::from(5));
    assert_eq!(&u * 35 + &v * 15, d);

    let (d, _u, v) = extended_gcd_bigint(&BigInt::from(0), &BigInt::from(5));
    assert_eq!(d, BigInt::from(5));
    // u * 0 = 0, so this verifies d = v * 5
    assert_eq!(BigInt::ZERO + &v * 5, d);
}

#[test]
fn test_matrix_basic() {
    let mut m = IntMatrix::new(2, 3);
    m.set(0, 0, BigInt::from(1));
    m.set(0, 1, BigInt::from(2));
    m.set(0, 2, BigInt::from(3));
    m.set(1, 0, BigInt::from(4));
    m.set(1, 1, BigInt::from(5));
    m.set(1, 2, BigInt::from(6));

    assert_eq!(m.get(0, 0), &BigInt::from(1));
    assert_eq!(m.get(1, 2), &BigInt::from(6));
}

#[test]
fn test_hnf_simple() {
    // Simple 2x2 matrix
    let mut a = IntMatrix::new(2, 2);
    a.set(0, 0, BigInt::from(4));
    a.set(0, 1, BigInt::from(6));
    a.set(1, 0, BigInt::from(2));
    a.set(1, 1, BigInt::from(3));

    let big_num = BigInt::from(1000000);
    let result = determinant_of_rectangular_matrix(&a, &big_num);
    assert!(result.is_some());

    let (det, basis) = result.unwrap();
    // det = gcd of 2x2 minors
    assert!(!det.is_zero());
    assert!(!basis.is_empty());
}

#[test]
fn test_hnf_coeff_guard() {
    // #437 regression: avoid unbounded BigInt extended GCD work in HNF.
    let mut a = IntMatrix::new(1, 2);
    a.set(0, 0, BigInt::one() << 300);
    a.set(0, 1, BigInt::from(1));

    let d = BigInt::from(2);
    assert!(compute_hnf(&a, &d).is_none());
}

#[test]
fn test_hnf_det_guard() {
    let mut a = IntMatrix::new(1, 1);
    a.set(0, 0, BigInt::from(1));

    let d = BigInt::one() << 300;
    assert!(compute_hnf(&a, &d).is_none());
}

#[test]
fn test_hnf_cutter_empty() {
    let cutter = HnfCutter::new();
    assert!(!cutter.has_constraints());
    let cuts = cutter.generate_cuts();
    assert!(cuts.is_empty());
}

#[test]
fn test_hnf_cutter_simple() {
    let mut cutter = HnfCutter::new();

    // Add constraint: 2*x + 3*y <= 7
    cutter.add_constraint(
        &[(0, BigInt::from(2)), (1, BigInt::from(3))],
        BigInt::from(7),
        true,
    );

    assert!(cutter.has_constraints());

    // With only one constraint, we likely won't get a cut
    // (need enough constraints to form a full-rank basis)
    let cuts = cutter.generate_cuts();
    // May or may not generate cuts depending on rank
    let _ = cuts;
}

#[test]
fn test_hnf_zero_diagonal_handling() {
    // Test the zero diagonal case that Z3 handles specially (#1062)
    // Matrix where initial diagonal is zero
    let mut a = IntMatrix::new(2, 2);
    a.set(0, 0, BigInt::from(0)); // Zero in initial diagonal
    a.set(0, 1, BigInt::from(6));
    a.set(1, 0, BigInt::from(4));
    a.set(1, 1, BigInt::from(8));

    let d = BigInt::from(24);
    let result = compute_hnf(&a, &d);
    // Zero diagonal requires prepare_pivot to swap columns before elimination.
    // Small coefficients should not trip the overflow guard, so we expect Some.
    let hnf = result.expect("compute_hnf should succeed for small zero-diagonal matrix");
    // HNF diagonal entries must be positive (lower-triangular form invariant)
    assert!(
        hnf.h.get(0, 0) > &BigInt::ZERO,
        "HNF diagonal h[0,0] must be positive, got {}",
        hnf.h.get(0, 0)
    );
}

/// Prove register_var is O(n) per call (Vec::contains) making
/// add_constraint O(V*N) where V=vars per constraint and N=total vars.
/// With N constraints of V vars each, total cost is O(N*V*N) = O(N²V).
/// A HashMap would make register_var O(1), reducing to O(N*V).
/// Bug: #3077 (HnfCutter quadratic register_var)
#[test]
fn test_register_var_is_linear_scan() {
    let mut cutter = HnfCutter::new();
    // Register 1000 unique vars; each register_var scans existing vec
    for i in 0..1000 {
        cutter.register_var(i);
    }
    assert_eq!(cutter.var_indices.len(), 1000);

    // Re-registering existing vars: each contains() scans all 1000
    // This is the O(N) per call pattern that makes add_constraint O(N²)
    for i in 0..1000 {
        cutter.register_var(i); // O(1000) scan each time
    }
    assert_eq!(cutter.var_indices.len(), 1000); // no duplicates added

    // add_constraint also uses position() which is O(N) per coefficient
    let coeffs: Vec<(usize, BigInt)> = (0..100).map(|i| (i, BigInt::from(i + 1))).collect();
    cutter.add_constraint(&coeffs, BigInt::from(50), true);
    assert_eq!(cutter.rows.len(), 1);
    // Each of the 100 coefficients triggered O(1000) position() scan
}

#[test]
fn test_hnf_d_equals_1() {
    // Regression test for d=1 case (#1062)
    // With d=1, the modular reduction becomes trivial, but we should
    // still process all rows and not break early
    let mut a = IntMatrix::new(1, 2);
    a.set(0, 0, BigInt::from(2));
    a.set(0, 1, BigInt::from(3));

    let d = BigInt::from(1);
    let result = compute_hnf(&a, &d);
    assert!(result.is_some(), "HNF with d=1 should succeed");

    let hnf = result.unwrap();
    // Diagonal should be positive
    assert!(
        hnf.h.get(0, 0) > &BigInt::zero(),
        "Diagonal should be positive"
    );
}

#[test]
fn test_divide_r_by_diagonal_exact_division() {
    let q = divide_r_by_diagonal(&BigInt::from(12), &BigInt::from(3), 0);
    assert_eq!(q, Some(BigInt::from(4)));
}

#[test]
fn test_divide_r_by_diagonal_invariant_violation_behavior() {
    let result =
        std::panic::catch_unwind(|| divide_r_by_diagonal(&BigInt::from(5), &BigInt::from(2), 1));

    if cfg!(debug_assertions) {
        assert!(
            result.is_err(),
            "debug builds should panic on HNF divisibility invariant violation"
        );
    } else {
        assert!(
            result.expect("release builds should not panic").is_none(),
            "release builds should return None on HNF divisibility invariant violation"
        );
    }
}
