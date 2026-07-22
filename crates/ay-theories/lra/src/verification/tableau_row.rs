// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Bounds Consistency Invariants
// ========================================================================

// Tautological harnesses removed (Part of #4064):
// - proof_contradictory_bounds_detected: assumed lower > upper then asserted lower > upper
// - proof_equal_strict_bounds_contradictory: asserted x == x && (true || true)

// ========================================================================
// TableauRow Invariants
// ========================================================================

/// Coefficient lookup returns zero for missing variables
#[kani::proof]
fn proof_coeff_missing_is_zero() {
    let row = TableauRow::new(
        0,
        vec![(1, BigRational::from(BigInt::from(3)))],
        BigRational::zero(),
    );

    // Variable 2 is not in the row
    let coeff = row.coeff(2);
    assert!(coeff.is_zero(), "Missing variable has zero coefficient");
}

/// contains returns true iff variable in coeffs
#[kani::proof]
fn proof_contains_correctness() {
    let row = TableauRow::new(
        0,
        vec![
            (1, BigRational::from(BigInt::from(3))),
            (2, BigRational::from(BigInt::from(-5))),
        ],
        BigRational::zero(),
    );

    assert!(row.contains(1), "Variable 1 is in row");
    assert!(row.contains(2), "Variable 2 is in row");
    assert!(!row.contains(3), "Variable 3 is not in row");
    assert!(!row.contains(0), "Basic var 0 is not in coeffs");
}
