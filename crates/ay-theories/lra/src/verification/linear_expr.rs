// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// LinearExpr Invariants
// ========================================================================

/// Adding zero coefficient doesn't change the expression
#[kani::proof]
fn proof_add_term_zero_is_noop() {
    let mut expr = LinearExpr::zero();
    expr.add_term(0, BigRational::from(BigInt::from(5)));

    let coeff_before = expr
        .coeffs
        .iter()
        .find(|(v, _)| *v == 0)
        .map(|(_, c)| c.clone());

    // Adding zero should not change anything
    expr.add_term(0, BigRational::zero());

    let coeff_after = expr
        .coeffs
        .iter()
        .find(|(v, _)| *v == 0)
        .map(|(_, c)| c.clone());

    assert!(
        coeff_before == coeff_after,
        "Adding zero coefficient is a no-op"
    );
}

/// Adding opposite coefficients cancels to zero
#[kani::proof]
fn proof_add_term_cancellation() {
    let mut expr = LinearExpr::zero();

    let val: i32 = kani::any();
    kani::assume(val != 0 && val > -1000 && val < 1000);

    let coeff = BigRational::from(BigInt::from(val));
    let neg_coeff = -coeff.clone();

    expr.add_term(0, coeff);
    assert!(!expr.coeffs.is_empty(), "Should have one term");

    expr.add_term(0, neg_coeff);
    let has_var_0 = expr.coeffs.iter().any(|(v, _)| *v == 0);
    assert!(!has_var_0, "Opposite coefficients should cancel");
}

/// Scaling by 1 preserves the expression
#[kani::proof]
fn proof_scale_by_one() {
    let mut expr = LinearExpr::zero();

    let val: i32 = kani::any();
    kani::assume(val > -100 && val < 100);

    let coeff = BigRational::from(BigInt::from(val));
    expr.add_term(0, coeff.clone());
    expr.constant = BigRational::from(BigInt::from(42)).into();

    let coeff_before = expr
        .coeffs
        .iter()
        .find(|(v, _)| *v == 0)
        .map(|(_, c)| c.clone());
    let const_before = expr.constant.clone();

    expr.scale(&BigRational::one());

    let coeff_after = expr
        .coeffs
        .iter()
        .find(|(v, _)| *v == 0)
        .map(|(_, c)| c.clone());

    assert!(
        coeff_before == coeff_after,
        "Scale by 1 preserves coefficients"
    );
    assert!(
        expr.constant == const_before,
        "Scale by 1 preserves constant"
    );
}

/// Double negation returns to original
#[kani::proof]
fn proof_double_negation() {
    let mut expr = LinearExpr::zero();

    let val: i32 = kani::any();
    kani::assume(val > -100 && val < 100);

    expr.add_term(0, BigRational::from(BigInt::from(val)));
    expr.constant = BigRational::from(BigInt::from(17)).into();

    let coeff_original = expr
        .coeffs
        .iter()
        .find(|(v, _)| *v == 0)
        .map(|(_, c)| c.clone());
    let const_original = expr.constant.clone();

    expr.negate();
    expr.negate();

    let coeff_final = expr
        .coeffs
        .iter()
        .find(|(v, _)| *v == 0)
        .map(|(_, c)| c.clone());

    assert!(
        coeff_original == coeff_final,
        "Double negation restores coefficient"
    );
    assert!(
        expr.constant == const_original,
        "Double negation restores constant"
    );
}

/// is_constant returns true iff no variable terms
#[kani::proof]
fn proof_is_constant_correctness() {
    let expr = LinearExpr::zero();
    assert!(expr.is_constant(), "Zero expression is constant");

    let const_expr = LinearExpr::constant(BigRational::from(BigInt::from(42)));
    assert!(const_expr.is_constant(), "Constant expression is constant");

    let var_expr = LinearExpr::var(0);
    assert!(
        !var_expr.is_constant(),
        "Variable expression is not constant"
    );
}
