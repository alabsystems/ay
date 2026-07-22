// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// Kani Formal Verification Proofs
// ============================================================================
//
// These proofs verify core invariants of the NIA solver using bounded model checking.
// Areas covered:
// 1. Monomial degree and structure invariants
// 2. Sign computation properties (product_sign)
// 3. Tangent plane mathematical properties
// 4. Push/pop state management consistency
// 5. Sign constraint consistency

use super::*;
use crate::monomial::Monomial;
use crate::sign_lemmas::product_sign;
use crate::tangent_lemmas::{is_underestimate, tangent_plane};
use ay_core::nonlinear;
use num_traits::FromPrimitive;

// ========================================================================
// Monomial Invariants
// ========================================================================

/// Monomial degree equals length of vars
#[kani::proof]
fn proof_monomial_degree_equals_vars_len() {
    let len: usize = kani::any();
    kani::assume(len > 0 && len <= 4);

    let mut vars = Vec::new();
    for i in 0..len {
        vars.push(ay_core::term::TermId(i as u32));
    }

    let aux = ay_core::term::TermId(100);
    let mon = Monomial::new(vars.clone(), aux);

    assert!(mon.degree == len, "Degree equals vars length");
    assert!(mon.vars.len() == len, "Vars length preserved");
}

/// is_binary returns true iff degree == 2
#[kani::proof]
fn proof_monomial_is_binary_iff_degree_two() {
    let degree: usize = kani::any();
    kani::assume(degree > 0 && degree <= 4);

    let mut vars = Vec::new();
    for i in 0..degree {
        vars.push(ay_core::term::TermId(i as u32));
    }

    let aux = ay_core::term::TermId(100);
    let mon = Monomial::new(vars, aux);

    assert!(
        mon.is_binary() == (degree == 2),
        "is_binary iff degree == 2"
    );
}

/// is_square requires degree == 2 AND same variable
#[kani::proof]
fn proof_monomial_is_square_requires_same_vars() {
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();
    kani::assume(v1 < 100 && v2 < 100);

    let vars = vec![ay_core::term::TermId(v1), ay_core::term::TermId(v2)];
    let aux = ay_core::term::TermId(100);
    let mon = Monomial::new(vars, aux);

    assert!(
        mon.is_square() == (v1 == v2),
        "is_square iff both vars same"
    );
}

/// x() returns first element, y() returns second
#[kani::proof]
fn proof_monomial_x_y_accessors() {
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();
    kani::assume(v1 < 100 && v2 < 100);

    let vars = vec![ay_core::term::TermId(v1), ay_core::term::TermId(v2)];
    let aux = ay_core::term::TermId(100);
    let mon = Monomial::new(vars, aux);

    assert!(
        mon.x() == Some(ay_core::term::TermId(v1)),
        "x() returns first"
    );
    assert!(
        mon.y() == Some(ay_core::term::TermId(v2)),
        "y() returns second"
    );
}

/// aux_var is preserved
#[kani::proof]
fn proof_monomial_aux_var_preserved() {
    let aux_id: u32 = kani::any();
    kani::assume(aux_id < 1000);

    let vars = vec![ay_core::term::TermId(1), ay_core::term::TermId(2)];
    let aux = ay_core::term::TermId(aux_id);
    let mon = Monomial::new(vars, aux);

    assert!(mon.aux_var == aux, "aux_var is preserved");
}

// ========================================================================
// Sign Computation Invariants
// ========================================================================

/// product_sign with any zero factor returns 0
#[kani::proof]
fn proof_product_sign_zero_factor() {
    let s1: i32 = kani::any();
    let s2: i32 = kani::any();
    kani::assume(s1 >= -1 && s1 <= 1);
    kani::assume(s2 >= -1 && s2 <= 1);

    let with_zero = [s1, 0, s2];
    assert!(
        product_sign(&with_zero) == 0,
        "Zero factor yields zero product"
    );
}

/// product_sign of two positives is positive
#[kani::proof]
fn proof_product_sign_positive_positive() {
    assert!(product_sign(&[1, 1]) == 1, "pos * pos = pos");
}

/// product_sign of two negatives is positive
#[kani::proof]
fn proof_product_sign_negative_negative() {
    assert!(product_sign(&[-1, -1]) == 1, "neg * neg = pos");
}

/// product_sign of positive and negative is negative
#[kani::proof]
fn proof_product_sign_mixed() {
    assert!(product_sign(&[1, -1]) == -1, "pos * neg = neg");
    assert!(product_sign(&[-1, 1]) == -1, "neg * pos = neg");
}

/// product_sign is associative for non-zero factors
#[kani::proof]
fn proof_product_sign_associative() {
    let s1: i32 = kani::any();
    let s2: i32 = kani::any();
    let s3: i32 = kani::any();
    kani::assume(s1 == -1 || s1 == 1);
    kani::assume(s2 == -1 || s2 == 1);
    kani::assume(s3 == -1 || s3 == 1);

    let all = product_sign(&[s1, s2, s3]);
    let grouped_12_3 = product_sign(&[product_sign(&[s1, s2]), s3]);
    let grouped_1_23 = product_sign(&[s1, product_sign(&[s2, s3])]);

    assert!(all == grouped_12_3, "product_sign is associative");
    assert!(all == grouped_1_23, "product_sign is associative");
}

/// product_sign of even number of negatives is positive
#[kani::proof]
fn proof_product_sign_even_negatives() {
    assert!(product_sign(&[-1, -1]) == 1, "2 negatives = positive");
    assert!(
        product_sign(&[-1, -1, -1, -1]) == 1,
        "4 negatives = positive"
    );
}

/// product_sign of odd number of negatives is negative
#[kani::proof]
fn proof_product_sign_odd_negatives() {
    assert!(product_sign(&[-1]) == -1, "1 negative = negative");
    assert!(product_sign(&[-1, -1, -1]) == -1, "3 negatives = negative");
}

// ========================================================================
// Tangent Plane Mathematical Properties
// ========================================================================

/// tangent_plane at the model point equals x*y
///
/// Note: Uses fixed test values rather than symbolic inputs because
/// BigRational arithmetic with symbolic inputs causes CBMC memory issues.
#[kani::proof]
fn proof_tangent_plane_at_model_point() {
    // Test with fixed values to avoid CBMC memory issues with BigRational
    // T(a,b) at point (a,b) = a*b + b*a - a*b = a*b
    let a_rat = BigRational::from_i32(2).expect("constant i32");
    let b_rat = BigRational::from_i32(3).expect("constant i32");
    let t = tangent_plane(&a_rat, &b_rat, &a_rat, &b_rat);
    let ab = &a_rat * &b_rat;
    assert!(t == ab, "T(2,3) at (2,3) = 2*3 = 6");

    // Test with negatives
    let a2 = BigRational::from_i32(-1).expect("constant i32");
    let b2 = BigRational::from_i32(4).expect("constant i32");
    let t2 = tangent_plane(&a2, &b2, &a2, &b2);
    let ab2 = &a2 * &b2;
    assert!(t2 == ab2, "T(-1,4) at (-1,4) = -4");

    // Test with zeros
    let a3 = BigRational::from_i32(0).expect("constant i32");
    let b3 = BigRational::from_i32(5).expect("constant i32");
    let t3 = tangent_plane(&a3, &b3, &a3, &b3);
    let ab3 = &a3 * &b3;
    assert!(t3 == ab3, "T(0,5) at (0,5) = 0");
}

/// tangent_plane is linear in x (T(x1,y) - T(x2,y) = b*(x1-x2))
///
/// Note: Uses fixed test values to avoid CBMC memory issues with BigRational.
#[kani::proof]
fn proof_tangent_plane_linear_in_x() {
    // T(x,y) = a*y + b*x - a*b
    // T(x1,y) - T(x2,y) = b*x1 - b*x2 = b*(x1-x2)
    let a = BigRational::from_i32(2).expect("constant i32");
    let b = BigRational::from_i32(3).expect("constant i32");

    // Test: T(5,4) - T(1,4) should equal 3*(5-1) = 12
    let x1 = BigRational::from_i32(5).expect("constant i32");
    let x2 = BigRational::from_i32(1).expect("constant i32");
    let y = BigRational::from_i32(4).expect("constant i32");

    let t1 = tangent_plane(&a, &b, &x1, &y);
    let t2 = tangent_plane(&a, &b, &x2, &y);

    let diff = &t1 - &t2;
    let expected = &b * (&x1 - &x2);

    assert!(diff == expected, "Tangent plane is linear in x");
}

/// tangent_plane is linear in y (T(x,y1) - T(x,y2) = a*(y1-y2))
///
/// Note: Uses fixed test values to avoid CBMC memory issues with BigRational.
#[kani::proof]
fn proof_tangent_plane_linear_in_y() {
    // T(x,y) = a*y + b*x - a*b
    // T(x,y1) - T(x,y2) = a*y1 - a*y2 = a*(y1-y2)
    let a = BigRational::from_i32(2).expect("constant i32");
    let b = BigRational::from_i32(3).expect("constant i32");

    // Test: T(4,5) - T(4,1) should equal 2*(5-1) = 8
    let x = BigRational::from_i32(4).expect("constant i32");
    let y1 = BigRational::from_i32(5).expect("constant i32");
    let y2 = BigRational::from_i32(1).expect("constant i32");

    let t1 = tangent_plane(&a, &b, &x, &y1);
    let t2 = tangent_plane(&a, &b, &x, &y2);

    let diff = &t1 - &t2;
    let expected = &a * (&y1 - &y2);

    assert!(diff == expected, "Tangent plane is linear in y");
}

/// is_underestimate: same sign displacements give underestimate
///
/// Note: Uses fixed test values to avoid CBMC memory issues with BigRational.
#[kani::proof]
fn proof_is_underestimate_same_sign_quadrant() {
    // From (2, 3):
    // - (3, 4): dx=1, dy=1 (both positive) -> underestimate
    // - (1, 2): dx=-1, dy=-1 (both negative) -> underestimate
    // - (3, 2): dx=1, dy=-1 (mixed) -> overestimate
    // - (1, 4): dx=-1, dy=1 (mixed) -> overestimate
    let a = BigRational::from_i32(2).expect("constant i32");
    let b = BigRational::from_i32(3).expect("constant i32");

    // First quadrant (both positive) -> underestimate
    let x1 = BigRational::from_i32(3).expect("constant i32");
    let y1 = BigRational::from_i32(4).expect("constant i32");
    assert!(
        is_underestimate(&a, &b, &x1, &y1),
        "Same sign (++) is underestimate"
    );

    // Third quadrant (both negative) -> underestimate
    let x2 = BigRational::from_i32(1).expect("constant i32");
    let y2 = BigRational::from_i32(2).expect("constant i32");
    assert!(
        is_underestimate(&a, &b, &x2, &y2),
        "Same sign (--) is underestimate"
    );

    // Fourth quadrant (mixed) -> overestimate
    let x3 = BigRational::from_i32(3).expect("constant i32");
    let y3 = BigRational::from_i32(2).expect("constant i32");
    assert!(
        !is_underestimate(&a, &b, &x3, &y3),
        "Mixed sign (+-) is overestimate"
    );

    // Second quadrant (mixed) -> overestimate
    let x4 = BigRational::from_i32(1).expect("constant i32");
    let y4 = BigRational::from_i32(4).expect("constant i32");
    assert!(
        !is_underestimate(&a, &b, &x4, &y4),
        "Mixed sign (-+) is overestimate"
    );
}

// ========================================================================
// Push/Pop State Management
// ========================================================================
//
// Note: Full NiaSolver proofs involving TermStore/LiaSolver creation are
// too complex for Kani due to the nested solver state. We test the core
// Vec<usize> scope tracking logic directly. The actual push/pop behavior
// is verified through the unit tests in the tests module.

// Tautological harnesses removed (Part of #4064):
// - proof_scope_marker_tracking: tested bare Vec operations, not NIA solver logic
// - proof_scope_pop_empty_safe: tested Vec::pop() returns None on empty
// - proof_scope_push_pop_restores: tested Vec push/pop restores length
// - proof_scope_nested_lifo: tested Vec LIFO ordering (std library guarantee)
// - proof_asserted_truncation: tested Vec::truncate with hardcoded values

// ========================================================================
// Sign Constraint Tracking
// ========================================================================

/// sign_contradicts correctly identifies contradictions for all constraint types
#[kani::proof]
fn proof_sign_contradicts_all_constraints() {
    // Positive: contradicted by non-positive
    assert!(nonlinear::sign_contradicts(SignConstraint::Positive, 0));
    assert!(nonlinear::sign_contradicts(SignConstraint::Positive, -1));
    assert!(!nonlinear::sign_contradicts(SignConstraint::Positive, 1));

    // Negative: contradicted by non-negative
    assert!(nonlinear::sign_contradicts(SignConstraint::Negative, 0));
    assert!(nonlinear::sign_contradicts(SignConstraint::Negative, 1));
    assert!(!nonlinear::sign_contradicts(SignConstraint::Negative, -1));

    // Zero: contradicted by non-zero
    assert!(nonlinear::sign_contradicts(SignConstraint::Zero, 1));
    assert!(nonlinear::sign_contradicts(SignConstraint::Zero, -1));
    assert!(!nonlinear::sign_contradicts(SignConstraint::Zero, 0));

    // NonNegative: contradicted only by negative
    assert!(nonlinear::sign_contradicts(SignConstraint::NonNegative, -1));
    assert!(!nonlinear::sign_contradicts(SignConstraint::NonNegative, 0));
    assert!(!nonlinear::sign_contradicts(SignConstraint::NonNegative, 1));

    // NonPositive: contradicted only by positive
    assert!(nonlinear::sign_contradicts(SignConstraint::NonPositive, 1));
    assert!(!nonlinear::sign_contradicts(SignConstraint::NonPositive, 0));
    assert!(!nonlinear::sign_contradicts(
        SignConstraint::NonPositive,
        -1
    ));
}

/// sign_from_constraints returns correct sign for all constraint types
#[kani::proof]
fn proof_sign_from_constraints_all() {
    let dummy = ay_core::term::TermId(1);

    // Definite constraints return their sign
    let pos = vec![(SignConstraint::Positive, dummy)];
    let neg = vec![(SignConstraint::Negative, dummy)];
    let zero = vec![(SignConstraint::Zero, dummy)];
    assert!(nonlinear::sign_from_constraints(Some(&pos)) == Some(1));
    assert!(nonlinear::sign_from_constraints(Some(&neg)) == Some(-1));
    assert!(nonlinear::sign_from_constraints(Some(&zero)) == Some(0));

    // Non-definite constraints return None
    let nonneg = vec![(SignConstraint::NonNegative, dummy)];
    let nonpos = vec![(SignConstraint::NonPositive, dummy)];
    assert!(nonlinear::sign_from_constraints(Some(&nonneg)).is_none());
    assert!(nonlinear::sign_from_constraints(Some(&nonpos)).is_none());

    // No constraints returns None
    assert!(nonlinear::sign_from_constraints(None).is_none());
}
