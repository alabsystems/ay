// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_rational::Rational64;

use super::{
    carcara_printed_la_generic_literal_supported, printed_la_generic_unit_implication_is_supported,
    resolve_printed_la_generic_coefficients,
};

fn r(n: i64, d: i64) -> Rational64 {
    Rational64::new(n, d)
}

/// The lra_080 regression: an equality whose printed orientation
/// (`(= (- (* 2.0 r2)) (/ 70.0 10.0))`) is the negation of the internal one,
/// so the internal-orientation signs (`5/2`) do not cancel `r2` for the
/// checker; the printed-form repair must flip it to `-5/2`.
#[test]
fn repairs_reoriented_equality_sign() {
    let atoms = vec![
        ("(= (- (* 2.0 r2)) (/ 70.0 10.0))".to_string(), true),
        ("(= (* 3.0 r6) (- (/ 15.0 2.0)))".to_string(), true),
        ("(>= (+ r1 7.0) 6.0)".to_string(), true),
        (
            "(>= (+ (+ (- (* 2.0 r1)) (- (* 5.0 r2)) (* 3.0 r6)) (- (/ 4.0 3.0))) 45.0)"
                .to_string(),
            true,
        ),
    ];
    let existing = vec![r(5, 2), r(-1, 1), r(2, 1), r(1, 1)];
    let magnitudes = vec![r(5, 2), r(1, 1), r(2, 1), r(1, 1)];
    let out = resolve_printed_la_generic_coefficients(&atoms, &existing, &magnitudes);
    assert_eq!(out, vec![r(-5, 2), r(-1, 1), r(2, 1), r(1, 1)]);
}

/// A certificate whose printed orientation already cancels must be returned
/// byte-identical (no gratuitous re-signing of correct certificates).
#[test]
fn keeps_already_valid_certificate() {
    // x = 5 and x <= 3: e0 = x - 5 (eq), e1 = 3 - x (ineq). 1*(x-5)+1*(3-x) = -2 < 0.
    let atoms = vec![
        ("(= x 5.0)".to_string(), true),
        ("(<= x 3.0)".to_string(), true),
    ];
    let existing = vec![r(1, 1), r(1, 1)];
    let magnitudes = vec![r(1, 1), r(1, 1)];
    let out = resolve_printed_la_generic_coefficients(&atoms, &existing, &magnitudes);
    assert_eq!(out, vec![r(1, 1), r(1, 1)]);
}

/// The wrong equality sign for `x = 5 ∧ x <= 3` must be repaired to `+1`
/// (`-1` leaves `8 - 2x`, which does not cancel).
#[test]
fn repairs_pure_equality_inequality_pair() {
    let atoms = vec![
        ("(= x 5.0)".to_string(), true),
        ("(<= x 3.0)".to_string(), true),
    ];
    let existing = vec![r(-1, 1), r(1, 1)];
    let magnitudes = vec![r(1, 1), r(1, 1)];
    let out = resolve_printed_la_generic_coefficients(&atoms, &existing, &magnitudes);
    assert_eq!(out, vec![r(1, 1), r(1, 1)]);
}

/// The QF_ALIA array-swap regression cancels to exactly zero, but one
/// positively weighted hypothesis is strict (`b[0] > b[1]`). That is the
/// contradiction `0 > 0`, so the printed-form search must accept it and repair
/// the two equality orientations.
#[test]
fn repairs_strict_zero_opaque_select_chain() {
    let atoms = vec![
        ("(= (select b 1) (select a 1))".to_string(), true),
        ("(<= (select a 0) (select a 1))".to_string(), true),
        ("(> (select b 0) (select b 1))".to_string(), true),
        ("(= (select b 0) (select a 0))".to_string(), true),
    ];
    let existing = vec![r(-1, 1), r(1, 1), r(1, 1), r(1, 1)];
    let magnitudes = vec![r(1, 1), r(1, 1), r(1, 1), r(1, 1)];
    let out = resolve_printed_la_generic_coefficients(&atoms, &existing, &magnitudes);
    assert_eq!(out, vec![r(1, 1), r(1, 1), r(1, 1), r(-1, 1)]);
}

/// A conflict with a non-arithmetic (unparseable-as-linear) atom must fall
/// back to the existing coefficients unchanged (no false repair).
#[test]
fn falls_back_on_unhandled_atom() {
    let atoms = vec![
        ("(distinct x 5.0)".to_string(), true),
        ("(<= x 3.0)".to_string(), true),
    ];
    let existing = vec![r(3, 1), r(7, 1)];
    let magnitudes = vec![r(3, 1), r(7, 1)];
    let out = resolve_printed_la_generic_coefficients(&atoms, &existing, &magnitudes);
    assert_eq!(out, existing);
}

/// An uninterpreted term (`(f 0)`) is treated as an opaque variable keyed by
/// its printed string, so a conflict over it still cancels and validates.
#[test]
fn opaque_application_is_one_variable() {
    // -2*(f 0) = 1 (eq) and (f 0) >= 1 (ineq): 1*(f0-... ) chosen by repair.
    let atoms = vec![
        ("(= (* (- 2.0) (f 0)) 1.0)".to_string(), true),
        ("(>= (f 0) 1.0)".to_string(), true),
    ];
    // eq: e = -2*(f0) - 1; ineq: e = (f0) - 1. To cancel (f0): a_eq*(-2) + a_ineq*1 = 0.
    // With |a_ineq| = 2, a_eq = 1 gives -2*(f0) + 2*(f0) = 0; const -1*1 + 2*(-1) = -3 < 0.
    let existing = vec![r(-1, 1), r(2, 1)];
    let magnitudes = vec![r(1, 1), r(2, 1)];
    let out = resolve_printed_la_generic_coefficients(&atoms, &existing, &magnitudes);
    // a_eq must be +1 (so -2*(f0) cancels +2*(f0)); ineq magnitude 2.
    assert_eq!(out, vec![r(1, 1), r(2, 1)]);
}

#[test]
fn authored_linear_cancellation_implication_is_supported() {
    assert!(printed_la_generic_unit_implication_is_supported(
        "(< (+ I W (- W)) 0)",
        "(< I 0)",
    ));
}

#[test]
fn authored_computed_coefficient_implication_is_rejected() {
    assert!(!printed_la_generic_unit_implication_is_supported(
        "(< (* (+ 1 1) x) 0)",
        "(< (* 2 x) 0)",
    ));
}

#[test]
fn authored_unary_plus_implication_is_rejected() {
    assert!(!printed_la_generic_unit_implication_is_supported(
        "(< (+ x) 0)",
        "(< (+ x) 0)",
    ));
}

#[test]
fn authored_non_implication_is_rejected() {
    assert!(!printed_la_generic_unit_implication_is_supported(
        "(< x 0)",
        "(< (+ x 1) 0)",
    ));
}

/// Carcara's `LinearComb::from_term` makes a product with no direct numeric
/// coefficient ONE opaque atom, and so does AY's linearizer once it meets a
/// second nonconstant factor. The printed grammar that decides whether a
/// published `la_generic` row is checkable must read it the same way, or the
/// exporter degrades a provable step to `hole`.
///
/// MEASURED on pinned carcara 1.1.0 (git 9a352ee): the three-row Farkas
/// conflict over `sum`, `i`, `sq` that shares `(* i i)` between two literals
/// checks `valid` under `:rule la_generic :args (-1 -1 1)`. The exported
/// document is pinned end to end by
/// `group_proof::export_alethe_validation::pinned_carcara_accepts_a_shared_opaque_nonlinear_product`.
#[test]
fn shared_opaque_nonlinear_product_is_one_printed_la_generic_atom() {
    assert!(carcara_printed_la_generic_literal_supported(
        "(not (= sq (* i i)))"
    ));
    assert!(carcara_printed_la_generic_literal_supported(
        "(<= (+ (* sum 2) (* i 3) 1) (+ (* i 2) (* i i) 1))"
    ));
    // Three nonconstant factors are still one atom.
    assert!(carcara_printed_la_generic_literal_supported(
        "(<= (* i i i) x)"
    ));
}

/// The opaque-atom reading is admitted only for factors whose nonconstancy is
/// STRUCTURALLY certain, exactly as `wire_rule::carcara_linear_term_supported`
/// requires: a computed constant must never be mistaken for the first of the
/// two nonconstant factors, because AY and Carcara scale such a product
/// differently.
#[test]
fn computed_coefficient_is_still_refused_by_the_printed_grammar() {
    assert!(!carcara_printed_la_generic_literal_supported(
        "(<= (* (+ 1 1) x) 0)"
    ));
    assert!(!carcara_printed_la_generic_literal_supported(
        "(<= (* (/ x y) z) 0)"
    ));
    // A direct numeric coefficient is the ordinary linear shape and stays
    // supported on either side.
    assert!(carcara_printed_la_generic_literal_supported(
        "(<= (* 2 x) 0)"
    ));
    assert!(carcara_printed_la_generic_literal_supported(
        "(<= (* x (- 2)) 0)"
    ));
}

/// The authored-assume implication bridge keeps its narrow grammar: it needs
/// only sums and direct numeric scaling, and its own coefficient replay
/// declines nonlinear products anyway.
#[test]
fn the_authored_assume_bridge_still_refuses_nonlinear_products() {
    assert!(!printed_la_generic_unit_implication_is_supported(
        "(<= (* i i) 0)",
        "(<= (* i i) 1)",
    ));
}
