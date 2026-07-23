// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_rational::Rational64;

use super::resolve_printed_la_generic_coefficients;

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
