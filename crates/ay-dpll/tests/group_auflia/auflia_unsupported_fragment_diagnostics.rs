// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ntest::timeout;

#[test]
#[timeout(60_000)]
fn div_in_unsupported_mixed_arith_reports_unsupported_arithmetic_fragment() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const x Int)
        (declare-const d Int)
        (declare-const q Int)
        (declare-const r Real)
        (declare-const a (Array Int Int))
        (assert (= q (div x d)))
        (assert (= r (to_real (* x x))))
        (assert (= (select a q) 1))
        (check-sat)
        (get-info :reason-unknown)
        (get-info :all-statistics)
    "#;

    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output[0], "unknown",
        "expected unsupported mixed arithmetic with div to fail closed: {output:?}"
    );
    assert_eq!(
        output[1], "(:reason-unknown (unsupported arithmetic))",
        "div/mod Unknown should identify the arithmetic fragment: {output:?}"
    );
    assert!(
        output[2].contains(".unsupported-fragment") && output[2].contains("\"arithmetic-div-mod\""),
        "missing AUFLIA arithmetic-fragment route statistics: {output:?}"
    );
}

#[test]
#[timeout(60_000)]
fn mixed_nonlinear_real_without_div_keeps_generic_incomplete_reason() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const x Int)
        (declare-const r Real)
        (declare-const a (Array Int Int))
        (assert (= r (to_real (* x x))))
        (assert (= (select a x) 1))
        (check-sat)
        (get-info :reason-unknown)
        (get-info :all-statistics)
    "#;

    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output[0], "unknown",
        "mixed nonlinear Int/Real remains fail-closed without LRA combination: {output:?}"
    );
    assert_eq!(
        output[1], "(:reason-unknown incomplete)",
        "a div/mod-free QfUfnira gap must keep its generic reason: {output:?}"
    );
    assert!(
        !output[2].contains(".unsupported-fragment"),
        "div/mod-free QfUfnira must not mint an arithmetic-div-mod diagnostic: {output:?}"
    );
}

#[test]
#[timeout(60_000)]
fn eliminated_constant_div_in_mixed_arith_keeps_generic_incomplete_reason() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const x Int)
        (declare-const q Int)
        (declare-const r Real)
        (declare-const a (Array Int Int))
        (assert (= q (div x 2)))
        (assert (= r (to_real (* x x))))
        (assert (= (select a q) 1))
        (check-sat)
        (get-info :reason-unknown)
        (get-info :all-statistics)
    "#;

    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output[0], "unknown",
        "mixed nonlinear Int/Real remains fail-closed after constant-div elimination: {output:?}"
    );
    assert_eq!(
        output[1], "(:reason-unknown incomplete)",
        "an eliminated constant div must not be reported as a surviving capability gap: {output:?}"
    );
    assert!(
        !output[2].contains(".unsupported-fragment"),
        "eliminated constant div must not mint an arithmetic-div-mod diagnostic: {output:?}"
    );
}

#[test]
#[timeout(60_000)]
fn qf_auflia_residual_symbolic_divisor_fails_closed_after_preprocessing() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (declare-const result Int)
        (assert (= x 1))
        (assert (> y 1))
        (assert (= result 1))
        (assert (= result (div x y)))
        (assert (= (select a result) 7))
        (check-sat)
        (get-info :reason-unknown)
        (get-info :all-statistics)
    "#;

    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output[0], "unknown",
        "residual symbolic AUFLIA div must not produce a trusted SAT result: {output:?}"
    );
    assert_eq!(
        output[1], "(:reason-unknown (unsupported arithmetic))",
        "residual symbolic AUFLIA div should keep structured arithmetic diagnostics: {output:?}"
    );
    assert!(
        output[2].contains(".unsupported-fragment") && output[2].contains("\"arithmetic-div-mod\""),
        "missing residual AUFLIA div/mod route statistics: {output:?}"
    );
}

#[test]
#[timeout(60_000)]
fn qf_auflia_residual_symbolic_modulus_fails_closed_after_preprocessing() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (declare-const result Int)
        (assert (= x 1))
        (assert (> y 1))
        (assert (= result 1))
        (assert (= result (mod x y)))
        (assert (= (select a result) 7))
        (check-sat)
        (get-info :reason-unknown)
        (get-info :all-statistics)
    "#;

    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output[0], "unknown",
        "residual symbolic AUFLIA mod must not produce a trusted SAT result: {output:?}"
    );
    assert_eq!(
        output[1], "(:reason-unknown (unsupported arithmetic))",
        "residual symbolic AUFLIA mod should keep structured arithmetic diagnostics: {output:?}"
    );
    assert!(
        output[2].contains(".unsupported-fragment") && output[2].contains("\"arithmetic-div-mod\""),
        "missing residual AUFLIA div/mod route statistics: {output:?}"
    );
}
