// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for `(mod x k)` / `(div x k)` with constant divisor in LIA (#1614).

use ntest::timeout;

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_constant_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x 2) 1))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_constant_unsat_contradiction() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x 2) 0))
        (assert (= (mod x 2) 1))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_negative_constant_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x (- 2)) 1))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_div_by_constant_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (div x 2) 0))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_div_by_negative_constant_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (div x (- 2)) 0))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_zero_unconstrained_sat() {
    // SMT-LIB 2.6 Ints: div/mod are total but their value when the divisor is 0
    // is UNCONSTRAINED (any integer is a valid model; consistent across
    // occurrences). So `(mod x 0)` may differ from `x`, hence `(not (= (mod x 0)
    // x))` is SATISFIABLE (a model picks `(mod x 0) != x`). AY used to pin
    // `(mod x 0) = x` and wrongly returned unsat here; commit fixing div/mod-by-0
    // made the zero-divisor value unconstrained (matching z3), so this is now sat.
    // (z3 itself returns `unknown` on this QF_LIA shape; AY is sound and decides.)
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (not (= (mod x 0) x)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_constant_check_sat_assuming_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 1))
        (check-sat-assuming ((= (mod x 2) 1)))
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_declared_qf_lra_int_mod_routes_to_lia_8969() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const n Int)
        (assert (<= 0 n))
        (assert (<= n 65535))
        (assert (< (mod n 2) 1))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_declared_qf_lra_int_integrality_is_not_relaxed_8969() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Int)
        (assert (= (* 2 x) 1))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Regression test for #2781: constant folding must use Euclidean division,
/// not Rust's truncation-toward-zero division.
///
/// SMT-LIB defines: a = b * (div a b) + (mod a b), with 0 <= (mod a b) < |b|.
/// Verified against Z3 for all four sign combinations.
#[test]
#[timeout(60_000)]
fn test_qf_lia_constant_folding_euclidean_division_2781() {
    // (div -7 2) = -4 (not -3)
    assert_eq!(
        crate::common::solve("(set-logic QF_LIA)(assert (= (div (- 7) 2) (- 4)))(check-sat)")
            .trim(),
        "sat"
    );

    // (mod -7 2) = 1 (not -1)
    assert_eq!(
        crate::common::solve("(set-logic QF_LIA)(assert (= (mod (- 7) 2) 1))(check-sat)").trim(),
        "sat"
    );

    // (div 7 -2) = -3 (not -4)
    assert_eq!(
        crate::common::solve("(set-logic QF_LIA)(assert (= (div 7 (- 2)) (- 3)))(check-sat)")
            .trim(),
        "sat"
    );

    // (mod 7 -2) = 1 (always non-negative)
    assert_eq!(
        crate::common::solve("(set-logic QF_LIA)(assert (= (mod 7 (- 2)) 1))(check-sat)").trim(),
        "sat"
    );

    // (div -7 -2) = 4 (not 3)
    assert_eq!(
        crate::common::solve("(set-logic QF_LIA)(assert (= (div (- 7) (- 2)) 4))(check-sat)")
            .trim(),
        "sat"
    );

    // (mod -7 -2) = 1 (always non-negative)
    assert_eq!(
        crate::common::solve("(set-logic QF_LIA)(assert (= (mod (- 7) (- 2)) 1))(check-sat)")
            .trim(),
        "sat"
    );
}
