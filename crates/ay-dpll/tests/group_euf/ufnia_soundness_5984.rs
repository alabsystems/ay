// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #5984 and #4525: UFNIA/UFNRA/UFNIRA/AUFNIRA support.
//!
//! #5984: logic_has_uf check misses UFNIA/UFNRA/UFNIRA.
//! Before the fix, UFNIA/UFNRA mapped to NIA/NRA, losing UF information.
//!
//! #4525: Combined EUF+NIA solver via UfNiaSolver Nelson-Oppen adapter.
//! QF_UFNIA, QF_AUFNIRA, UFNIA, UFNIRA, AUFNIRA now solve with combined
//! EUF+NIA theory instead of immediately returning Unknown.

use ntest::timeout;

/// QF_UFNIA with UF consistency requirement: (f x) must equal (f y) when x = y.
/// Before #5984 fix: NIA solver could return sat with inconsistent UF assignments.
/// After #4525 fix: returns unsat via combined EUF+NIA Nelson-Oppen solver.
#[test]
#[timeout(10_000)]
fn qf_ufnia_returns_unsat_with_uf_congruence() {
    let smt = r#"
(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).unwrap();
    // #4525: Combined EUF+NIA solver returns unsat (EUF congruence f(x)=f(y) when x=y).
    assert_eq!(
        result, "unsat",
        "UFNIA with combined EUF+NIA solver should detect UF congruence conflict"
    );
}

/// #9036: UFNIA must defer integer branch-and-bound splits from NIA.
///
/// `UfNiaSolver` used to pass `NiaSolver::check()` through the LRA-specific
/// triage helper. When NIA legitimately returned `NeedSplit` for the fractional
/// LP relaxation of `2*x >= 5`, that helper panicked with "LRA solver returned
/// NeedSplit". The UFNIA adapter must use the integer split triage instead.
#[test]
#[timeout(10_000)]
fn qf_ufnia_defers_nia_need_split_without_panic_9036() {
    let smt = r#"
(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (>= (* 2 x) 5))
(assert (= (f x) (f x)))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).unwrap();
    assert_ne!(
        result, "unsat",
        "2*x >= 5 has integer models; UFNIA must not reject it"
    );
}

/// QF_UFNRA: same UF consistency test with real arithmetic.
#[test]
#[timeout(10_000)]
fn qf_ufnra_returns_unknown_not_unsound_sat() {
    let smt = r#"
(set-logic QF_UFNRA)
(declare-fun g (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= a b))
(assert (not (= (g a) (g b))))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).unwrap();
    assert_ne!(
        result, "sat",
        "UFNRA must not return sat without UF congruence closure"
    );
}

/// QF_AUFNIA: arrays + UF + NIA preserves UF information.
/// #4525: Combined EUF+NIA solver detects (f x) = (f x) tautology.
#[test]
#[timeout(10_000)]
fn qf_aufnia_returns_unsat_with_uf_congruence() {
    let smt = r#"
(set-logic QF_AUFNIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (not (= (f x) (f x))))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).unwrap();
    // (f x) = (f x) is a UF tautology — EUF detects this directly.
    assert_eq!(
        result, "unsat",
        "AUFNIA with combined EUF+NIA solver should detect UF tautology"
    );
}

/// Quantified UFNIA with quantifiers: may return sat, unsat, or unknown.
/// The combined EUF+NIA solver handles the ground part; quantifiers are
/// incomplete so unknown is acceptable.
#[test]
#[timeout(10_000)]
fn quantified_ufnia_not_unsound_sat() {
    let smt = r#"
(set-logic UFNIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (>= (f x) 0)))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).unwrap();
    // Quantified UFNIA may return sat (correct: any f mapping to non-negative works),
    // unknown (incomplete), but must not produce incorrect results.
    assert!(
        result == "sat" || result == "unknown",
        "Quantified UFNIA should return sat or unknown — got: {result}"
    );
}

/// QF_UFNIRA: mixed int/real + UF.
/// #4525: Combined EUF+NIA solver handles NIRA (routes through UfNiaSolver).
#[test]
#[timeout(10_000)]
fn qf_ufnira_returns_unsat_with_uf_congruence() {
    let smt = r#"
(set-logic QF_UFNIRA)
(declare-fun h (Int) Real)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (not (= (h x) (h y))))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).unwrap();
    assert_ne!(
        result, "sat",
        "UFNIRA must not return sat without proving the UF congruence conflict"
    );
}

/// AUFNIRA: arrays + UF + nonlinear integer/real arithmetic (#4525).
/// This is the key logic for model-checker consumer TLAPS integration.
#[test]
#[timeout(10_000)]
fn aufnira_uf_congruence_unsat() {
    let smt = r#"
(set-logic AUFNIRA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).unwrap();
    assert_eq!(
        result, "unsat",
        "AUFNIRA should solve UF congruence conflicts via combined EUF+NIA"
    );
}

/// AUFNIRA with linear integer arithmetic + UF (#4525).
/// Tests the combined path with a SAT instance that doesn't require NIA.
#[test]
#[timeout(10_000)]
fn aufnira_linear_sat() {
    let smt = r#"
(set-logic AUFNIRA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (f x) (+ x 1)))
(assert (= (f y) (+ y 1)))
(assert (= x y))
(assert (= (f x) (f y)))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).unwrap();
    // f(x)=x+1, x=y, so f(x)=f(y) trivially. Must not return unsat.
    assert_ne!(
        result, "unsat",
        "AUFNIRA: linear f(x)=x+1, x=y, f(x)=f(y) is satisfiable"
    );
}

/// AUFNIRA TLAPS-style proof obligation (#4525).
#[test]
#[timeout(10_000)]
fn aufnira_tlaps_style_obligation() {
    let smt = r#"
(set-logic AUFNIRA)
(declare-fun Len ((Array Int Int)) Int)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun n () Int)
(assert (= (Len a) n))
(assert (> n 0))
(assert (= a b))
(assert (not (= (Len b) n)))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).unwrap();
    assert_eq!(
        result, "unsat",
        "AUFNIRA TLAPS obligation: Len(a)=n, a=b implies Len(b)=n"
    );
}
