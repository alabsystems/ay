// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `check-sat-assuming` with combined theories.
//!
//! Consumer: model-checker-consumer uses check-sat-assuming with UFLIA/AUFLIA for incremental
//! verification queries. These tests verify that assumption-based solving
//! correctly interacts with the Nelson-Oppen combiner's equality propagation.

use crate::common::solve;

/// QF_UFLIA check-sat-assuming: basic assumption toggling.
/// Verifies that named assumptions can switch between SAT and UNSAT.
#[test]
fn test_uflia_check_sat_assuming_basic_toggle() {
    let output = solve(
        r#"
(set-logic QF_UFLIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun f (Int) Int)

; Base constraints
(assert (= (f x) (f y)))
(assert (=> (= (f x) (f y)) (= x y)))
; So x = y is forced

; Named assumptions
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (=> p (> x 10)))
(assert (=> q (< y 5)))

; With p only: x=y and x>10 => sat
(check-sat-assuming (p))

; With p and q: x=y and x>10 and y<5 => x>10 and x<5 => unsat
(check-sat-assuming (p q))

; With q only: x=y and y<5 => sat
(check-sat-assuming (q))

; With neither: just x=y => sat
(check-sat)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat"))
        .collect();
    assert_eq!(
        results.len(),
        4,
        "expected 4 check-sat results, got: {output}"
    );
    assert_eq!(results[0].trim(), "sat", "p only: {output}");
    assert_eq!(
        results[1].trim(),
        "unsat",
        "p and q (contradiction): {output}"
    );
    assert_eq!(results[2].trim(), "sat", "q only: {output}");
    assert_eq!(results[3].trim(), "sat", "no assumptions: {output}");
}

/// QF_UFLIA check-sat-assuming: UF congruence with assumption-guarded equality.
/// Tests that UF congruence does not persist across check-sat-assuming calls.
#[test]
fn test_uflia_check_sat_assuming_congruence_isolation() {
    let output = solve(
        r#"
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun f (Int) Int)

; Base: f(a) != f(b)
(assert (not (= (f a) (f b))))

; Assumption-guarded equality
(declare-fun eq_guard () Bool)
(assert (=> eq_guard (= a b)))

; With eq_guard: a=b => f(a)=f(b) by congruence => contradiction with base
(check-sat-assuming (eq_guard))

; Without eq_guard: a and b are distinct, no contradiction
(check-sat)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat"))
        .collect();
    assert_eq!(results.len(), 2, "expected 2 results, got: {output}");
    assert_eq!(
        results[0].trim(),
        "unsat",
        "with eq_guard (congruence contradiction): {output}"
    );
    assert_eq!(results[1].trim(), "sat", "without eq_guard: {output}");
}

/// QF_LIA check-sat-assuming with push/pop interaction.
/// Verifies that assumptions and scoped assertions interact correctly.
#[test]
fn test_lia_check_sat_assuming_with_push_pop() {
    let output = solve(
        r#"
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)

(declare-fun p () Bool)
(assert (=> p (> x 100)))

; Base: x + y = 50
(assert (= (+ x y) 50))

; check-sat-assuming p: x>100 and x+y=50 => y<-50, sat
(check-sat-assuming (p))

(push 1)
; In scope: y > 0
(assert (> y 0))
; check-sat-assuming p: x>100 and x+y=50 and y>0 => x>100 and y=50-x<-50 but y>0 => unsat
(check-sat-assuming (p))
(pop 1)

; After pop: y>0 is gone, should be sat again with p
(check-sat-assuming (p))
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat"))
        .collect();
    assert_eq!(results.len(), 3, "expected 3 results, got: {output}");
    assert_eq!(results[0].trim(), "sat", "base with p: {output}");
    assert_eq!(results[1].trim(), "unsat", "scope with p and y>0: {output}");
    assert_eq!(results[2].trim(), "sat", "after pop with p: {output}");
}

/// AUFLIA check-sat-assuming with array constraints.
/// Tests assumption-guarded array store/select interactions.
#[test]
fn test_auflia_check_sat_assuming_array_interaction() {
    let output = solve(
        r#"
(set-logic AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)

; Base: select(a, i) = 42
(assert (= (select a i) 42))

; Assumption-guarded: i = j
(declare-fun idx_eq () Bool)
(assert (=> idx_eq (= i j)))

; With idx_eq: i=j => select(a,j) should also be 42, consistent
(assert (= (select a j) 42))
(check-sat-assuming (idx_eq))

; Check without idx_eq: i and j independent, select(a,j)=42 still forced
(check-sat)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat"))
        .collect();
    assert_eq!(results.len(), 2, "expected 2 results, got: {output}");
    assert_eq!(results[0].trim(), "sat", "with idx_eq: {output}");
    assert_eq!(results[1].trim(), "sat", "without idx_eq: {output}");
}

/// QF_UFLIA check-sat-assuming: multiple calls with different assumption sets.
/// Verifies that the solver correctly resets between check-sat-assuming calls.
#[test]
fn test_uflia_check_sat_assuming_multiple_rounds() {
    let output = solve(
        r#"
(set-logic QF_UFLIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun f (Int) Int)

(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)

(assert (=> p (> x 0)))
(assert (=> q (> y 0)))
(assert (=> r (< (+ x y) 0)))

; p and q: x>0, y>0 => sat
(check-sat-assuming (p q))

; p and r: x>0 and x+y<0 => y<-x<0 => sat (y unconstrained by q)
(check-sat-assuming (p r))

; p, q, r: x>0, y>0, x+y<0 => contradiction
(check-sat-assuming (p q r))

; Just r: x+y<0 => sat (x,y unconstrained otherwise)
(check-sat-assuming (r))
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat"))
        .collect();
    assert_eq!(results.len(), 4, "expected 4 results, got: {output}");
    assert_eq!(results[0].trim(), "sat", "p,q: {output}");
    assert_eq!(results[1].trim(), "sat", "p,r: {output}");
    assert_eq!(
        results[2].trim(),
        "unsat",
        "p,q,r (contradiction): {output}"
    );
    assert_eq!(results[3].trim(), "sat", "r only: {output}");
}

/// (#h10) QF_ALIA: `(= p (= (select arr i) (select arr j)))` with `(not p)`
/// assumed is genuinely SAT (z3=sat): the two free selects can differ so the
/// inner equality is false, p=false, and `(not p)` holds. The combined
/// array+LIA solver decides SAT but extracts a degenerate model (defaults both
/// unconstrained selects to the same value via `i = j`), so VariableSubstitution
/// eliminated `p` and model completion re-derived its `bool_override` to TRUE.
/// Assumption validation then saw `(not p)` evaluate FALSE and previously
/// fail-closed to an `(error)` that DROPPED the verdict.
///
/// The fix resolves the eliminated assumption atom through the recorded
/// substitution chain to its defining atom and honors the SAT solver's
/// authoritative truth assignment for it, confirming the SAT solver genuinely
/// satisfied the assumption. This must return SAT (never an error/drop).
#[test]
fn test_qf_alia_check_sat_assuming_select_disequality_no_error_h10() {
    let output = solve(
        r#"
(set-logic QF_ALIA)
(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const p Bool)
(assert (= p (= (select arr i) (select arr j))))
(check-sat-assuming ((not p)))
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(results.len(), 1, "expected 1 result, got: {output}");
    assert_eq!(
        results[0].trim(),
        "sat",
        "select-disequality-via-assumption must be SAT (never error/drop): {output}"
    );
    assert!(
        !output.contains("error"),
        "must not emit an (error) / drop the verdict: {output}"
    );
}

/// (#h10 soundness control) Reflexive select `(= (select arr i) (select arr i))`
/// is a tautology, so `p` must be TRUE and `(not p)` is genuinely UNSAT. The h10
/// substitution-resolving fix must NOT launder this into a spurious SAT: the SAT
/// solver assigns the reflexive equality atom TRUE, so resolving `(not p)`
/// through the substitution chain correctly finds it unsatisfiable.
#[test]
fn test_qf_alia_check_sat_assuming_reflexive_select_still_unsat_h10() {
    let output = solve(
        r#"
(set-logic QF_ALIA)
(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const p Bool)
(assert (= p (= (select arr i) (select arr i))))
(check-sat-assuming ((not p)))
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(results.len(), 1, "expected 1 result, got: {output}");
    assert_eq!(
        results[0].trim(),
        "unsat",
        "reflexive select with (not p) must stay UNSAT: {output}"
    );
}
