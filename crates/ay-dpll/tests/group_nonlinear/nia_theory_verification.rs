// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) integration tests for the NIA (Non-linear Integer Arithmetic) theory.
//!
//! Tests cover:
//! 1. Polynomial inequality SAT/UNSAT via the Executor (SMT-LIB path)
//! 2. Sign determination: x>0 ∧ y>0 ⇒ x*y>0
//! 3. Tangent plane lemma generation (indirectly, via model consistency check)
//! 4. Cross-theory NIA+LIA interaction
//! 5. QF_NIA SMT-LIB benchmark regression tests
//!
//! # Strictness policy (Part of #3752)
//!
//! Tests where the solver currently returns a definitive answer (sat or unsat)
//! use strict assertions that require that exact answer. Tests where the solver
//! returns "unknown" due to NIA incompleteness accept `unknown` alongside the
//! expected answer and are marked with `// NIA-INCOMPLETE:` comments explaining
//! why. If solver improvements cause a previously-unknown test to start
//! returning a definitive answer, the test should be tightened.
//!
//! Part of #3512

use ntest::timeout;

// ============================================================================
// 1. Polynomial inequality tests
// ============================================================================

/// x^2 >= 0 is a tautology for integers.
// NIA-INCOMPLETE: solver returns unknown; lacks nonlinear tautology reasoning.
#[test]
#[timeout(10_000)]
fn nia_square_nonnegative_sat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (>= (* x x) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "x^2 >= 0 should be SAT or Unknown, got: {result}"
    );
}

/// x^2 < 0 is unsatisfiable for integers.
// NIA-INCOMPLETE: solver returns unknown; lacks nonlinear infeasibility proof.
#[test]
#[timeout(10_000)]
fn nia_square_negative_unsat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (< (* x x) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "x^2 < 0 should be UNSAT or Unknown, got: {result}"
    );
}

/// Simple satisfiable nonlinear: x*y = 6 with x=2, y=3.
// NIA-INCOMPLETE: solver returns unknown; lacks nonlinear model construction.
#[test]
#[timeout(10_000)]
fn nia_product_equals_constant_sat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* x y) 6))
(assert (> x 0))
(assert (> y 0))
(assert (< x 4))
(assert (< y 4))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "x*y = 6 with bounds should be SAT or Unknown, got: {result}"
    );
}

/// No integer solution: x*y = 1 with x > 1 (would need x=1, contradicts x>1).
// NIA-INCOMPLETE: solver returns unknown; lacks nonlinear factorization reasoning.
#[test]
#[timeout(10_000)]
fn nia_product_one_no_solution_unsat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* x y) 1))
(assert (> x 1))
(assert (> y 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "x*y = 1 with x > 1, y > 0 should be UNSAT or Unknown, got: {result}"
    );
}

// ============================================================================
// 2. Sign determination tests
// ============================================================================

/// x > 0 ∧ y > 0 ∧ x*y < 0 is unsatisfiable (product of positives is positive).
// The search lane detects this conflict, but the public strict gate may return
// `unknown` until that nonlinear lemma has independently checkable proof authority.
#[test]
#[timeout(10_000)]
fn nia_sign_positive_product_conflict() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (> y 0))
(assert (< (* x y) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "x>0 ∧ y>0 ∧ x*y<0 must never be SAT, got: {result}"
    );
}

/// x < 0 ∧ y < 0 ∧ x*y < 0 is unsatisfiable (product of negatives is positive).
// The search lane detects this conflict, but strict publication may fail closed.
#[test]
#[timeout(10_000)]
fn nia_sign_negative_product_conflict() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (< x 0))
(assert (< y 0))
(assert (< (* x y) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "x<0 ∧ y<0 ∧ x*y<0 must never be SAT, got: {result}"
    );
}

/// x > 0 ∧ y < 0 ∧ x*y > 0 is unsatisfiable (mixed signs → negative product).
// The search lane detects this conflict, but strict publication may fail closed.
#[test]
#[timeout(10_000)]
fn nia_sign_mixed_product_conflict() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (< y 0))
(assert (> (* x y) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "x>0 ∧ y<0 ∧ x*y>0 must never be SAT, got: {result}"
    );
}

/// x > 0 ∧ y > 0 ∧ x*y > 0 is satisfiable (consistent signs).
// NIA-INCOMPLETE: solver returns unknown; cannot construct nonlinear model.
#[test]
#[timeout(10_000)]
fn nia_sign_positive_product_consistent() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (> y 0))
(assert (> (* x y) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "x>0 ∧ y>0 ∧ x*y>0 should be SAT or Unknown, got: {result}"
    );
}

// ============================================================================
// 3. Tangent plane lemma tests (via model consistency)
// ============================================================================

/// Test that the solver does not claim SAT for a formula where the nonlinear
/// product constraint is inconsistent with the model. x*y = 10 with tight
/// bounds that force a unique assignment.
// NIA-INCOMPLETE: solver returns unknown; lacks nonlinear evaluation under
// concrete assignments.
#[test]
#[timeout(10_000)]
fn nia_tangent_plane_model_consistency() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* x y) 10))
(assert (= x 2))
(assert (= y 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "x=2, y=5, x*y=10 should be SAT or Unknown, got: {result}"
    );
}

/// x*y = 10 with x=2, y=3 is unsatisfiable (2*3=6 ≠ 10).
// NIA-INCOMPLETE: solver returns unknown; lacks nonlinear evaluation under
// concrete assignments.
#[test]
#[timeout(10_000)]
fn nia_tangent_plane_model_inconsistency() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* x y) 10))
(assert (= x 2))
(assert (= y 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "x=2, y=3, x*y=10 should be UNSAT or Unknown, got: {result}"
    );
}

// ============================================================================
// 4. Cross-theory NIA+LIA interaction tests
// ============================================================================

/// Mixed linear and nonlinear: x + y >= 5 ∧ x*y = 6 ∧ x > 0 ∧ y > 0
/// Satisfiable: x=2, y=3 gives x+y=5, x*y=6.
// NIA-INCOMPLETE: solver returns unknown; cannot combine linear and nonlinear
// reasoning to construct a satisfying model.
#[test]
#[timeout(10_000)]
fn nia_lia_cross_theory_sat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= (+ x y) 5))
(assert (= (* x y) 6))
(assert (> x 0))
(assert (> y 0))
(assert (<= x 3))
(assert (<= y 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "linear + nonlinear SAT case, got: {result}"
    );
}

/// Mixed linear and nonlinear constraints that are unsatisfiable:
/// x + y = 3 ∧ x*y = 5 ∧ x > 0 ∧ y > 0
/// The only positive integer pairs summing to 3 are (1,2) and (2,1),
/// neither gives product 5.
// NIA-INCOMPLETE: solver returns unknown; lacks case-split or nonlinear
// infeasibility reasoning for this constraint combination.
#[test]
#[timeout(10_000)]
fn nia_lia_cross_theory_unsat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 5))
(assert (> x 0))
(assert (> y 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "x+y=3, x*y=5, x>0, y>0 should be UNSAT or Unknown, got: {result}"
    );
}

/// Three variables with both linear and nonlinear constraints.
// NIA-INCOMPLETE: solver returns unknown even with concrete variable values;
// lacks nonlinear evaluation under concrete assignments.
#[test]
#[timeout(10_000)]
fn nia_lia_three_vars() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= x 2))
(assert (= y 3))
(assert (= z (* x y)))
(assert (= z 6))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "x=2, y=3, z=x*y=6 should be SAT or Unknown, got: {result}"
    );
}

// ============================================================================
// 5. QF_NIA SMT-LIB benchmark regression tests
// ============================================================================

/// SMT-LIB style: simple quadratic constraint x^2 + y^2 <= 1 with integer vars.
/// Solutions: (0,0), (0,1), (0,-1), (1,0), (-1,0).
// NIA-INCOMPLETE: solver returns unknown; lacks quadratic model construction.
#[test]
#[timeout(10_000)]
fn nia_benchmark_quadratic_circle() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= (+ (* x x) (* y y)) 1))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "x^2+y^2 <= 1 has integer solutions, got: {result}"
    );
}

/// SMT-LIB style: Pell-like equation x^2 - 2*y^2 = 1.
/// Known solution: x=1, y=0.
// NIA-INCOMPLETE: solver returns unknown; lacks Diophantine equation solving.
#[test]
#[timeout(10_000)]
fn nia_benchmark_pell_equation() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (- (* x x) (* 2 (* y y))) 1))
(assert (>= x 0))
(assert (>= y 0))
(assert (<= x 10))
(assert (<= y 10))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "Pell equation x^2-2y^2=1 has solutions (x=1,y=0), (x=3,y=2), got: {result}"
    );
}

/// SMT-LIB style: Pythagorean triple x^2 + y^2 = z^2 with tight bounds.
/// Known solution: x=3, y=4, z=5.
// NIA-INCOMPLETE: solver returns unknown; lacks bounded nonlinear search.
#[test]
#[timeout(10_000)]
fn nia_benchmark_pythagorean_triple() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= (+ (* x x) (* y y)) (* z z)))
(assert (> x 0))
(assert (> y 0))
(assert (> z 0))
(assert (<= x 5))
(assert (<= y 5))
(assert (<= z 6))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "Pythagorean triple x^2+y^2=z^2 with bounds has solutions, got: {result}"
    );
}

// ============================================================================
// Incremental solving (push/pop) tests
// ============================================================================

/// Push/pop with nonlinear constraints: constraint at deeper scope is retracted.
#[test]
#[timeout(10_000)]
fn nia_incremental_push_pop_retract() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (> y 0))
(push 1)
(assert (< (* x y) 0))
(check-sat)
(pop 1)
(assert (> (* x y) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let results: Vec<&str> = result
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .collect();

    assert!(
        results.len() >= 2,
        "expected 2 check-sat results, got: {results:?}"
    );
    // The first query is contradictory. `unknown` is the correct fail-closed
    // public answer when the nonlinear lemma lacks a strict certificate.
    assert!(
        matches!(results[0], "unsat" | "unknown"),
        "first check-sat (sign conflict) must never be SAT, got: {}",
        results[0]
    );
    // NIA-INCOMPLETE: second check-sat (x>0 ∧ y>0 ∧ x*y>0) returns unknown;
    // consistent signs but solver cannot construct nonlinear model.
    assert!(
        matches!(results[1], "sat" | "unknown"),
        "second check-sat (after pop + consistent assert) should be SAT or Unknown, got: {}",
        results[1]
    );
}

// ============================================================================
// 6. Combined-theory-mode product model tests (fix4-nia-div)
// ============================================================================

/// r = n*(n+1) with n=2, r=6 is satisfiable (2*3 = 6).
///
/// STRICT: pre-fix4 NiaSolver poisoned LRA to Unknown on the nonlinear `*`
/// (LRA "simplex=Sat but unsupported, returning Unknown"). With combined
/// theory mode enabled at NiaSolver::new construction, LRA over-approximates
/// the product as a fresh opaque variable; NIA's check_monomial_consistency
/// confirms the opaque value matches the real product (2*3 = 6) and returns
/// a definitive SAT.
#[test]
#[timeout(10_000)]
fn nia_product_fixed_model_sat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun n () Int)
(declare-fun r () Int)
(assert (= r (* n (+ n 1))))
(assert (= n 2))
(assert (= r 6))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "r=n*(n+1) with n=2, r=6 must be SAT (combined-mode product model), got: {result}"
    );
}

/// r = n*(n+1) with n=2, r=7 is unsatisfiable (2*3 = 6 != 7).
///
/// CANARY (false-SAT): must NOT return "sat". Catches an under-validated
/// opaque monomial — i.e. if check_monomial_consistency or verify_model_strict
/// regressed and accepted the opaque product value without checking it equals
/// the real product. Returning "unsat" or "unknown" is acceptable.
#[test]
#[timeout(10_000)]
fn nia_product_fixed_model_unsat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun n () Int)
(declare-fun r () Int)
(assert (= r (* n (+ n 1))))
(assert (= n 2))
(assert (= r 7))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "r=n*(n+1) with n=2, r=7 must NOT be SAT (2*3 != 7), got: {result}"
    );
}

/// Push/pop with sign constraints: sign constraint from deeper scope should not
/// leak into outer scope. Regression test for #3523.
#[test]
#[timeout(10_000)]
fn nia_incremental_sign_constraint_leak_regression() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(push 1)
(assert (> x 0))
(assert (> y 0))
(assert (< (* x y) 0))
(check-sat)
(pop 1)
(assert (= x 0))
(assert (= (* x y) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let results: Vec<&str> = result
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .collect();

    assert!(
        results.len() >= 2,
        "expected 2 check-sat results, got: {results:?}"
    );
    // The first query is contradictory; strict publication may fail closed.
    assert!(
        matches!(results[0], "unsat" | "unknown"),
        "sign conflict must never be SAT, got: {}",
        results[0]
    );
    // NIA-INCOMPLETE: second check-sat (x=0, x*y=0) returns unknown after pop;
    // solver cannot evaluate nonlinear product under concrete assignment.
    // This would fail if sign constraints leaked from the inner scope.
    assert!(
        matches!(results[1], "sat" | "unknown"),
        "after pop, x=0 ∧ x*y=0 should be SAT or Unknown, got: {}",
        results[1]
    );
}

// ============================================================================
// 6. Symbolic mod/div on the NIA path (#nia-modxx-zerodiv)
// ============================================================================

/// `(mod x x)` with `x` bounded to `{0}` is a SINGLE consistent (unspecified)
/// value. Demanding it be both `>= y*y >= 1` and `< 0` is UNSAT (z3 agrees).
///
/// Regression for the wrong-SAT where the LRA layer dropped every atom
/// containing the symbolic `(mod x x)` as "unsupported" and NIA's tentative
/// patch returned SAT on a model (`y*y=1, (mod x x)=-1`) violating those dropped
/// atoms. The NIA path now eliminates symbolic mod/div to a tableau-supported
/// var, so the atoms are actually enforced. MUST NOT be SAT.
#[test]
#[timeout(10_000)]
fn nia_symbolic_mod_xx_zerodiv_not_sat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= x 2))
(assert (>= x 0))
(assert (<= (* y y) (mod x x)))
(assert (< (mod x x) 0))
(assert (>= y 1))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    // SOUNDNESS: z3 says unsat. AY must be unsat or unknown — never sat.
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "(mod x x) with one consistent value must NOT be SAT, got: {result}"
    );
}

/// Two contradictory bounds on the SAME symbolic `(mod x x)` term must be
/// refuted (the term denotes one value, so `> 5 ∧ < 3` is impossible). This
/// directly exercises the zero-divisor congruence on the nonlinear path.
#[test]
#[timeout(10_000)]
fn nia_symbolic_mod_xx_contradictory_bounds_not_sat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-const x Int)
(declare-const w Int)
(assert (>= x 0))
(assert (<= x 1))
(assert (= w (* x x)))
(assert (> (mod x x) 5))
(assert (< (mod x x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "same (mod x x) cannot be both > 5 and < 3, got: {result}"
    );
}

/// A single `(mod x x)` equality with `x` allowed to be `0` IS satisfiable: the
/// zero-divisor value is unspecified, so it may equal any constant (z3: sat).
/// Guards against over-degradation of genuine symbolic-mod SAT cases.
#[test]
#[timeout(10_000)]
fn nia_symbolic_mod_xx_single_constraint_sat() {
    let smt = r#"
(set-logic QF_NIA)
(declare-const x Int)
(declare-const w Int)
(assert (>= x 0))
(assert (<= x 2))
(assert (= w (* x x)))
(assert (= (mod x x) 42))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let r = crate::common::sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "(mod x x) = 42 with x possibly 0 should be SAT or Unknown, got: {result}"
    );
}
