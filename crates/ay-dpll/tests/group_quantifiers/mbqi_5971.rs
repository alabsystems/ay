// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for Model-Based Quantifier Instantiation (MBQI) (#5971).
//!
//! MBQI handles universal quantifiers that neither E-matching (no triggers)
//! nor CEGQI (non-arithmetic body) can process. It evaluates quantifier
//! bodies under the candidate model using ground term substitutions.
//!
//! Model value injection: when no ground terms exist for a bound variable's
//! sort, MBQI synthesizes default candidates (0 for Int, true/false for Bool,
//! etc.) from the model. This extends MBQI to handle quantifiers over sorts
//! that have no existing ground terms in the assertion set.
//!
//! Reference: Z3 `sat/smt/q_mbi.cpp` (quick_check, check_forall).

use ntest::timeout;

/// Pure UF quantifier: forall x:U. (f x) = (g x)
/// with ground terms f(a)=1 and g(a)=2, which falsifies the quantifier for x=a.
/// E-matching has no triggers (= is builtin). CEGQI doesn't apply (UF, not arith).
/// MBQI should find the counterexample x=a and produce UNSAT.
#[test]
#[timeout(60_000)]
fn test_mbqi_uf_forall_counterexample_unsat() {
    let smt = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun f (U) U)
        (declare-fun g (U) U)
        (declare-fun b () U)
        (declare-fun c () U)
        (assert (not (= (f a) (g a))))
        (assert (forall ((x U)) (= (f x) (g x))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // Ground assertion: f(a) != g(a)
    // Quantifier: forall x. f(x) = g(x)
    // Instantiation x=a gives f(a)=g(a), contradicting f(a)!=g(a).
    assert_eq!(outputs, vec!["unsat"]);
}

/// Pure UF quantifier that IS satisfied by the ground model.
/// forall x:U. (f x) = (f x) is trivially true.
/// MBQI should verify all substitutions evaluate to true → SAT.
#[test]
#[timeout(60_000)]
fn test_mbqi_uf_forall_trivially_true_sat() {
    let smt = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun f (U) U)
        (assert (forall ((x U)) (= (f x) (f x))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // forall x. f(x) = f(x) is trivially true.
    // MBQI checks x=a: f(a)=f(a) → true. All satisfied → SAT.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat or unknown, got {outputs:?}"
    );
}

/// MBQI with implication body: forall x. P(x) => Q(x)
/// with P(a)=true, Q(a)=false → falsifies for x=a → UNSAT.
#[test]
#[timeout(60_000)]
fn test_mbqi_uf_implication_counterexample_unsat() {
    let smt = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (assert (P a))
        (assert (not (Q a)))
        (assert (forall ((x U)) (=> (P x) (Q x))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // P(a) is true, Q(a) is false.
    // forall x. P(x)=>Q(x) instantiated with x=a gives P(a)=>Q(a) = true=>false = false.
    assert_eq!(outputs, vec!["unsat"]);
}

/// MBQI with two quantified variables over UF.
/// forall x y. f(x,y) = f(y,x) — symmetry axiom.
/// With f(a,b)=1 and f(b,a)=2, this is falsified for x=a,y=b.
#[test]
#[timeout(60_000)]
fn test_mbqi_uf_two_vars_symmetry_violation_unsat() {
    let smt = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun f (U U) U)
        (assert (not (= (f a b) (f b a))))
        (assert (forall ((x U) (y U)) (= (f x y) (f y x))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// MBQI for mixed UF+arithmetic: forall x:Int. f(x) >= 0
/// with f(0) = -1. E-matching has no triggers for >= (builtin).
/// CEGQI applies (arithmetic), but this tests that MBQI also works
/// as a fallback/complement.
#[test]
#[timeout(60_000)]
fn test_mbqi_arith_forall_violated_unsat() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) (- 1)))
        (assert (forall ((x Int)) (>= (f x) 0)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // f(0) = -1 but forall x. f(x) >= 0 requires f(0) >= 0. Contradiction.
    assert_eq!(outputs, vec!["unsat"]);
}

/// MBQI should handle formulas that were previously returned as unknown
/// due to QuantifierUnhandled. This formula has a pure Bool quantifier
/// that finite-domain expansion should handle, but tests the pipeline.
#[test]
#[timeout(60_000)]
fn test_mbqi_previously_unknown_now_decidable() {
    let smt = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun f (U) U)
        (assert (= (f a) b))
        (assert (= (f b) a))
        (assert (not (= a b)))
        (assert (forall ((x U)) (not (= (f (f x)) x))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // f(a)=b, f(b)=a, a!=b.
    // f(f(a)) = f(b) = a. So (f(f(a)))=a, which violates forall x. f(f(x))!=x.
    // MBQI with x=a: f(f(a))=a, not(a=a)=false → counterexample found → UNSAT.
    assert_eq!(outputs, vec!["unsat"]);
}

// ============================================================================
// Model value injection tests (#5971)
//
// These tests exercise the case where a quantified variable's sort has NO
// existing ground terms in the assertion set. MBQI must synthesize default
// candidates from the model (0 for Int, true/false for Bool, etc.) to
// find counterexamples.
// ============================================================================

/// Integer quantifier with no ground Int terms in assertions.
/// forall x:Int. x > 0 is false for x=0. The assertion set only contains
/// Bool-sorted terms (the quantifier itself). MBQI synthesizes Int candidate
/// 0 via model value injection and finds the counterexample.
#[test]
#[timeout(60_000)]
fn test_mbqi_model_value_injection_int_no_ground_terms() {
    let smt = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (> x 0)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // forall x. x > 0 is false (x=0 is a counterexample).
    // Without model value injection, MBQI would skip this quantifier
    // because no Int ground terms exist. With injection, it tries x=0
    // and finds the counterexample.
    assert_eq!(outputs, vec!["unsat"]);
}

/// Integer quantifier that IS satisfiable with synthesized defaults.
/// forall x:Int. (x + x) = (2 * x) is always true.
/// MBQI synthesizes x=0, evaluates 0+0=2*0 → true, and confirms SAT.
#[test]
#[timeout(60_000)]
fn test_mbqi_model_value_injection_int_trivially_true() {
    let smt = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (= (+ x x) (* 2 x))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // This is always true. MBQI with x=0: 0+0=2*0 → 0=0 → true.
    // Since all checked substitutions are satisfied, SAT is correct.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat or unknown, got {outputs:?}"
    );
}

/// Bool quantifier with no ground Bool terms besides true/false constants.
/// forall b:Bool. (and b (not b)) should evaluate to false for both
/// b=true and b=false → UNSAT.
#[test]
#[timeout(60_000)]
fn test_mbqi_model_value_injection_bool_no_ground_terms() {
    let smt = r#"
        (set-logic UF)
        (assert (forall ((b Bool)) (and b (not b))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // forall b. (b AND NOT b) is always false.
    // With model value injection, MBQI tries b=true: true AND false = false → counterexample.
    assert_eq!(outputs, vec!["unsat"]);
}

/// Uninterpreted sort with no ground terms — tests fresh constant synthesis.
/// forall x:U. P(x) with no ground U constants defined.
/// MBQI should synthesize a fresh element for sort U and evaluate P on it.
/// Since P is uninterpreted and unconstrained, the formula could be SAT.
#[test]
#[timeout(60_000)]
fn test_mbqi_model_value_injection_uninterpreted_sort() {
    let smt = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (assert (forall ((x U)) (P x)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // forall x. P(x) where P is unconstrained.
    // The model can set P to be always-true, so SAT is valid.
    // Unknown is also acceptable if MBQI cannot fully verify.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat or unknown, got {outputs:?}"
    );
}

/// Mixed: quantifier over Int sort with ground UF terms but no Int terms.
/// forall x:Int. f(x) >= x with only UF-sorted ground terms.
/// MBQI should synthesize Int candidate 0 and evaluate f(0) >= 0.
#[test]
#[timeout(60_000)]
fn test_mbqi_model_value_injection_int_with_uf_context() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun g (U) U)
        (declare-fun f (Int) Int)
        (assert (= (g a) a))
        (assert (= (f 0) (- 1)))
        (assert (forall ((x Int)) (>= (f x) 0)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // f(0)=-1 but forall x. f(x)>=0 requires f(0)>=0. UNSAT.
    // Note: This test also has Int ground term "0" from the assertion f(0)=-1,
    // but tests the path where MBQI combines ground terms with synthesized values.
    assert_eq!(outputs, vec!["unsat"]);
}

/// Two-variable quantifier where one sort has ground terms and one doesn't.
/// forall (x:U) (n:Int). implies (P x) (> n 0)
/// with P(a)=true. No Int ground terms exist.
/// MBQI should synthesize Int candidate 0, evaluate: P(a) => 0 > 0 = true => false = false.
#[test]
#[timeout(60_000)]
fn test_mbqi_model_value_injection_mixed_sorts() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun P (U) Bool)
        (assert (P a))
        (assert (forall ((x U) (n Int)) (=> (P x) (> n 0))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // P(a) is true. forall x n. P(x) => n > 0.
    // With x=a, n=0: P(a) => 0>0 = true => false = false → counterexample.
    assert_eq!(outputs, vec!["unsat"]);
}
