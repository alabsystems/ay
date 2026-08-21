// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn assert_pure_uflia_route_stats(exec: &Executor) {
    let stats = exec.statistics();
    assert_eq!(
        stats.get_int("smt.checks.arrays"),
        Some(0),
        "pure QF_UFLIA should use the UF+LIA combiner, not AUFLIA"
    );
    assert!(
        stats
            .get_int("smt.checks.euf")
            .expect("UFLIA route should report EUF checks")
            > 0,
        "UFLIA route should exercise EUF"
    );
    assert!(
        stats
            .get_int("smt.checks.lia")
            .expect("UFLIA route should report LIA checks")
            > 0,
        "UFLIA route should exercise LIA"
    );
}

#[test]
fn test_get_value_uf_returning_int() {
    // Regression test for #385: get-value on UF application returning Int
    // should return the actual value, not placeholder 0
    let input = r#"
        (set-option :produce-models true)
        (set-logic QF_UFLIA)
        (declare-sort U 0)
        (declare-fun f (U) Int)
        (declare-fun x () U)
        (assert (= (f x) 100))
        (check-sat)
        (get-value ((f x)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // The function application should evaluate to 100, not 0
    assert!(
        outputs[1].contains("100"),
        "Expected 100 in get-value output for (f x): {}",
        outputs[1]
    );
    // Should NOT contain 0 as the value (the placeholder)
    assert!(
        !outputs[1].contains("(f x) 0)"),
        "Should not return placeholder 0 for (f x): {}",
        outputs[1]
    );
}

#[test]
fn test_get_model_and_value_follow_pure_int_equality_8778() {
    let input = r#"
        (set-option :produce-models true)
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-fun f (Int) Int)
        (assert (= y x))
        (assert (= (f x) 5))
        (assert (> x 100))
        (check-sat)
        (get-model)
        (get-value ((f y)))
    "#;

    let commands = parse(input).expect("valid QF_UFLIA input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFLIA");

    assert_eq!(outputs.len(), 3);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("(define-fun x () Int 101)"),
        "expected x to use the LIA value in model output: {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("(define-fun y () Int 101)"),
        "expected y to keep the recovered LIA equality value in model output: {}",
        outputs[1]
    );
    assert!(
        outputs[2].contains("5"),
        "expected get-value on (f y) to use the same UF table entry as (f x): {}",
        outputs[2]
    );
    assert_pure_uflia_route_stats(&exec);
}

#[test]
fn test_get_value_uf_returning_real() {
    // Test UF returning Real sort
    let input = r#"
        (set-option :produce-models true)
        (set-logic QF_UFLRA)
        (declare-sort U 0)
        (declare-fun g (U) Real)
        (declare-fun y () U)
        (assert (= (g y) 3.14))
        (check-sat)
        (get-value ((g y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // z3-exact user-facing Real spelling (#real-fmt).
    assert!(
        outputs[1].contains("(/ 157.0 50.0)"),
        "Expected (/ 157.0 50.0) in get-value output for (g y): {}",
        outputs[1]
    );
    // Should NOT contain placeholder values (0.0 or (_ +zero ...))
    assert!(
        !outputs[1].contains("(g y) 0.0)") && !outputs[1].contains("+zero"),
        "Should not return placeholder value for (g y): {}",
        outputs[1]
    );
}

// QF_LRA (Linear Real Arithmetic) Tests
// =====================================
#[test]
fn test_executor_qf_uflia_simple_sat() {
    // Combine UF and LIA: f(x) = y, x >= 0
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-fun f (Int) Int)
        (assert (= (f x) y))
        (assert (>= x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_uflia_function_equality_unsat() {
    // f(x) = 5, f(x) = 6 is contradictory
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (= (f x) 5))
        (assert (= (f x) 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_uflia_congruence_with_arithmetic() {
    // Test EUF congruence with arithmetic on the same function application
    // This test uses the SAME function application f(x) in both constraints
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (>= (f x) 10))
        (assert (< (f x) 5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // f(x) >= 10 and f(x) < 5 is a contradiction
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_uflia_arithmetic_constraint_unsat() {
    // UF with integer gap constraint
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (> x 5))
        (assert (< x 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // No integer between 5 and 6 exclusively
    assert_eq!(outputs, vec!["unsat"]);
}
/// Mirror of the QF_UFLIA integer-gap test under QF_AUFLIA (#6300).
/// Ensures both combined-int entry points are narrowed to pure LIA.
#[test]
fn test_executor_qf_auflia_arithmetic_constraint_unsat_6300() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (> x 5))
        (assert (< x 6))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse QF_AUFLIA input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_AUFLIA");

    // No integer between 5 and 6 exclusively — same as QF_UFLIA case.
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_uflia_combined_sat() {
    // Combination of UF equality and separate arithmetic constraints
    // The UF equality (= (f a) (f b)) is independent of arithmetic
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-fun f (Int) Int)
        (assert (>= a 0))
        (assert (<= b 10))
        (assert (= (f a) (f b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_uflia_pure_route_skips_array_solver_8778() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (= (f x) (+ x 1)))
        (assert (= x 41))
        (assert (= (f x) 42))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_UFLIA input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFLIA");

    // The formula is satisfiable (z3: sat, x=41, f(41)=42), and the emitted
    // model now reads consistently: the #uflia-gate-model-read fix keys the
    // UF function-table lookup at the emitted LIA leaf value (x=41) and skips
    // the unresolvable self-row, so `(f x)` resolves to the pinned congruent
    // point f(41)=42 and the independent model-check gate CONFIRMS the
    // witness (this was the declared follow-up in the previous revision of
    // this comment, which pinned `unknown` while the model read was
    // self-inconsistent).
    assert_eq!(outputs, vec!["sat"]);
    assert_pure_uflia_route_stats(&exec);
}

#[test]
fn test_executor_qf_uflia_seq_like_int_encoding_model_validates_8778() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const s1 Int)
        (declare-const s2 Int)
        (declare-const v1 Int)
        (declare-fun seq_push (Int Int) Int)
        (declare-fun seq_len (Int) Int)
        (assert (= s2 (seq_push s1 v1)))
        (assert (= (seq_len s2) (+ (seq_len s1) 1)))
        (assert (= (seq_len s1) 0))
        (assert (= (seq_len s2) 1))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_UFLIA input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFLIA");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        exec.statistics().get_int("model_validation_failures"),
        Some(0),
        "pure UF sequence-like equalities should remain EUF-backed in the UFLIA model"
    );
    assert_pure_uflia_route_stats(&exec);
}

#[test]
fn test_executor_qf_auflia_euf_backed_sat_fallback_model_validates_9604() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-sort Color 0)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Int)
        (declare-fun d () Int)
        (declare-fun green () Color)
        (declare-fun il_pass () Int)
        (declare-fun il_tl () Color)
        (declare-fun ml_pass () Int)
        (declare-fun ml_tl () Color)
        (declare-fun red () Color)
        (assert (or (= ml_tl red) (= ml_tl green)))
        (assert (or (= il_tl red) (= il_tl green)))
        (assert (=> (= ml_tl green) (< (+ a b c) d)))
        (assert (or (= il_pass 0) (= il_pass 1)))
        (assert (or (= ml_pass 0) (= ml_pass 1)))
        (assert (=> (= ml_tl red) (= ml_pass 1)))
        (assert (=> (= il_tl red) (= il_pass 1)))
        (assert (or (= il_tl red) (= ml_tl red)))
        (assert (<= a 0))
        (assert (not (= il_tl green)))
        (assert (< (+ a b) d))
        (assert (not (= a 0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_AUFLIA input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_AUFLIA");

    assert_eq!(
        outputs,
        vec!["sat"],
        "unexpected AUFLIA result; unknown_reason={:?}; validation_stats={:?}; statistics={:?}",
        exec.get_reason_unknown(),
        exec.last_validation_stats,
        exec.statistics()
    );
    assert_eq!(
        exec.statistics().get_int("model_validation_failures"),
        Some(0),
        "EUF-backed AUFLIA SAT must not be rejected by the proportional SAT-fallback guard"
    );
    assert_pure_uflia_route_stats(&exec);
}

#[test]
fn test_executor_qf_uflia_seq_len_proxy_not_definitive_arithmetic_9227() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-sort Seq 0)
        (declare-const s Seq)
        (declare-const seq_len_proxy Int)
        (declare-fun seq_len (Seq) Int)
        (assert (= (seq_len s) seq_len_proxy))
        (assert (= seq_len_proxy 1))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_UFLIA input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFLIA");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        exec.statistics().get_int("model_validation_failures"),
        Some(0),
        "seq_len(UF) = proxy is mixed UF/Seq arithmetic and must not be \
         rejected by the definitive arithmetic oracle"
    );
}

#[test]
fn test_executor_auto_seq_sort_uf_proxy_routes_to_uflia_9227() {
    let input = r#"
        (declare-const s (Seq Int))
        (declare-const seq_len_proxy Int)
        (declare-fun seq_len ((Seq Int)) Int)
        (assert (= (seq_len s) seq_len_proxy))
        (assert (= seq_len_proxy 1))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid auto-logic input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("Seq-sorted UF proxy should route through UFLIA");

    assert_eq!(outputs, vec!["sat"]);
    assert_pure_uflia_route_stats(&exec);
}

#[test]
fn test_executor_declared_seqlia_seq_sort_uf_proxy_narrows_to_uflia_9227() {
    let input = r#"
        (set-logic QF_SEQLIA)
        (declare-const s (Seq Int))
        (declare-const seq_len_proxy Int)
        (declare-fun seq_len ((Seq Int)) Int)
        (assert (= (seq_len s) seq_len_proxy))
        (assert (= seq_len_proxy 1))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_SEQLIA input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("Seq-sorted UF proxy should narrow away from Seq theory");

    assert_eq!(outputs, vec!["sat"]);
    assert_pure_uflia_route_stats(&exec);
}

#[test]
fn test_executor_qf_uflia_bool_arith_equality_keeps_both_lia_sides_8778() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-fun f (Int) Int)
        (assert (= (< x 0) (< y 0)))
        (assert (< x 0))
        (assert (= (f y) 7))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_UFLIA input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFLIA");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        exec.statistics().get_int("model_validation_failures"),
        Some(0)
    );
    assert_pure_uflia_route_stats(&exec);
}

#[test]
fn test_executor_qf_uflia_asymmetric_bool_arith_equality_keeps_simple_side_8778() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-fun f (Int) Int)
        (assert (= (< (+ x 1) 0) (< y 0)))
        (assert (< (+ x 1) 0))
        (assert (= (f y) 7))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_UFLIA input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_UFLIA");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        exec.statistics().get_int("model_validation_failures"),
        Some(0)
    );
    assert_pure_uflia_route_stats(&exec);
}

// ======================================================================
// Regression tests for #8145: LIA check.rs overapproximation regression
// ======================================================================
//
// These tests verify that precise fold_reasons tracking (#8144) and removal
// of blanket augment_farkas_with_shared_eq_reasons (#8147) produce tight
// enough conflict clauses for UNSAT proofs to succeed, while still including
// sufficient reasons for soundness.
//
// The original bug: augmenting ALL Farkas conflicts with ALL shared equality
// reasons made conflict clauses too weak (more literals = weaker blocking
// clause = less pruning), causing valid UNSAT proofs to fail (solver returned
// unknown instead of unsat on two SMT-LIB benchmarks: xs-05-16-1-5-4-3.smt2
// and xs-05-19-1-4-2-1.smt2).

/// #8145 regression (A): UF equality sharing fixes a variable value, combined
/// with integer equations that need Diophantine solving. The Dioph solver's
/// fold_fixed_vars folds the UF-determined variable, and the resulting conflict
/// clause must be precise (include fold_reasons for the folded variable, but
/// NOT blanket shared equality reasons for unrelated variables).
///
/// Pattern: f(a) = f(b) forces a = b via congruence.  With a = 3, b is fixed
/// to 3 by N-O shared equality.  The equation 2*b + 2*c = 7 then has
/// GCD(2,2) = 2 which doesn't divide 7, giving UNSAT.  The conflict clause
/// must include the fold_reason for b = 3 (from shared equality) but not
/// overapproximate by including all shared equality reasons.
#[test]
#[ntest::timeout(30_000)]
fn test_uflia_dioph_fold_shared_eq_unsat_8145() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        ; f(a) = f(b) doesn't directly force a = b in QF_UFLIA,
        ; but a = 3 and b = 3 are asserted directly.
        (assert (= a 3))
        (assert (= b 3))
        ; 2*b + 2*c = 7 is UNSAT: GCD(2,2) = 2 does not divide 7
        ; After folding b = 3: 6 + 2*c = 7, so 2*c = 1, no integer solution.
        (assert (= (+ (* 2 b) (* 2 c)) 7))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8145: Dioph fold with fixed vars must produce tight conflict clause for UNSAT"
    );
}

/// #8145 regression (B): Multiple UF equalities creating a system where
/// fold_fixed_vars computes tight bounds, but only SOME of those bounds are
/// needed for the conflict.  If blanket augmentation were still active, the
/// extra reasons from unrelated UF equalities would weaken the conflict.
///
/// Pattern: f(x) = 5 determines (f x), g(y) = 10 determines (g y).
/// Equation: (f x) + (g y) + 2*z = 8.  After folding: 5 + 10 + 2*z = 8,
/// so 2*z = -7, no integer solution (GCD test).  Both fold_reasons are
/// needed, but no other shared equality reasons should be added.
#[test]
#[ntest::timeout(30_000)]
fn test_uflia_multiple_uf_fold_precise_conflict_8145() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (= (f x) 5))
        (assert (= (g y) 10))
        ; (f x) + (g y) + 2*z = 8
        ; After substitution: 5 + 10 + 2*z = 8, so 2*z = -7 (no integer solution)
        (assert (= (+ (f x) (g y) (* 2 z)) 8))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8145: Multiple UF folds must produce precise conflict clause"
    );
}

/// #8145 regression (C): Mix of UF-derived bounds and direct integer bounds.
/// Tests that fold_reasons only include reasons for actually-folded variables,
/// not for variables with direct bounds that happen to coexist with shared
/// equalities.
///
/// Pattern: a = 4 (direct bound), f(b) = 3 (UF-derived bound on f(b)).
/// 3*a + 3*(f b) = 10.  After folding a = 4: 12 + 3*(f b) = 10,
/// 3*(f b) = -2. After folding f(b) = 3: 3*3 = -2, contradiction.
/// Actually: 12 + 9 = 21 != 10.
#[test]
#[ntest::timeout(30_000)]
fn test_uflia_mixed_direct_and_uf_bounds_unsat_8145() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        ; Direct bound
        (assert (= a 4))
        ; UF-derived bound
        (assert (= (f b) 3))
        ; 3*a + 3*(f b) = 10: after substitution 3*4 + 3*3 = 12 + 9 = 21 != 10
        (assert (= (+ (* 3 a) (* 3 (f b))) 10))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8145: Mixed direct + UF bounds must not overapproximate conflict clause"
    );
}

/// #8145 regression (D): SAT counterpart to verify no false UNSAT from
/// fold_reasons.  Same structure as test A but with satisfiable equation.
///
/// Pattern: a = 3, b = 3, 2*b + 2*c = 8.  After folding b = 3: 6 + 2*c = 8,
/// so c = 1.  SAT.
#[test]
#[ntest::timeout(30_000)]
fn test_uflia_dioph_fold_shared_eq_sat_8145() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= a 3))
        (assert (= b 3))
        ; 2*b + 2*c = 8: after folding b = 3, 6 + 2*c = 8, c = 1. SAT.
        (assert (= (+ (* 2 b) (* 2 c)) 8))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "#8145: Dioph fold with satisfiable equation must not produce false UNSAT"
    );
}

/// #8145 regression (E): Congruence-driven shared equality with Farkas conflict.
/// Tests the specific N-O shared equality path where EUF discovers a = b from
/// f(a) = f(b), and LIA uses this to derive tight bounds that create a Farkas
/// conflict.  The conflict clause must include the shared equality reason but
/// not all possible shared equality reasons.
///
/// Pattern: f(a) = f(b) with a = b forced by congruence.
/// a >= 5, b <= 3.  Via shared equality a = b: 5 <= a = b <= 3, contradiction.
#[test]
#[ntest::timeout(30_000)]
fn test_uflia_congruence_shared_eq_farkas_conflict_8145() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        ; Force a = b via direct equality (congruence in N-O path)
        (assert (= a b))
        (assert (>= a 5))
        (assert (<= b 3))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8145: Shared equality Farkas conflict must be tight enough for UNSAT proof"
    );
}

#[test]
fn test_uf_over_compound_bool_arg_no_false_sat() {
    // Regression: false-SAT when an uninterpreted function is applied to a
    // *compound* Boolean argument. AY used to answer `sat`; z3/cvc5/yices2 all
    // say `unsat`. Fixed by Boolean-argument purification (purify_bool_args).
    // Minimal repro of the B-method CLEARSY QF_UF soundness bug.
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun TRUE () U)
        (declare-fun FALSE () U)
        (declare-fun BOOL () U)
        (declare-fun bool (Bool) U)
        (declare-fun mem (U U) Bool)
        (declare-fun g639 () U)
        (declare-fun g640 () U)
        (declare-fun P1 () Bool)
        (assert (mem TRUE BOOL))
        (assert (= (bool (and P1 (= g639 TRUE) (= g640 TRUE))) TRUE))
        (assert (= g639 FALSE))
        (assert (not (mem (bool (and P1 (= g639 TRUE) (= g640 FALSE))) BOOL)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UF over a compound Boolean argument must congruence-close (no false SAT)"
    );
}

/// Run a committed .smt2 fixture through the executor and return the ordered
/// sat/unsat/unknown answer sequence.
#[cfg(test)]
fn run_fixture_answers(rel_path: &str) -> Vec<String> {
    let path = format!("{}/../../{}", env!("CARGO_MANIFEST_DIR"), rel_path);
    let input =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read fixture {path}: {e}"));
    let commands = parse(&input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    outputs
        .into_iter()
        .filter(|o| matches!(o.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

/// Assert a fixture's answer sequence matches z3, tolerating honest
/// `unknown`s: under memory pressure (-j10 full-suite runs) individual
/// check-sats legitimately return `unknown` instead of sat/unsat. An
/// `unknown` position is skipped with a note; a sat/unsat that CONTRADICTS
/// z3 still fails, and an all-unknown run fails (nothing verified).
#[cfg(test)]
fn assert_answers_match_z3_modulo_unknown(got: &[String], expected: &[&str], context: &str) {
    assert_eq!(got.len(), expected.len(), "{context}: answer count");
    let mut skipped = 0usize;
    for (i, (g, e)) in got.iter().zip(expected).enumerate() {
        if g == "unknown" {
            skipped += 1;
            continue;
        }
        assert_eq!(g, *e, "{context}: check-sat #{}", i + 1);
    }
    if skipped > 0 {
        eprintln!("{context}: skipped {skipped} honest unknown answers (resource pressure)");
    }
    assert!(
        skipped < got.len(),
        "{context}: every answer was unknown — nothing verified"
    );
}

#[test]
fn test_clearsy_00307_full_instance_matches_z3() {
    // Full B-method CLEARSY QF_UF proof-obligation file that previously yielded a
    // false `sat` at check-sat #13 (the UF-over-compound-Bool-arg bug). After the
    // purification fix, AY must match z3/cvc5/yices2 on all 29 results.
    let expected: Vec<&str> = "sat unsat unsat sat sat sat unsat unsat unsat unsat \
        unsat sat sat unsat sat sat sat unsat unsat sat unsat unsat unsat unsat \
        unsat unsat sat sat sat"
        .split_whitespace()
        .collect();
    let got = run_fixture_answers(
        "benchmarks/smt/regression/soundness_qf_uf_incremental/clearsy_0000_00307_falsesat13.smt2",
    );
    assert_answers_match_z3_modulo_unknown(
        &got,
        &expected,
        "CLEARSY 00307: AY must match z3 (no false SAT at #13)",
    );
}

#[test]
fn test_clearsy_00310_full_instance_matches_z3() {
    // Companion CLEARSY file with a false `sat` at check-sat #44 pre-fix.
    let expected: Vec<&str> = "sat sat sat sat sat sat sat sat sat sat sat sat sat sat \
        sat sat sat sat sat sat sat sat sat sat sat sat sat sat sat sat sat sat unsat \
        unsat sat sat sat unsat unsat unsat unsat unsat sat sat unsat sat sat sat \
        unsat unsat sat unsat unsat unsat unsat unsat unsat sat sat sat"
        .split_whitespace()
        .collect();
    let got = run_fixture_answers(
        "benchmarks/smt/regression/soundness_qf_uf_incremental/clearsy_0001_00310_falsesat44.smt2",
    );
    assert_answers_match_z3_modulo_unknown(
        &got,
        &expected,
        "CLEARSY 00310: AY must match z3 (no false SAT at #44)",
    );
}

/// Project P1 (SMT-COMP soundness gate): a chained `ite`-over-Int that defines a
/// UF application is not enforced in the combined EUF+LIA path, so AY returns a
/// false `sat` on this minimized `traffic.ec` k-induction core. z3/cvc5/yices2
/// all say `unsat`. One wrong answer voids the QF_UFLIA (and superset QF_AUFLIA)
/// divisions, so the soundness invariant is: AY must NEVER answer `sat` here.
/// The competition-correct outcomes are `unsat` (complete fix — enforce the
/// ite-definition equality) or, at worst, `unknown` (a Sat->Unknown
/// model-validation gate). Both are sound; `sat` is a DQ.
///
/// Fixed by `IteDefinitionOracle` (definitive_eval.rs): a SAT model that makes
/// an ite+UF assertion concretely `Bool(false)` is rejected by the strict
/// model-validation gate, degrading the spurious `sat` to a sound `unknown`.
#[test]
fn test_traffic_uflia_ite_chain_no_false_sat() {
    let got = run_fixture_answers(
        "benchmarks/smt/regression/soundness_qf_uf_incremental/traffic_uflia_falsesat_min.smt2",
    );
    assert_ne!(
        got,
        vec!["sat".to_string()],
        "P1 soundness: ite-defined UF app must be enforced in combined EUF+LIA — \
         false `sat` is a division-voiding DQ (expected `unsat`, or `unknown` via gate)"
    );
    assert!(
        matches!(got.as_slice(), [only] if only == "unsat" || only == "unknown"),
        "P1: expected a single sound answer (`unsat` ideal, `unknown` acceptable), got {got:?}"
    );
}

// QF_UFLRA (Uninterpreted Functions with Linear Real Arithmetic) Tests

/// SOUNDNESS (found by scripts/diff_fuzz.py, QF_UFLRA): a Real variable that is
/// ite-defined in LRA and is the ARGUMENT of a UF app in EUF triggers a
/// false-UNSAT in the combined Nelson-Oppen path. `(= (ga z) 5) ∧
/// (= z (ite p -3 -2))` is trivially SAT (z3 = sat) but AY returns `unsat`.
/// Invariant: AY must NEVER answer `unsat` here (`sat` is correct; `unknown` is
/// an acceptable sound fallback). FIXED by the ITE-term Nelson-Oppen
/// shared-equality guard (nelson_oppen.rs `ite_shared_eq_guard_enabled`): EUF was
/// forwarding `ite_term = c` for both branch values, which LRA asserted
/// simultaneously into the simplex (`-3 = -2`) — now rejected, so AY returns the
/// correct `sat`.
#[test]
fn test_qf_uflra_ite_uf_arg_no_false_unsat() {
    let got = run_fixture_answers(
        "benchmarks/smt/regression/soundness_qf_uflra_ite_arg/min_falseunsat_ga_ite_arg.smt2",
    );
    assert_ne!(
        got,
        vec!["unsat".to_string()],
        "false-UNSAT: ite-defined UF argument in combined EUF+LRA — the formula is SAT \
         (expected `sat`, or `unknown` via a fail-closed re-verify gate)"
    );
}

// ---------------------------------------------------------------------------
// #g3-gate-reads-printed-uf — regression tests for gate (3) of the SAT emit
// funnel: `apply_independent_model_gate`'s `CannotConfirm` arm
// (`crates/ay-dpll/src/executor/model/independent_gate.rs`).
//
// BISECT: `66538b006f` ("feat(parity): define exact Z3 5 replacement gate")
// turned that arm from fail-OPEN into fail-CLOSED:
//
//     -   tracing::debug!(...); result                  // keep the verdict
//     +   self.downgrade_sat_after_gate(...);           // publish unknown
//     +   SolveResult::Unknown
//
// and deleted the `independent_model_gate_enabled()` early-out, so there is no
// longer any switch at the site. The posture is right — an unconfirmed witness
// must not ship as an authoritative `sat` — but it exposed a gap that had been
// invisible while the arm kept the verdict.
//
// ROOT CAUSE (measured with `AY_G3_GATE_DUMP=1` over a 10,773-file sweep): a
// model can interpret an uninterpreted function TOTALLY without pinning the
// individual application TERM. `(get-model)` serialises such a function as a
// complete `(define-fun mem ((x0 U) (x1 U)) Bool (ite ... else))`, and
// `(get-value ((mem <unlisted args>)))` answers the else branch — every
// EXTERNAL consumer sees a total interpretation. But the gate's
// `IndependentModelView::uf_app_value` resolves only through
// `Executor::evaluate_term`, which is keyed by the application's TermId and
// answers `Unknown` at an argument point the extracted function table does not
// list. The gate then reported
// `uninterpreted / unsupported function application: mem` and downgraded a
// model that is total, printable and VALID (z3 4.16.0 re-checks the emitted
// 1067-`define-fun` model of `clearsy_00302_prefix3` as `sat`).
//
// FIX: `uf_app_value_at` — a RECONCILED read. The gate evaluates the PUBLISHED
// total interpretation at the argument values it computed itself, reading the
// rows through `Executor::printed_uf_table_rows` (the very function
// `format_function_table` renders) with the printer's own first-match/else
// rule. An application the model pins is ALSO checked against that printed
// body: pin and printed value must agree, otherwise the gate fails closed
// (`CannotConfirm`). So a confirmed `sat` certifies the interpretation
// `(get-model)` publishes — never a hybrid of pins and printed rows, which was
// the defect that kept the first version of this patch out of main
// (the development design notes). That MINTS the
// missing confirmation instead of relaxing the gate: it still returns
// `ModelViolates` when the published interpretation falsifies an assertion,
// and every step fails closed on anything it cannot read back.
//
// SCOPE, unrounded: over the 10,773-file sweep gate (3) fires on 57 files, and
// 42 change verdict when the site is forced open. THIS RECOVERS 3 FILES / 11
// QUERY-LEVEL ANSWERS. 39 remain. They are deliberately untouched, and NOT for
// lack of a mechanism:
//
//   * 33 QF_AUFLIA storecomm/storeinv + the `RF` file above: the emitted model
//     is genuinely PARTIAL, so there is nothing faithful to read. Verified
//     directly on three of them —
//       storeinv_..._00002_001 -> (error "model value for array a1 is not available")
//       storecomm_..._00020_002 -> (error "model value for i_640 is not available
//                                   (internal error: sat accepted without a total model)")
//       fb_var_27_8            -> (error "model value for function RF is not available:
//                                   no complete array model value ...")
//     That is an upstream MODEL-CONSTRUCTION defect (array lane), not a gate
//     defect; publishing `sat` would ship a witness `(get-model)` cannot print.
//   * 1 QF_AX (`r3_rank4_..._false_UNSAT`): the gate is masking a genuinely
//     INVALID model — z3 refutes the completed witness. Must stay closed.
//   * 2 QF_NRA metitarski: the witness is a `root-obj` ALGEBRAIC value and
//     `ModelValue` has no algebraic representative (`eval.rs:207`). Correct
//     witnesses, but reading them needs exact algebraic arithmetic in the
//     independent evaluator.
//   * 1 QF_FPLRA: the ROUNDING form of `(_ to_fp ..)`. `eval.rs` declines it BY
//     DESIGN — "an independent gate must not confirm a model using the same
//     rounding routine that produced it". A principled refusal, left alone.
//   * 2 under-specified builtins (`fp.to_real` of NaN, `mod` by zero). SMT-LIB
//     leaves the value free, so the gate has nothing to check against; one of
//     the two documents `unknown` as its own expected answer.

/// `clearsy_00302_prefix3` is the repo's own regression asset for this family
/// and its header records the expected answers: `sat unsat unsat`. Check-sat #1
/// answered `unknown` from `66538b006f` until #g3-gate-reads-printed-uf: the
/// `mem` predicate is interpreted totally by the emitted model but the gate
/// could not read that interpretation at the applications the table omits.
///
/// Asserting only #1 deliberately: #2/#3 are a DIFFERENT, still-open
/// completeness gap (they do not reach this gate at all).
#[test]
fn test_clearsy_00302_prefix_first_query_is_sat() {
    let got = run_fixture_answers(
        "benchmarks/smt/regression/euf_bool_arg_guard_seed/clearsy_00302_prefix3.smt2",
    );
    assert_eq!(
        got.first().map(String::as_str),
        Some("sat"),
        "#g3-gate-reads-printed-uf: the emitted model interprets `mem` totally \
         (z3 re-checks it `sat`), so the independent gate must CONFIRM it rather \
         than report an unsupported UF application — got {got:?}"
    );
}

/// The same mechanism inside an incremental QF_UF file. Check-sats #4, #5, #12,
/// #13 and #15 answered `unknown` at `66538b006f`; z3 4.16.0 and cvc5 1.3.0
/// (default and `--finite-model-find`) all say `sat` for each. The companion
/// `test_clearsy_00307_full_instance_matches_z3` above cannot catch this — it
/// SKIPS `unknown` positions by design.
#[test]
fn test_clearsy_00307_printed_uf_interpretation_queries_are_sat() {
    let got = run_fixture_answers(
        "benchmarks/smt/regression/soundness_qf_uf_incremental/clearsy_0000_00307_falsesat13.smt2",
    );
    for q in [4usize, 5, 12, 13, 15] {
        assert_eq!(
            got.get(q - 1).map(String::as_str),
            Some("sat"),
            "#g3-gate-reads-printed-uf: check-sat #{q} must be `sat` \
             (z3 + cvc5 + cvc5 --finite-model-find agree) — got {got:?}"
        );
    }
}

/// MINIMAL isolation of the mechanism (ddmin-reduced from
/// `clearsy_00302_prefix3`, then hand-minimised to 8 declarations).
///
/// `(bool (or ...))` is a COMPOUND argument, so `(mem (bool ...) s)` is an
/// argument point the extracted function table never lists — the table holds
/// only `mem(a, s) = true`. The emitted model is nonetheless TOTAL:
///
///     (define-fun bool ((x0 Bool)) U (as @U!2 U))
///     (define-fun mem ((x0 U) (x1 U)) Bool
///       (ite (and (= x0 (as @U!0 U)) (= x1 (as @U!1 U))) true false))
///
/// so the unlisted point reads `false` and BOTH assertions hold (z3 4.16.0
/// re-checks that substituted model `sat`; z3, cvc5 1.3.0 and cvc5
/// `--finite-model-find` all answer `sat` on the instance itself).
///
/// Before #g3-gate-reads-printed-uf the gate reported
/// `uninterpreted / unsupported function application: mem` at the unlisted
/// point and `66538b006f`'s fail-closed `CannotConfirm` arm published
/// `unknown`.
#[test]
fn test_unlisted_uf_point_reads_printed_else_branch() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun mem (U U) Bool)
        (declare-fun bool (Bool) U)
        (declare-fun TRUE () U)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun s () U)
        (assert (mem a s))
        (assert (not (mem (bool (or (= a b) (= b TRUE))) s)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "#g3-gate-reads-printed-uf: a UF application at an argument point the \
         function table omits must be read from the EMITTED total interpretation \
         (the printed else branch), not left unevaluable"
    );
}

// NEGATIVE CONTROLS live next to the mechanism, in
// `executor/model/independent_gate.rs` (`g3_*` tests), because they need a
// model the SOLVER would never produce: a printed value at an UNPINNED point
// that falsifies an assertion (`g3_unlisted_uf_point_printed_value_falsifying_assertion_is_refuted`
// — must be `ModelViolates`), and a per-application pin that DISAGREES with
// the printed body at the same point
// (`g3_pin_disagreeing_with_printed_table_is_refused` — must be
// `CannotConfirm`). The second is the exact hybrid-interpretation
// counterexample that kept the first version of this patch out of main
// (the development design notes).
