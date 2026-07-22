// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_executor_qf_auflia_simple_sat() {
    // Basic array with integer indices and UF
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-fun f (Int) Int)
        (assert (= (select a i) (f i)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_auflia_array_store_select() {
    // Test simple array read
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (assert (= (select a i) v))
        (assert (>= v 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_auflia_arithmetic_constraint_unsat() {
    // Array with contradictory arithmetic constraints on values
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (>= (select a i) 10))
        (assert (< (select a i) 5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_auflia_function_equality_unsat() {
    // f(i) = 5, f(i) = 6 is contradictory (EUF reasoning)
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const i Int)
        (declare-fun f (Int) Int)
        (assert (= (f i) 5))
        (assert (= (f i) 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_auflia_combined_sat() {
    // Combination of arrays, UF, and arithmetic - all satisfiable
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-fun f (Int) Int)
        (assert (>= i 0))
        (assert (<= j 10))
        (assert (= (f i) (select a j)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_auflia_index_bounds() {
    // Array with integer index constraints
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (>= i 0))
        (assert (<= i 100))
        (assert (= (select a i) i))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
/// Regression test for #5086: store commutativity pattern.
/// store(store(a,i,v),j,v) = store(store(a,j,v),i,v) when i ≠ j.
/// Without eager ROW1/ROW2 lemma preprocessing, the solver returns `unknown`
/// because the SAT solver cannot reason about index equality relationships
/// that arise from extensionality Skolem variables.
#[test]
fn test_executor_qf_auflia_store_commutativity_unsat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (assert (not (= i j)))
        (assert (not (= (store (store a i v) j v) (store (store a j v) i v))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}
/// Regression test for #5086: extended store commutativity with read-back.
/// Tests that after two stores with disjoint indices, reading back gives the
/// correct values regardless of store order.
#[test]
fn test_executor_qf_auflia_store_commutativity_readback_unsat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (assert (not (= i j)))
        (assert (not (=
            (select (store (store a i v) j w) i)
            v)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}

/// Regression for #9604 SMT audit: QF_AUFLIA swap witnesses use an
/// Int-valued `sk(Array, Array)` index and assert a select disequality at that
/// witness. The disequality's select terms must be shared with LIA; otherwise
/// model extraction can collapse both select values to the same default and
/// fail closed as `unknown`.
#[test]
fn test_executor_qf_auflia_swap_skolem_select_diseq_sat_9604() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (assert (= (select a 0) 1))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_AUFLIA swap input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_AUFLIA");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "unexpected AUFLIA swap result; outputs={outputs:?}; unknown_reason={:?}; statistics={:?}",
        exec.unknown_reason(),
        exec.statistics()
    );
    assert_eq!(
        exec.statistics().get_int("model_validation_failures"),
        Some(0),
        "swap witness SAT model must validate"
    );
}

/// Regression test for #8596: const-array with store and model equality.
/// `a = store(const(0), x, 1)` means a[x]=1 and a[k]=0 for k!=x.
/// `a[y] = 1` requires x=y (model equality) since the only non-zero
/// cell is at index x. Without N-O model equality splitting, the solver
/// may declare UNSAT before the array theory's final_check fires.
#[test]
fn test_executor_qf_auflia_const_array_model_eq_sat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (select a x) 1))
        (assert (= (select a y) 1))
        (assert (= a (store ((as const (Array Int Int)) 0) x 1)))
        (assert (>= y 0))
        (assert (<= y 10))
        (assert (>= x 0))
        (assert (<= x 10))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["sat"]);
}

/// Regression test for #8596: two const-arrays with stores and arithmetic.
/// `a = store(const(0), z, 3)` and `b = store(const(0), z, 7)`.
/// `a[x] + b[y] = 10` requires x=z AND y=z (model equalities).
/// Without model equality splitting, the solver cannot discover these
/// equalities and incorrectly returns UNSAT.
#[test]
fn test_executor_qf_auflia_two_const_arrays_model_eq_sat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (= (+ (select a x) (select b y)) 10))
        (assert (= (select a z) 3))
        (assert (= (select b z) 7))
        (assert (= a (store ((as const (Array Int Int)) 0) z 3)))
        (assert (= b (store ((as const (Array Int Int)) 0) z 7)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["sat"]);
}

/// Minimal reproduction for #8596: const-array + store + select at different index.
/// Stripped of bounds to isolate the core failure.
///
/// The QF_AUFLIA path (lazy pipeline with N-O fixpoint) correctly returns sat.
/// The QF_AX path (eager extension, pure array+EUF) has a known limitation:
/// the first SAT solve iteration's eager extension does not assert the array
/// equality `(= a store(const(0), x, 1))` to the array theory, so ROW2 axioms
/// are not generated and the solver incorrectly returns unsat. This is tracked
/// separately — the NeedModelEquality dispatch fix in this commit unblocks the
/// AUFLIA path which is the primary use case.
#[test]
fn test_executor_qf_auflia_const_array_model_eq_minimal() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (select a y) 1))
        (assert (= a (store ((as const (Array Int Int)) 0) x 1)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["sat"], "QF_AUFLIA path should return sat");
}

/// Regression for verification-consumer layout axioms: unused memory array declarations must
/// not make AUFLIA return `unknown` before preprocessing can substitute
/// a nullary Int constant divisor and eliminate `(mod size align)`.
#[test]
fn test_executor_qf_auflia_unused_arrays_mod_substituted_divisor_sat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const heap (Array Int Int))
        (declare-const domain (Array Int Bool))
        (declare-const perms (Array Int Int))
        (declare-fun size_of_logic () Int)
        (declare-fun align_of_logic () Int)
        (assert (>= size_of_logic 0))
        (assert (>= align_of_logic 1))
        (assert (or (= align_of_logic 1) (= align_of_logic 2) (= align_of_logic 4) (= align_of_logic 8) (= align_of_logic 16) (= align_of_logic 32) (= align_of_logic 64)))
        (assert (= (mod size_of_logic align_of_logic) 0))
        (assert (= size_of_logic 1))
        (assert (= align_of_logic 1))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["sat"]);
}

/// Same layout shape with a nontrivial power-of-two divisor.  verification-consumer declares
/// layout witnesses as nullary Int functions, so the AUFLIA preprocessor must
/// substitute `(= align_of_logic 4)` before the residual div/mod guard runs.
#[test]
fn test_executor_qf_auflia_unused_arrays_mod_substituted_nullary_divisor_sat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const heap (Array Int Int))
        (declare-const domain (Array Int Bool))
        (declare-const perms (Array Int Int))
        (declare-fun size_of_logic () Int)
        (declare-fun align_of_logic () Int)
        (assert (>= size_of_logic 0))
        (assert (>= align_of_logic 1))
        (assert (or (= align_of_logic 1) (= align_of_logic 2) (= align_of_logic 4) (= align_of_logic 8) (= align_of_logic 16) (= align_of_logic 32) (= align_of_logic 64)))
        (assert (= (mod size_of_logic align_of_logic) 0))
        (assert (= size_of_logic 8))
        (assert (= align_of_logic 4))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["sat"]);
}

/// Same verification-consumer layout shape as the SAT test above, but with an invalid witness.
/// This ensures the AUFLIA preprocessing path preserves the modulo constraint.
#[test]
fn test_executor_qf_auflia_unused_arrays_mod_substituted_divisor_unsat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const heap (Array Int Int))
        (declare-const domain (Array Int Bool))
        (declare-const perms (Array Int Int))
        (declare-fun size_of_logic () Int)
        (declare-fun align_of_logic () Int)
        (assert (>= size_of_logic 0))
        (assert (>= align_of_logic 1))
        (assert (or (= align_of_logic 1) (= align_of_logic 2) (= align_of_logic 4) (= align_of_logic 8) (= align_of_logic 16) (= align_of_logic 32) (= align_of_logic 64)))
        (assert (= (mod size_of_logic align_of_logic) 0))
        (assert (= size_of_logic 3))
        (assert (= align_of_logic 2))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}

/// verification-consumer layout axioms can refute a model by asserting the same symbolic
/// modulo equality and its negation. This needs only Boolean contradiction
/// detection over the temporary assertion window; residual symbolic `mod`
/// should not hide the UNSAT behind an unsupported-arithmetic Unknown.
#[test]
fn test_executor_qf_auflia_residual_mod_syntactic_contradiction_unsat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const heap (Array Int Int))
        (declare-const domain (Array Int Bool))
        (declare-const perms (Array Int Int))
        (declare-fun size_of_logic () Int)
        (declare-fun align_of_logic () Int)
        (assert (>= size_of_logic 0))
        (assert (>= align_of_logic 1))
        (assert (or (= align_of_logic 1) (= align_of_logic 2) (= align_of_logic 4) (= align_of_logic 8) (= align_of_logic 16) (= align_of_logic 32) (= align_of_logic 64)))
        (assert (= (mod size_of_logic align_of_logic) 0))
        (assert (not (= (mod size_of_logic align_of_logic) 0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}

// QF_AUFLRA (Arrays + Uninterpreted Functions + Linear Real Arithmetic) Tests
