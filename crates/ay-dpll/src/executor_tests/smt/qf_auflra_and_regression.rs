// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_executor_qf_auflra_simple_sat() {
    // Basic array with real-valued contents and UF
    let input = r#"
        (set-logic QF_AUFLRA)
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (declare-fun f (Int) Real)
        (assert (= (select a i) (f i)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_auflra_array_arithmetic_unsat() {
    // Array with contradictory real arithmetic constraints
    let input = r#"
        (set-logic QF_AUFLRA)
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (assert (>= (select a i) 10.0))
        (assert (< (select a i) 5.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_auflra_function_equality_unsat() {
    // f(x) = 5.5, f(x) = 6.5 is contradictory
    let input = r#"
        (set-logic QF_AUFLRA)
        (declare-const x Int)
        (declare-fun f (Int) Real)
        (assert (= (f x) 5.5))
        (assert (= (f x) 6.5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_auflra_combined_sat() {
    // Combination of arrays, UF, and real arithmetic - all satisfiable
    // Note: Arithmetic constraints on UF terms should be handled by the EUF solver,
    // while arithmetic on array select results go to LRA.
    let input = r#"
        (set-logic QF_AUFLRA)
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const x Real)
        (declare-fun f (Int) Real)
        (assert (= (select a i) x))
        (assert (>= x 0.0))
        (assert (= (f i) (f j)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_auflra_real_constraints() {
    // Array values constrained by real arithmetic
    let input = r#"
        (set-logic QF_AUFLRA)
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (declare-const x Real)
        (assert (= (select a i) x))
        (assert (>= x 1.5))
        (assert (<= x 2.5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

// =========================================================================
// Nelson-Oppen equality propagation regressions (#4915)
// =========================================================================
/// QF_UFLRA interface arithmetic contradiction (#4915 Case B).
///
/// x = 2.0, (+ x 1.0) = (f y), NOT (f y) = 3.0 is unsatisfiable because
/// (+ x 1.0) evaluates to 3.0 under x = 2.0, so (f y) = 3.0 is implied
/// by congruence. Without the interface bridge in UfLraSolver, AY fails
/// to evaluate (+ x 1.0) and propagate the result to EUF.
#[test]
fn test_uflra_interface_bridge_contradiction_4915() {
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (declare-fun f (Real) Real)
        (assert (= x 2.0))
        (assert (= (+ x 1.0) (f y)))
        (assert (not (= (f y) 3.0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}
/// QF_LIRA cross-sort contradiction (#4915 Case A).
///
/// x = 1 (Int), to_real(x) = r, r = 2.0 is unsatisfiable because
/// to_real(1) = 1.0 ≠ 2.0. Without cross-sort value propagation from
/// LIA to LRA, the solver misses that x = 1 in LIA implies x = 1.0 in LRA.
///
/// Two bugs were involved:
/// 1. `to_real` was not recognized as a pure arithmetic term, so the equality
///    `(= (to_real x) r)` was not routed to LRA at all.
/// 2. `propagate_cross_sort_values` was called before `lra.check()`, when LRA's
///    `term_to_var` was still empty (variables are lazily created during check).
#[test]
fn test_lira_cross_sort_contradiction_4915() {
    let input = r#"
        (set-logic QF_LIRA)
        (declare-fun x () Int)
        (declare-fun r () Real)
        (assert (= x 1))
        (assert (= (to_real x) r))
        (assert (= r 2.0))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}
/// QF_UFLRA: UF function with Real arithmetic argument (#4915).
///
/// f((+ x 1.0)) is a UF application where the argument `(+ x 1.0)` is a
/// Real arithmetic expression. Without `track_uf_arith_args`, this argument
/// is not registered as an interface term, so the bridge never evaluates it
/// under the LRA model. With x = 2.0, `(+ x 1.0)` = 3.0, and the bridge
/// should propagate `f(3.0) = f((+ x 1.0))` to EUF via congruence.
///
/// The formula is unsat because:
/// - x = 2.0 → (+ x 1.0) = 3.0
/// - f(3.0) = 10.0 (asserted)
/// - f((+ x 1.0)) = f(3.0) = 10.0 (by congruence via bridge evaluation)
/// - But f((+ x 1.0)) ≠ 10.0 (asserted) — contradiction
#[test]
fn test_uflra_uf_arith_arg_bridge_4915() {
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-fun x () Real)
        (declare-fun f (Real) Real)
        (assert (= x 2.0))
        (assert (= (f 3.0) 10.0))
        (assert (not (= (f (+ x 1.0)) 10.0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}
/// Regression test for #6242: unit theory lemma at non-zero decision level
/// must not cause false UNSAT.
///
/// This exercises the LRA theory propagation path where:
/// 1. A disjunction forces the SAT solver to make decisions (level > 0)
/// 2. One branch leads to a theory-detected infeasibility (tight bounds)
/// 3. The LRA theory emits a conflict lemma (potentially unit)
/// 4. The solver must correctly backtrack to the other branch (SAT)
///
/// Before the fix (commits 65e1eae78, 812df31e8), a unit theory lemma at
/// level > 0 could be used as a reason clause in conflict analysis. Since
/// unit clauses lack a watch[1] literal, this corrupted the learned clause
/// and could produce false UNSAT.
#[test]
fn test_executor_qf_lra_unit_theory_lemma_backtrack_sat_6242() {
    // Two branches via disjunction:
    //   Branch A: x >= 5 AND y >= 6 AND x + y <= 10  (UNSAT: 5+6=11 > 10)
    //   Branch B: x <= 2 AND y <= 3                   (SAT: e.g., x=1, y=2)
    //
    // The solver decides which branch to try first. When it tries branch A,
    // the LRA theory detects infeasibility via bound propagation. This may
    // produce a unit theory lemma. The solver must backtrack to branch B.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const b Bool)
        (assert (or b (not b)))
        (assert (=> b (and (>= x 5.0) (>= y 6.0) (<= (+ x y) 10.0))))
        (assert (=> (not b) (and (<= x 2.0) (<= y 3.0))))
        (assert (>= x 0.0))
        (assert (>= y 0.0))
        (check-sat)
    "#;
    // Branch A is UNSAT (infeasible bounds), branch B is SAT.
    // Overall result must be SAT (b = false, x ∈ [0,2], y ∈ [0,3]).

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "#6242 regression: theory conflict on one disjunction branch must not cause false UNSAT"
    );
}
/// Regression test for #6242 variant: multiple overlapping theory conflicts.
///
/// A 3-way disjunction where two branches are UNSAT (theory conflicts) and
/// one is SAT. The solver may encounter multiple unit theory lemmas across
/// different decision levels before finding the SAT branch.
#[test]
fn test_executor_qf_lra_multi_branch_theory_conflict_sat_6242() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (or a b (and (not a) (not b))))
        (assert (=> a (and (>= x 10.0) (<= x 5.0))))
        (assert (=> b (and (>= y 10.0) (<= y 5.0))))
        (assert (=> (and (not a) (not b)) (and (>= x 1.0) (<= x 2.0) (>= y 1.0) (<= y 2.0))))
        (check-sat)
    "#;
    // Branch a: x >= 10 AND x <= 5 (UNSAT)
    // Branch b: y >= 10 AND y <= 5 (UNSAT)
    // Branch (not a, not b): x ∈ [1,2], y ∈ [1,2] (SAT)

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "#6242 regression: multiple theory conflicts must not poison subsequent branches"
    );
}
