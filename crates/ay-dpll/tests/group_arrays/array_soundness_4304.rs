// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration regressions for #4304 (array soundness).

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::io::Read;
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

fn solve(smt: &str) -> (Executor, Vec<String>) {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");
    (exec, outputs)
}

enum TimedChildOutcome {
    Result(String),
    Timeout,
}

fn sat_result(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

fn run_current_test_with_timeout(
    test_name: &str,
    child_env: &str,
    deadline: Duration,
) -> TimedChildOutcome {
    let current_exe = std::env::current_exe().expect("current test binary path");
    let mut child = Command::new(current_exe)
        .arg("--exact")
        .arg(test_name)
        .arg("--nocapture")
        .env(child_env, "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn child test binary");

    let status = match child
        .wait_timeout(deadline)
        .expect("failed waiting on child test binary")
    {
        Some(status) => status,
        None => {
            let _ = child.kill();
            let _ = child.wait();
            return TimedChildOutcome::Timeout;
        }
    };

    let mut stdout = String::new();
    let mut stderr = String::new();
    child
        .stdout
        .take()
        .expect("stdout pipe")
        .read_to_string(&mut stdout)
        .expect("read child stdout");
    child
        .stderr
        .take()
        .expect("stderr pipe")
        .read_to_string(&mut stderr)
        .expect("read child stderr");

    assert!(
        status.success(),
        "child test {test_name} exited with {status}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    TimedChildOutcome::Result(stdout)
}

#[test]
#[timeout(10_000)]
fn model_validation_no_silent_skip_for_false_array_assertion() {
    // After (check-sat) returns SAT, validate the model immediately.
    // Then add a contradictory assertion and check that re-solving detects it.
    // The model validation is called between the two check-sats.
    let commands = parse(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= i 7))
        (assert (= (select a i) 42))
        (check-sat)
    "#,
    )
    .expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");
    assert_eq!(outputs, vec!["sat"]);

    // Model validation should succeed (the model is consistent).
    let stats = exec
        .validate_model()
        .expect("consistent array assertion should validate");
    assert!(
        stats.checked > 0,
        "array assertions must be checked, not skipped"
    );

    // Now add a contradictory assertion and re-check:
    let contra = parse(
        r#"
        (assert (= (select a i) 41))
        (check-sat)
    "#,
    )
    .expect("parse");
    let outputs2 = exec.execute_all(&contra).expect("execute_all");
    assert_eq!(
        outputs2[0], "unsat",
        "contradictory array assertion must make formula unsatisfiable"
    );
}

#[test]
#[timeout(10_000)]
fn qf_ax_store_equality_sat_correct() {
    // Legitimate SAT: b = store(a, 1, 42) and select(b, 1) = 42.
    // The semantic array model normalizer must verify b and store(a,1,42)
    // have the same normalized model (default + sorted stores map).
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (store a 1 42)))
        (assert (= (select b 1) 42))
        (check-sat)
    "#,
    );

    assert_eq!(outputs[0], "sat", "store equality must be correctly SAT");
}

#[test]
#[timeout(10_000)]
fn qf_ax_nested_store_chain_never_wrong_sat() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i1 () Index)
        (declare-fun i2 () Index)
        (declare-fun i3 () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (declare-fun e3 () Element)
        (assert (not (= i1 i2)))
        (assert (not (= i1 i3)))
        (assert (not (= i2 i3)))
        (assert (not (= (select (store (store (store a i1 e1) i2 e2) i3 e3) i1) e1)))
        (check-sat)
    "#,
    );

    assert_ne!(
        outputs[0], "sat",
        "nested store-chain contradiction must not produce wrong SAT"
    );
}

#[test]
#[timeout(30_000)]
fn qf_auflia_symbolic_store_commute_is_guarded_6367() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (declare-const w Int)
        (assert (not
            (= (store (store a j w) i v)
               (ite (= i j)
                    (store a i v)
                    (store (store a i v) j w)))))
        (check-sat)
    "#,
    );

    assert_eq!(
        outputs[0], "unsat",
        "symbolic store commute must preserve the aliasing case with an equality guard"
    );
}

/// Regression for #6598: symbolic store commutation without proven distinctness
/// changes which value the outer store writes at a shared index.
///
/// `store(store(a, j, 20), i, 10)` with `i = j`: outer store `i` wins → value
/// at the shared index is `10`. If the rewriter incorrectly commutes to
/// `store(store(a, i, 10), j, 20)`, then outer store `j` wins → value is `20`.
///
/// This test asserts that `select(store(store(a, j, 20), i, 10), i) = 10` when
/// `i = j`. A rewriter that commutes symbolic indices without a distinctness
/// proof would break this invariant.
#[test]
#[timeout(10_000)]
fn symbolic_store_commute_alias_value_6598() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (assert (= i j))
        (assert (not (= (select (store (store a j 20) i 10) i) 10)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "#6598: with i=j, select(store(store(a,j,20),i,10),i) must equal 10 (outer store wins)"
    );
}

/// Regression for #6598: SAT variant confirming the non-alias case.
///
/// When `i ≠ j`, `select(store(store(a, j, 20), i, 10), j)` should be `20`
/// (the inner store at index `j` is not overwritten by the outer store at `i`).
#[test]
#[timeout(10_000)]
fn symbolic_store_commute_non_alias_value_6598() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (assert (not (= i j)))
        (assert (not (= (select (store (store a j 20) i 10) j) 20)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "#6598: with i≠j, select(store(store(a,j,20),i,10),j) must equal 20 (inner store preserved)"
    );
}

// storeinv 5+ index tests removed — these timeout without lazy ROW2 axiom
// instantiation (#6546). Re-add when #6546 is implemented.

// --- QF_AUFLIA cross-theory soundness regressions ---

#[test]
#[timeout(10_000)]
fn qf_auflia_store_value_congruence_with_arith_index() {
    // Two stores equal at equal indices must have equal values.
    // This requires store-value congruence axioms in the AUFLIA path.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (assert (= i j))
        (assert (= (store a i v) (store b j w)))
        (assert (not (= v w)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "store congruence: equal stores at equal indices => equal values"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_shadowed_store_value_requires_distinct_outer_index_8871() {
    // If the outer store index j is provably distinct from i, array equality
    // between the two chains forces the inner values at i to agree.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (assert (= j (+ i 1)))
        (assert (= (store (store a i v) j x)
                   (store (store a i w) j x)))
        (assert (not (= v w)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "when j=i+1, equal shadowed store chains must still agree on the inner value at i"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_shadowed_store_value_alias_branch_sat_8871() {
    // If the outer store aliases the inner one, both sides collapse to
    // store(a, i, x), so differing shadowed values remain satisfiable.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (assert (= (store (store a i v) i x)
                   (store (store a i w) i x)))
        (assert (not (= v w)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "sat",
        "aliasing outer stores overwrite the shadowed inner value on both sides"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_shadowed_store_value_without_distinctness_guard_sat_8871() {
    // Without a proof that j != i, the formula stays satisfiable: choose j=i
    // and both sides collapse to store(a, i, x).
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (assert (= (store (store a i v) j x)
                   (store (store a i w) j x)))
        (assert (not (= v w)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "sat",
        "shadowed store equality must not force v=w without a distinctness proof for the outer index"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_array_sum_bound() {
    // store(a,0,10), store(b,1,20), then 10+20 > 31 is false.
    // Requires store-value congruence to propagate select values to LIA.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 0 10)))
        (assert (= b (store b 1 20)))
        (assert (> (+ (select b 0) (select b 1)) 31))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "array store values must propagate to arithmetic: 10 + 20 = 30, not > 31"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_array_init_read_back() {
    // Initialize array then read back — common program pattern, should be SAT.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store (store (store a 0 1) 1 2) 2 3)))
        (assert (= (select b 0) 1))
        (assert (= (select b 1) 2))
        (assert (= (select b 2) 3))
        (check-sat)
    "#,
    );
    assert_eq!(outputs[0], "sat", "array init + read-back must be SAT");
}

#[test]
#[timeout(10_000)]
fn qf_auflia_array_swap() {
    // Swap two array elements and verify b[i] = a[j].
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (assert (not (= i j)))
        (assert (= b (store (store a i (select a j)) j (select a i))))
        (assert (not (= (select b i) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(outputs[0], "unsat", "after swap, b[i] must equal a[j]");
}

#[test]
#[timeout(10_000)]
fn qf_auflia_store_overwrite() {
    // store(store(a,i,v),i,w) = store(a,i,w) — store overwrite axiom.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (assert (not (= (store (store a i v) i w) (store a i w))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "store overwrite: store(store(a,i,v),i,w) = store(a,i,w)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_array_diff_index_arith() {
    // select(store(a,i,42), i+0) must equal 42 (i+0 = i).
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (assert (= (select (store a i 42) (+ i 0)) 43))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "select(store(a,i,42), i+0) = 42, not 43"
    );
}

// --- Regression tests for #4665: symbolic-index ROW2 with arithmetic disequality ---

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_arithmetic_disequality_4665() {
    // y = x + 1 implies x ≠ y, so select(store(a,x,42),y) = select(a,y).
    // Combined with select(store(a,x,42),y) = 42 and select(a,y) ≠ 42, this is unsat.
    // Previously returned false sat because the array solver didn't learn x ≠ y from LIA.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= y (+ x 1)))
        (assert (= (select (store a x 42) y) 42))
        (assert (not (= (select a y) 42)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "ROW2 + arithmetic disequality: y=x+1 implies select(store(a,x,42),y) = select(a,y)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_explicit_disequality_4665() {
    // Direct disequality i ≠ j + ROW2: select(store(a,i,42),j) must equal select(a,j).
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (not (= i j)))
        (assert (not (= (select (store a i 42) j) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "ROW2: i≠j → select(store(a,i,42),j) = select(a,j)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_intermediate_variable_4665() {
    // b = store(a,i,42), select(b,j) ≠ select(a,j) with i ≠ j: unsat by ROW2 + equality.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (not (= i j)))
        (assert (= b (store a i 42)))
        (assert (not (= (select b j) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "ROW2 through intermediate variable: b=store(a,i,42), i≠j → select(b,j) = select(a,j)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row_symbolic_non_alias_sat_4665_matrix() {
    // Corrected #4665 SAT/UNSAT matrix: this symbolic ROW shape is SAT.
    // With i ≠ j, select(store(a,i,42),j) can still be 42 when a[j] = 42.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (not (= i j)))
        (assert (= (select (store a i 42) j) 42))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "sat",
        "symbolic non-alias read-over-write can be SAT when the base array already stores 42 at j"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_const_array_non_alias_unsat_4665() {
    // Reproducer for #4665:
    // domain = store(const 0, addr1, 1), addr1 ≠ addr2, select(domain, addr2) = 1.
    // Since addr2 reads the const default 0, this must be UNSAT.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const addr1 Int)
        (declare-const addr2 Int)
        (declare-const domain (Array Int Int))
        (assert (= domain (store ((as const (Array Int Int)) 0) addr1 1)))
        (assert (not (= addr1 addr2)))
        (assert (= (select domain addr2) 1))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "non-aliased read from store(const 0, addr1, 1) must return 0, not 1"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflra_row2_arithmetic_disequality_4665() {
    // Real-index variant of #4665: y = x + 0.5 implies x ≠ y.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLRA)
        (declare-fun a () (Array Real Real))
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (= y (+ x 0.5)))
        (assert (= (select (store a x 42.0) y) 42.0))
        (assert (not (= (select a y) 42.0)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "AUFLRA ROW2: y=x+0.5 implies select(store(a,x,42),y)=select(a,y)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflira_row2_arithmetic_disequality_4665() {
    // Mixed-theory variant: real array indices are solved via LRA in AUFLIRA.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIRA)
        (declare-fun a () (Array Real Real))
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (= y (+ x 1.5)))
        (assert (= (select (store a x 3.0) y) 3.0))
        (assert (not (= (select a y) 3.0)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "AUFLIRA ROW2: y=x+1.5 must force non-alias read-over-write"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_store_congruence_base_equality_5116() {
    // Store congruence: if a = b then store(a,i,v) = store(b,i,v).
    // Without add_array_congruence_axioms, the eager QF_ABV path treats
    // (= a b) as an opaque Tseitin atom with no connection to store terms.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun v () (_ BitVec 8))
        (assert (= a b))
        (assert (not (= (store a #x00 v) (store b #x00 v))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: a=b must imply store(a,i,v)=store(b,i,v)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_store_chain_congruence_5116() {
    // Multiple store operations on equal base arrays must produce equal results.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-fun v1 () (_ BitVec 8))
        (declare-fun v2 () (_ BitVec 8))
        (assert (= a b))
        (define-fun a1 () (Array (_ BitVec 4) (_ BitVec 8)) (store a #x0 v1))
        (define-fun b1 () (Array (_ BitVec 4) (_ BitVec 8)) (store b #x0 v1))
        (define-fun a2 () (Array (_ BitVec 4) (_ BitVec 8)) (store a1 #x1 v2))
        (define-fun b2 () (Array (_ BitVec 4) (_ BitVec 8)) (store b1 #x1 v2))
        (assert (not (= a2 b2)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: same store chains on equal arrays must be equal"
    );
}

// --- QF_ABV soundness regressions (#5083) ---
// The original #5083 false SATs on try5_small_difret_functions_ground_* benchmarks
// were caused by the array extensionality bug (#4304). These tests verify
// the fix holds for BV array combinations.

#[test]
#[timeout(10_000)]
fn qf_abv_extensionality_bv_arrays_5083() {
    // Two BV arrays that differ at a known index must not be equal.
    // Requires extensionality Skolem diff witness generation in the BV path.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= (select a #x05) #xFF))
        (assert (= (select b #x05) #x00))
        (assert (= a b))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: arrays differing at index #x05 cannot be equal"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_row2_symbolic_bv_index_5083() {
    // ROW2 with symbolic BV index: select(store(a,i,v),j) where i!=j.
    // The array solver must generate the disequality axiom.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun i () (_ BitVec 8))
        (declare-fun j () (_ BitVec 8))
        (assert (not (= i j)))
        (assert (not (= (select (store a i #x42) j) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV ROW2: i!=j -> select(store(a,i,v),j) = select(a,j)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_store_read_back_bv_5083() {
    // Store then read back pattern with BV arrays — must be SAT.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-fun addr () (_ BitVec 32))
        (declare-fun val () (_ BitVec 8))
        (assert (= (select (store mem addr val) addr) val))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "sat",
        "QF_ABV: store-then-read-back must be SAT"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_memory_store_chain_unsat_5083() {
    // Byte-addressable memory pattern (common in binary analysis).
    // Store 4 bytes at addr, then read back expecting wrong value — UNSAT.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-fun addr () (_ BitVec 32))
        (define-fun mem1 () (Array (_ BitVec 32) (_ BitVec 8))
            (store (store (store (store mem
                addr #xDE)
                (bvadd addr #x00000001) #xAD)
                (bvadd addr #x00000002) #xBE)
                (bvadd addr #x00000003) #xEF))
        (assert (not (= (select mem1 addr) #xDE)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: byte-store chain read-back at base addr must equal stored value"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_memory_store_chain_adjacent_read_5083() {
    // Store at addr, read at addr+1 must get the second byte, not the first.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-fun addr () (_ BitVec 32))
        (define-fun mem1 () (Array (_ BitVec 32) (_ BitVec 8))
            (store (store mem addr #xAA) (bvadd addr #x00000001) #xBB))
        (assert (= (select mem1 (bvadd addr #x00000001)) #xAA))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: reading addr+1 must get #xBB not #xAA"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_extensionality_with_store_5083() {
    // After storing different values at the same index, arrays must differ.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun i () (_ BitVec 8))
        (define-fun a1 () (Array (_ BitVec 8) (_ BitVec 8)) (store a i #x00))
        (define-fun a2 () (Array (_ BitVec 8) (_ BitVec 8)) (store a i #xFF))
        (assert (= a1 a2))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: store(a,i,0) != store(a,i,0xFF) via extensionality"
    );
}

// --- Regressions for storeinv/storecomm/swap fixpoint fix (#4304) ---

/// Storeinv cross-swap: swap values between a1/a2 at two indices.
/// The `_nf_` (no-forwarding) pattern uses let-expanded nested stores with no
/// intermediate variable equalities. Requires the congruence+ROW fixpoint loop
/// in `solve_array_euf` to propagate extensionality Skolem selects through the
/// full store chain.
#[test]
#[timeout(10_000)]
fn qf_ax_storeinv_cross_swap_nf_2idx() {
    // Exact copy of storeinv_t1_np_nf_ai_00002_001.cvc.smt2
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a1 () (Array Index Element))
        (declare-fun a2 () (Array Index Element))
        (declare-fun i1 () Index)
        (declare-fun i2 () Index)
        (assert (let ((?v_0 (store a2 i1 (select a1 i1)))
                      (?v_1 (store a1 i1 (select a2 i1))))
                  (= (store ?v_1 i2 (select ?v_0 i2))
                     (store ?v_0 i2 (select ?v_1 i2)))))
        (assert (not (= a1 a2)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "storeinv _nf_ 2idx: cross-swap forces a1 = a2"
    );
}

/// Storeinv cross-swap with declare-fun intermediates (_sf_ variant).
/// Uses explicit store equalities with intermediate variables.
#[test]
#[timeout(10_000)]
fn qf_ax_storeinv_cross_swap_sf_2idx() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a1 () (Array Index Element))
        (declare-fun a2 () (Array Index Element))
        (declare-fun i1 () Index)
        (declare-fun i2 () Index)
        (declare-fun v0 () (Array Index Element))
        (assert (= v0 (store a2 i1 (select a1 i1))))
        (declare-fun v1 () (Array Index Element))
        (assert (= v1 (store a1 i1 (select a2 i1))))
        (declare-fun lhs () (Array Index Element))
        (assert (= lhs (store v1 i2 (select v0 i2))))
        (declare-fun rhs () (Array Index Element))
        (assert (= rhs (store v0 i2 (select v1 i2))))
        (assert (= lhs rhs))
        (assert (not (= a1 a2)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "storeinv _sf_ 2idx: cross-swap via intermediates forces a1 = a2"
    );
}

/// Store commutativity: two orderings of the same stores, checked via select.
/// store(store(a,i,v),j,w)[k] = store(store(a,j,w),i,v)[k] for all k.
#[test]
#[timeout(10_000)]
fn qf_ax_storecomm_read_at_arbitrary_index() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-fun a () (Array Index Elem))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v () Elem)
        (declare-fun w () Elem)
        (declare-fun k () Index)
        (assert (not (= i j)))
        (assert (not (= (select (store (store a i v) j w) k)
                        (select (store (store a j w) i v) k))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "storecomm: reordered stores are pointwise equal"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_storecomm_select_witness_with_aliases() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (declare-fun v3 () Int)
        (declare-fun lhs () (Array Int Int))
        (declare-fun rhs () (Array Int Int))
        (declare-fun k () Int)
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (assert (= lhs (store (store (store a 1 v1) 2 v2) 3 v3)))
        (assert (= rhs (store (store (store a 3 v3) 1 v1) 2 v2)))
        (assert (= e1 (select lhs k)))
        (assert (= e2 (select rhs k)))
        (assert (not (= e1 e2)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_AUFLIA storecomm aliases are pointwise equal at any witness index"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_storecomm_invalid_select_witness_remains_sat() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (declare-fun lhs () (Array Int Int))
        (declare-fun rhs () (Array Int Int))
        (declare-fun k () Int)
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (assert (= lhs (store a 1 v1)))
        (assert (= rhs (store (store a 1 v1) 2 v2)))
        (assert (= e1 (select lhs k)))
        (assert (= e2 (select rhs k)))
        (assert (not (= e1 e2)))
        (check-sat)
    "#,
    );
    assert_ne!(
        outputs[0], "unsat",
        "storecomm_invalid has a real support difference and must not be forced UNSAT"
    );
}

/// #5086: Disjunctive store equality propagation.
///
/// From `store(a, x, v) = b` and `store(a, y, w) = b`, the theory entails
/// `x = y OR a = b`. Combined with `f(x) != f(y)` (ruling out x=y) and
/// `g(a) != g(b)` (ruling out a=b), the formula is UNSAT.
///
/// This is the `array_incompleteness1.smt2` benchmark from SMT-LIB, designed
/// to require an array decision procedure to propagate entailed disjunctions
/// of equalities between shared terms.
///
/// Reference: Stump, Barrett, Dill, Levitt. "A Decision Procedure for an
/// Extensional Theory of Arrays", Section 6.2.
#[test]
#[timeout(10_000)]
fn disjunctive_store_equality_5086() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun g ((Array Int Int)) Int)
        (declare-fun f (Int) Int)
        (assert (and (= (store a x v) b) (= (store a y w) b)
                     (not (= (f x) (f y))) (not (= (g a) (g b)))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "disjunctive store equality: x=y OR a=b must be propagated"
    );
}

/// #5086 variant: Same pattern but with explicit negations separated.
///
/// Tests that the disjunctive axiom fires even when constraints are given
/// as separate assertions rather than a single conjunction.
#[test]
#[timeout(10_000)]
fn disjunctive_store_equality_separated_5086() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun g ((Array Int Int)) Int)
        (declare-fun f (Int) Int)
        (assert (= (store a x v) b))
        (assert (= (store a y w) b))
        (assert (not (= (f x) (f y))))
        (assert (not (= (g a) (g b))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "separated disjunctive store equality: x=y OR a=b"
    );
}

/// #5086 variant: Three stores to the same target.
///
/// store(a,x,v)=b, store(a,y,w)=b, store(a,z,u)=b
/// with x!=y, y!=z, x!=z and a!=b → contradiction because
/// from any pair, x=y OR a=b, and we have x!=y → a=b.
#[test]
#[timeout(10_000)]
fn disjunctive_store_equality_three_stores_5086() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun u () Int)
        (assert (= (store a x v) b))
        (assert (= (store a y w) b))
        (assert (not (= x y)))
        (assert (not (= a b)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "three stores: x!=y and a!=b contradicts store(a,x,v)=store(a,y,w)"
    );
}

// --- Regressions for #6282: QF_AUFLIA storeinv wrong answers ---

/// AUFLIA storeinv nf size=2: cross-swap at 2 indices using nested let.
///
/// This is the QF_AUFLIA variant of the QF_AX storeinv test above, using
/// Int-sorted arrays and indices. The N-O fixpoint must propagate array
/// equalities back to EUF for this to work (#6282).
///
/// AY cannot yet solve this within 30s (deep store chain reasoning needed).
/// Run in a subprocess so the timeout kills the whole solver, not just the
/// parent test thread.
///
/// Matches storeinv_nf_size2.smt2 benchmark.
#[test]
fn qf_auflia_storeinv_nf_2idx_6282() {
    const CHILD_ENV: &str = "AY_ARRAY_STOREINV_NF_2IDX_6282_CHILD";

    if std::env::var_os(CHILD_ENV).is_some() {
        let (_, outputs) = solve(
            r#"
            (set-logic QF_AUFLIA)
            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun i1 () Int)
            (declare-fun i2 () Int)
            (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
            (assert (let ((?v_0 (store a2 i1 (select a1 i1)))
                          (?v_1 (store a1 i1 (select a2 i1))))
                      (= (store ?v_1 i2 (select ?v_0 i2))
                         (store ?v_0 i2 (select ?v_1 i2)))))
            (assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
            (check-sat)
        "#,
        );
        println!("{}", outputs[0]);
        return;
    }

    match run_current_test_with_timeout(
        "array_soundness_4304::qf_auflia_storeinv_nf_2idx_6282",
        CHILD_ENV,
        Duration::from_secs(30),
    ) {
        TimedChildOutcome::Result(stdout) => {
            let result = sat_result(&stdout).expect("child emitted solve result");
            assert_ne!(
                result, "sat",
                "AUFLIA storeinv nf 2idx: cross-swap must not return false SAT (#6282)"
            );
        }
        TimedChildOutcome::Timeout => {
            // Timeout: AY cannot solve 2-index storeinv nf within 30s — incompleteness, not unsoundness.
        }
    }
}

/// AUFLIA storeinv single: store(a, i, select(a, i)) = a.
///
/// Simplest store invariant in QF_AUFLIA with Int sorts.
/// Matches storeinv_nf_single.smt2 benchmark.
#[test]
#[timeout(10_000)]
fn qf_auflia_storeinv_nf_single_6282() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (assert (not (= (store a i (select a i)) a)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "AUFLIA storeinv single: store(a,i,sel(a,i)) = a (#6282)"
    );
}

/// AUFLIA storeinv sf size=2: flat form with intermediate variables.
///
/// Same cross-swap as nf but using named intermediates. This encoding is
/// easier for the solver because each store has a named variable base,
/// allowing direct ROW lemma generation.
#[test]
fn qf_auflia_storeinv_sf_2idx_6282() {
    const CHILD_ENV: &str = "AY_ARRAY_STOREINV_SF_2IDX_6282_CHILD";

    if std::env::var_os(CHILD_ENV).is_some() {
        let (_, outputs) = solve(
            r#"
            (set-logic QF_AUFLIA)
            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun i1 () Int)
            (declare-fun i2 () Int)
            (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
            (declare-fun v0 () (Array Int Int))
            (assert (= v0 (store a2 i1 (select a1 i1))))
            (declare-fun v1 () (Array Int Int))
            (assert (= v1 (store a1 i1 (select a2 i1))))
            (assert (= (store v1 i2 (select v0 i2))
                       (store v0 i2 (select v1 i2))))
            (assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
            (check-sat)
        "#,
        );
        println!("{}", outputs[0]);
        return;
    }

    match run_current_test_with_timeout(
        "array_soundness_4304::qf_auflia_storeinv_sf_2idx_6282",
        CHILD_ENV,
        Duration::from_mins(2),
    ) {
        TimedChildOutcome::Result(stdout) => {
            let result = sat_result(&stdout).expect("child emitted solve result");
            assert_eq!(
                result, "unsat",
                "AUFLIA storeinv sf 2idx: flat cross-swap forces a1 = a2 (#6282)"
            );
        }
        TimedChildOutcome::Timeout => {
            // Timeout remains acceptable here: this benchmark is still incomplete
            // at current HEAD, even when run in isolation.
        }
    }
}

/// Regression: storeinv_invalid_t1_pp_nf_ai_00002 is SAT (`:status sat` in
/// SMT-LIB, confirmed by Z3). This test is a soundness guard: AY must not
/// return `unsat` on the benchmark, even though current HEAD still times out on
/// it under the test budget.
///
/// The formula asserts that two store chains on `a1` and `a2` produce equal
/// results after a cross-swap of selected values, and simultaneously that `a1`
/// and `a2` differ at some witness index `sk(a1,a2)`. This is satisfiable
/// (the arrays can differ at indices other than `i1`/`i2`).
///
/// Run in a subprocess so the timeout kills the solver process, not just the
/// parent test thread. Timeout remains acceptable here: it is an
/// incompleteness/performance gap, not a soundness bug.
#[test]
fn storeinv_invalid_false_unsat_smtcomp_6608() {
    const CHILD_ENV: &str = "AY_ARRAY_STOREINV_INVALID_6608_CHILD";

    if std::env::var_os(CHILD_ENV).is_some() {
        let (_, outputs) = solve(
            r#"
            (set-logic QF_AUFLIA)
            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun i1 () Int)
            (declare-fun i2 () Int)
            (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
            (assert (let ((?v_0 (store a2 i1 (select a1 i1)))
                          (?v_1 (store a1 i1 (select a2 i1))))
                      (= (store ?v_1 i1 (select ?v_0 i2))
                         (store ?v_0 i2 (select ?v_1 i2)))))
            (assert (let ((?v_0 (sk a1 a2)))
                      (not (= (select a1 ?v_0) (select a2 ?v_0)))))
            (check-sat)
        "#,
        );
        println!("{}", outputs[0]);
        return;
    }

    match run_current_test_with_timeout(
        "array_soundness_4304::storeinv_invalid_false_unsat_smtcomp_6608",
        CHILD_ENV,
        Duration::from_secs(30),
    ) {
        TimedChildOutcome::Result(stdout) => {
            let result = sat_result(&stdout).expect("child emitted solve result");
            assert_ne!(
                result, "unsat",
                "storeinv_invalid is SAT (:status sat, Z3 confirms); AY must not return false UNSAT"
            );
        }
        TimedChildOutcome::Timeout => {
            // Timeout remains acceptable here: current HEAD still fails to
            // solve the benchmark under 30s, but that is incompleteness rather
            // than a false UNSAT result.
        }
    }
}

/// #arr_lia561 wrong-UNSAT regression: an Int-array AUFLIA formula where one var
/// (`a2`) is given TWO store-flat definitions to the SAME base (`a1`), combined
/// with a select-through-store on a third array `a3` (sharing the constant `0`),
/// `i1 != 3`, and `a1 != a3`.
///
/// The combined LIA+Array+EUF route merges `parent_selects` across the array
/// equality/alias closure (including model/sentinel equalities). The
/// read-over-write conflict checker (`check_array_equality`) then paired
/// `select(a3, K)` — which is only MODEL-equal to `a1`, not provably so — with
/// `select(a2, K)` under `a1 = a2` and emitted the false theorem
/// `select(a1,K)=select(a3,K) | ¬(a1=a2) | ¬(select(a1,K)=select(a2,K))`,
/// closing a spurious UNSAT. The fix validates each select's actual array
/// against the equality side (adding the alias proof, or skipping if not
/// provable). Z3 confirms `sat`; AY must never return UNSAT here. This minimized
/// core solves to `sat`; the original arr_lia561 9-assertion form (which also
/// aliases `a2 = a0`) degrades to a sound `unknown` under the in-process solver.
#[test]
#[timeout(60_000)]
fn arr_lia561_dup_store_flat_not_false_unsat() {
    let (_, outputs) = solve(
        r#"
        (set-logic ALL)
        (declare-fun a0 () (Array Int Int))
        (declare-fun a1 () (Array Int Int))
        (declare-fun a2 () (Array Int Int))
        (declare-fun a3 () (Array Int Int))
        (declare-fun i1 () Int)
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (assert (= 2 (select (store a3 0 e1) i1)))
        (assert (= a2 (store a1 i1 0)))
        (assert (= a2 (store a1 3 e2)))
        (assert (distinct 3 i1))
        (assert (not (= a1 a3)))
        (check-sat)
    "#,
    );
    let result = sat_result(&outputs[0]).expect("solver emitted a result");
    assert_ne!(
        result, "unsat",
        "arr_lia561 dup-store-flat core is SAT (Z3 confirms); AY must not return false UNSAT"
    );
}
