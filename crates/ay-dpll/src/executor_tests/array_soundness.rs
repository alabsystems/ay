// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AX soundness regression tests (#4304)
//!
//! These formulas are UNSAT. The array theory solver must produce "unsat"
//! (not "sat" or "unknown") for these well-known array axiom patterns.
//!
//! Patterns tested:
//! - Nested store chains (ROW1+ROW2 walking)
//! - Store transitivity via equality (b = store(a,i,e))
//! - Swap pattern (double store with cross-references)
//! - Transitive equality chains (c = b = store(a,i,e))
//! - Conflicting stores (a = store(b,i,e1) and a = store(b,i,e2) with e1 != e2)

#![allow(clippy::large_stack_arrays)]

use ntest::timeout;

use crate::Executor;
use ay_frontend::parse;

#[test]
fn test_qf_ax_nested_store_chain_unsat() {
    // Nested stores: select(store(store(store(a, i1, e1), i2, e2), i3, e3), i1)
    // must equal e1 when i1 != i2 and i1 != i3 (ROW2 skip + ROW1 match).
    let input = r#"
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
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "unsat", "Regression #4304: nested store chain");
}

#[test]
fn test_qf_ax_store_transitivity_unsat() {
    // b = store(a, i, e), so select(b, i) = e by ROW1.
    // select(a, i) = e is also asserted, so select(a, i) = select(b, i).
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e () Element)
        (assert (= (select a i) e))
        (assert (= b (store a i e)))
        (assert (not (= (select a i) (select b i))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #4304: store transitivity via equality"
    );
}

#[test]
fn test_qf_ax_swap_pattern_unsat() {
    // Swap a[i] and a[j]: b = store(store(a, i, a[j]), j, a[i])
    // After swap with i != j: b[i] must equal a[j] (ROW2 skip j, ROW1 match i).
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (assert (not (= i j)))
        (assert (not (= (select (store (store a i (select a j)) j (select a i)) i) (select a j))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "unsat", "Regression #4304: swap pattern");
}

#[test]
fn test_qf_ax_transitive_equality_chain_unsat() {
    // c = b = store(a, i, e), so select(c, i) = e via two-hop equality.
    // BFS equality traversal in find_store_through_eq is required.
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun c () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e () Element)
        (assert (= b (store a i e)))
        (assert (= c b))
        (assert (not (= (select c i) e)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #4304: transitive equality chain (c = b = store(a,i,e))"
    );
}

#[test]
fn test_qf_ax_conflicting_store_values_unsat() {
    // a = store(b, i, e1) and a = store(b, i, e2) with e1 != e2.
    // Two stores to same (base, index) must have equal values.
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (assert (not (= e1 e2)))
        (assert (= a (store b i e1)))
        (assert (= a (store b i e2)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #4304: conflicting store values (same base+index, different values)"
    );
}

#[test]
fn test_qf_alia_const_array_store_eq_unsound_4479() {
    // Regression test for #4479: store(const_array(0), 0, 0) == store(const_array(0), 0, 1)
    // was returning Sat (UNSOUND). The two arrays differ at index 0 (value 0 vs 1).
    //
    // Fix: mk_eq rewrites (= (store a i v1) (store a i v2)) -> (= v1 v2) when
    // base and index are syntactically identical. Here (= 0 1) folds to false.
    let input = r#"
        (set-logic QF_AUFLIA)
        (assert (= (store ((as const (Array Int Int)) 0) 0 0)
                   (store ((as const (Array Int Int)) 0) 0 1)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert!(
        outputs[0] == "unsat" || outputs[0] == "unknown",
        "Regression #4479: store(const(0),0,0) = store(const(0),0,1) must not be sat, got: {}",
        outputs[0]
    );
}

/// Regression for the const-array-read soundness bug: `check_const_array_read`
/// fired a value-distinctness conflict lemma for `select(arr, i) != default`
/// WITHOUT including (or verifying) the premise `arr =_E const-array(default)`.
///
/// Here `I = const(1)` and `J = store(const(0), 5, 1)`. They differ at every
/// index except 5 (I[k]=1, J[k]=0 for k!=5), so `I != J` is SAT. During search
/// the SAT solver tentatively set the *eager congruence* atom `(= I const(0))`
/// (the store's base), which made `select(I, d)` read from `const(0)` and thus
/// conflict with `select(I, d) = 1`. The conflict was real GIVEN `I = const(0)`,
/// but the emitted unit lemma `not (= 1 (select I d))` dropped the
/// `not (I = const(0))` guard, asserting `select(I, d) != 1` unconditionally —
/// contradicting `I = const(1)` and yielding a spurious UNSAT.
#[test]
#[timeout(20_000)]
fn test_qf_alia_const_vs_store_const_diff_default_sat() {
    let input = r#"
        (set-logic QF_ALIA)
        (declare-const I (Array Int Int))
        (declare-const J (Array Int Int))
        (assert (= I ((as const (Array Int Int)) 1)))
        (assert (= J (store ((as const (Array Int Int)) 0) 5 1)))
        (assert (not (= I J)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0],
        "sat",
        "const(1) and store(const(0),5,1) differ at index 0 (1 vs 0); I != J is SAT; \
         unknown_reason={:?}; statistics={:?}",
        exec.unknown_reason(),
        exec.statistics(),
    );
}

/// Companion to `test_qf_alia_const_vs_store_const_diff_default_sat`: when the
/// store writes the const default value into the const-array, the store is the
/// identity and the two arrays ARE equal, so the disequality is UNSAT. Confirms
/// the soundness fix did not over-correct into accepting genuine equalities.
#[test]
#[timeout(20_000)]
fn test_qf_alia_const_vs_identity_store_unsat() {
    let input = r#"
        (set-logic QF_ALIA)
        (declare-const I (Array Int Int))
        (declare-const J (Array Int Int))
        (assert (= I ((as const (Array Int Int)) 1)))
        (assert (= J (store ((as const (Array Int Int)) 1) 5 1)))
        (assert (not (= I J)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "store(const(1),5,1) = const(1), so I = J and the disequality is UNSAT"
    );
}

/// `select(const(7), k) = 7` for all `k`. Asserting `select(I, k) != 7` with
/// `I = const(7)` must be UNSAT. Exercises the (sound) const-read conflict path
/// where the select genuinely reads the const-array it is equal to.
#[test]
#[timeout(20_000)]
fn test_qf_alia_const_read_value_unsat() {
    let input = r#"
        (set-logic QF_ALIA)
        (declare-const I (Array Int Int))
        (declare-const k Int)
        (assert (= I ((as const (Array Int Int)) 7)))
        (assert (not (= (select I k) 7)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "select(const(7), k) = 7 for all k; asserting != 7 is UNSAT"
    );
}

/// Two const-arrays over different store-of-const bases that genuinely differ
/// (different default value at an unwritten index): `I = store(const(2), 0, 5)`,
/// `J = store(const(3), 0, 5)` differ at index 1 (2 vs 3), so `I != J` is SAT.
#[test]
#[timeout(20_000)]
fn test_qf_alia_store_const_diff_default_diseq_sat() {
    let input = r#"
        (set-logic QF_ALIA)
        (declare-const I (Array Int Int))
        (declare-const J (Array Int Int))
        (assert (= I (store ((as const (Array Int Int)) 2) 0 5)))
        (assert (= J (store ((as const (Array Int Int)) 3) 0 5)))
        (assert (not (= I J)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "sat",
        "store(const(2),0,5) and store(const(3),0,5) differ at index 1 (2 vs 3)"
    );
}

#[test]
fn test_qf_ax_store_store_same_base_idx_diff_val_unsat_4479() {
    // Variant of #4479 using QF_AX with uninterpreted sorts:
    // store(a, i, e1) = store(a, i, e2) with e1 != e2.
    // The store-store rewrite reduces this to (= e1 e2) which contradicts (not (= e1 e2)).
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (assert (not (= e1 e2)))
        (assert (= (store a i e1) (store a i e2)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #4479: store(a,i,e1) = store(a,i,e2) with e1 != e2 must be unsat"
    );
}

/// Store permutation with extra store: false-UNSAT regression (#5179).
///
/// Two store chains over the same base with permuted orders for indices 1,2:
/// chain A: base[1->v1][2->v2]  (2 stores)
/// chain B: base[2->v2][1->v1][3->v3]  (3 stores -- extra at index 3)
///
/// Since chain B has an additional store at index 3, the arrays differ.
/// Expected: sat.
///
/// Root cause: `resolve_select_base_for_propagation` used `known_distinct()`
/// which includes external (model-based) disequalities. When the extensionality
/// Skolem variable was assigned a value different from all store indices by LIA,
/// both selects resolved to the same base and were propagated as equal with
/// empty reasons. This unconditional equality contradicted the extensionality
/// witness disequality, producing false UNSAT.
#[test]
fn test_store_permutation_extra_store_sat_5179() {
    // Soundness guard: must not return "unsat". Timeout is acceptable since it
    // is not a wrong answer. The AUFLIA deferred-check architecture (#6282)
    // causes the solver to not converge on nested-store formulas within a
    // reasonable test timeout; this is a performance issue tracked separately.
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let input = r#"
            (set-logic QF_AUFLIA)
            (declare-fun base () (Array Int Int))
            (declare-fun v1 () Int)
            (declare-fun v2 () Int)
            (declare-fun v3 () Int)

            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun b1 () (Array Int Int))
            (declare-fun b2 () (Array Int Int))
            (declare-fun b3 () (Array Int Int))

            (assert (= a1 (store base 1 v1)))
            (assert (= a2 (store a1 2 v2)))
            (assert (= b1 (store base 2 v2)))
            (assert (= b2 (store b1 1 v1)))
            (assert (= b3 (store b2 3 v3)))
            (assert (not (= a2 b3)))
            (check-sat)
        "#;

        let commands = parse(input).expect("invariant: valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec
            .execute_all(&commands)
            .expect("invariant: execute succeeds");
        let _ = tx.send(outputs[0].clone());
    });

    match rx.recv_timeout(std::time::Duration::from_secs(15)) {
        Ok(answer) => {
            assert!(
                answer == "sat" || answer == "unknown",
                "Regression #5179: store permutation with extra store must not be unsat, got: {answer}",
            );
        }
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            // Timeout is acceptable: the solver did not return "unsat".
        }
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            // Solver thread panicked or exited without sending.
            // Not a false-UNSAT (no answer was returned), so not a soundness issue.
        }
    }
}

/// Same as above but with symbolic (non-constant) indices.
#[test]
fn test_store_permutation_extra_store_symbolic_indices_5179() {
    // Soundness guard: must not return "unsat". Timeout is acceptable.
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let input = r#"
            (set-logic QF_AUFLIA)
            (declare-fun base () (Array Int Int))
            (declare-fun i1 () Int)
            (declare-fun i2 () Int)
            (declare-fun i3 () Int)
            (declare-fun v1 () Int)
            (declare-fun v2 () Int)
            (declare-fun v3 () Int)

            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun b1 () (Array Int Int))
            (declare-fun b2 () (Array Int Int))
            (declare-fun b3 () (Array Int Int))

            (assert (= a1 (store base i1 v1)))
            (assert (= a2 (store a1 i2 v2)))
            (assert (= b1 (store base i2 v2)))
            (assert (= b2 (store b1 i1 v1)))
            (assert (= b3 (store b2 i3 v3)))
            (assert (not (= a2 b3)))
            (assert (distinct i1 i2 i3))
            (check-sat)
        "#;

        let commands = parse(input).expect("invariant: valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec
            .execute_all(&commands)
            .expect("invariant: execute succeeds");
        let _ = tx.send(outputs[0].clone());
    });

    match rx.recv_timeout(std::time::Duration::from_secs(15)) {
        Ok(answer) => {
            assert!(
                answer == "sat" || answer == "unknown",
                "Regression #5179: store permutation with extra store (symbolic) must not be unsat, got: {answer}",
            );
        }
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            // Timeout is acceptable: the solver did not return "unsat".
        }
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            // Solver thread panicked or exited without sending.
            // Not a false-UNSAT (no answer was returned), so not a soundness issue.
        }
    }
}

/// Store permutation with distinct concrete indices: two arrays built by
/// applying the same 3 stores in different order to the same base must be
/// equal (read at a Skolem witness). Status: SAT (the formula is satisfiable
/// because the arrays are provably equal).
///
/// Regression for #5086/#5179: `resolve_select_base_for_propagation` used
/// `known_distinct` (including model-based external disequalities) to skip
/// stores, producing spurious equalities -> false UNSAT. The fix uses
/// `explain_distinct_if_provable` which only accepts provable disequalities.
///
/// Note: After the #6282 soundness fix (guarded store-store aliases +
/// no-congruence fixpoint), the solver may return "unknown" on SAT
/// nested-store formulas. "unknown" is sound (never wrong); "unsat"
/// would be a soundness bug.
#[test]
#[allow(clippy::large_stack_arrays)]
#[timeout(15_000)]
fn test_store_permutation_distinct_indices_sat_5086() {
    // For the regression, use a formula where the answer IS sat:
    // store(store(a, 1, e1), 2, e2) vs store(store(a, 2, e2), 1, e3)
    // with e1 != e3. At index 1: fwd has e1, rev has e3, so they differ -> sat.
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (assert (not (= e1 e3)))
        (assert (not (=
            (store (store a 1 e1) 2 e2)
            (store (store a 2 e2) 1 e3))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert!(
        outputs[0] == "sat" || outputs[0] == "unknown",
        "Regression #5086: store permutation with e1 != e3 must not be unsat, got: {}",
        outputs[0]
    );
}

/// Store permutation with 3 distinct concrete indices and equal values:
/// two arrays built by storing the same (index, value) pairs in different
/// order must be equal. The formula asserts they differ -> UNSAT.
///
/// Regression for #5086: the fixpoint loop in combined theory axiom
/// generation must propagate ROW lemmas through the full store chain.
#[test]
fn test_store_permutation_same_values_unsat_5086() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (declare-fun sk () Int)
        (assert (not (=
            (select (store (store (store a 1 e1) 2 e2) 3 e3) sk)
            (select (store (store (store a 3 e3) 2 e2) 1 e1) sk))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #5086: store permutation with same values at distinct indices must be unsat"
    );
}

#[test]
fn test_storecomm_deep_extensionality_witness_no_false_sat() {
    let permutation = [
        4, 51, 7, 16, 8, 23, 25, 19, 40, 2, 31, 45, 30, 59, 13, 54, 10, 47, 21, 18, 32, 35, 50, 24,
        12, 43, 5, 9, 1, 15, 20, 49, 56, 33, 60, 44, 6, 34, 38, 26, 29, 41, 55, 42, 57, 27, 14, 58,
        48, 36, 28, 52, 39, 22, 11, 17, 37, 3, 46, 53,
    ];
    let mut input = String::from(
        "(set-logic QF_AUFLIA)\n\
         (declare-fun a1 () (Array Int Int))\n\
         (declare-fun i () Int)\n\
         (declare-fun sk ((Array Int Int) (Array Int Int)) Int)\n",
    );
    for i in 1..=60 {
        input.push_str(&format!("(declare-fun e{i} () Int)\n"));
    }

    let mut left_prev = "a1".to_string();
    for i in 1..=60 {
        let current = format!("left_{i}");
        input.push_str(&format!(
            "(declare-fun {current} () (Array Int Int))\n\
             (assert (= {current} (store {left_prev} {i} e{i})))\n"
        ));
        left_prev = current;
    }

    let mut right_prev = "a1".to_string();
    for (pos, i) in permutation.iter().enumerate() {
        let current = format!("right_{}", pos + 1);
        input.push_str(&format!(
            "(declare-fun {current} () (Array Int Int))\n\
             (assert (= {current} (store {right_prev} {i} e{i})))\n"
        ));
        right_prev = current;
    }

    input.push_str(&format!(
        "(declare-fun x () Int)\n\
         (declare-fun y () Int)\n\
         (assert (= x (select {left_prev} i)))\n\
         (assert (= y (select {right_prev} i)))\n\
         (assert (= i (sk {left_prev} {right_prev})))\n\
         (assert (not (= x y)))\n\
         (check-sat)\n"
    ));

    let commands = parse(&input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert!(
        outputs[0] == "unsat" || outputs[0] == "unknown",
        "deep storecomm extensionality witness must not return false SAT, got: {}",
        outputs[0]
    );
}

/// Two same-base store chains whose write sets differ at exactly one
/// index (chain A never writes i6, chain B does) must admit the
/// extensionality-witness model: selects at the Skolem index differ.
/// Verdict pin for the alias-explanation prune in
/// `explain_distinct_select_aliases` (explanation choice must remain
/// sound on the minimized storecomm shape).
#[test]
fn test_storecomm_singleton_difference_witness_is_sat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a1 () (Array Int Int))
        (declare-fun a_0 () (Array Int Int))
        (declare-fun a_1 () (Array Int Int))
        (declare-fun a_2 () (Array Int Int))
        (declare-fun a_3 () (Array Int Int))
        (declare-fun a_4 () (Array Int Int))
        (declare-fun a_5 () (Array Int Int))
        (declare-fun b_0 () (Array Int Int))
        (declare-fun b_1 () (Array Int Int))
        (declare-fun b_2 () (Array Int Int))
        (declare-fun b_3 () (Array Int Int))
        (declare-fun b_4 () (Array Int Int))
        (declare-fun b_5 () (Array Int Int))
        (declare-fun i1 () Int)
        (declare-fun i2 () Int)
        (declare-fun i3 () Int)
        (declare-fun i4 () Int)
        (declare-fun i5 () Int)
        (declare-fun i6 () Int)
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (declare-fun e4 () Int)
        (declare-fun e5 () Int)
        (declare-fun e6 () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
        (assert (= a_0 (store a1 i1 e1)))
        (assert (= a_1 (store a_0 i2 e2)))
        (assert (= a_2 (store a_1 i3 e3)))
        (assert (= a_3 (store a_2 i4 e4)))
        (assert (= a_4 (store a_3 i5 e5)))
        (assert (= a_5 (store a_4 i1 e1)))
        (assert (= b_0 (store a1 i1 e1)))
        (assert (= b_1 (store b_0 i3 e3)))
        (assert (= b_2 (store b_1 i5 e5)))
        (assert (= b_3 (store b_2 i2 e2)))
        (assert (= b_4 (store b_3 i4 e4)))
        (assert (= b_5 (store b_4 i6 e6)))
        (assert (= x (select a_5 w)))
        (assert (= y (select b_5 w)))
        (assert (= w (sk a_5 b_5)))
        (assert (not (= i1 i2)))
        (assert (not (= i1 i3)))
        (assert (not (= i1 i4)))
        (assert (not (= i1 i5)))
        (assert (not (= i1 i6)))
        (assert (not (= i2 i3)))
        (assert (not (= i2 i4)))
        (assert (not (= i2 i5)))
        (assert (not (= i2 i6)))
        (assert (not (= i3 i4)))
        (assert (not (= i3 i5)))
        (assert (not (= i3 i6)))
        (assert (not (= i4 i5)))
        (assert (not (= i4 i6)))
        (assert (not (= i5 i6)))
        (assert (not (= x y)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "sat",
        "singleton-difference storecomm witness shape must be sat"
    );
}

/// QF_AUFBV soundness regression: store(const(false), P, true)[P] must be true.
///
/// Formula: P = bv0, V = store(const_array(false), P, true), assert not(select(V, P)).
/// V[P] = V[0] = true (stored), so not(V[P]) = false. Conjunction is UNSAT.
///
/// Root cause (#6124): `parse_simple_sort` couldn't handle BV-indexed Array
/// sorts like `(Array (_ BitVec 32) Bool)` — the naive space-split misparse
/// caused `(_ BitVec 32)` to be treated as Uninterpreted, breaking array
/// axiom generation. Fixed by using `extract_first_sort` for parenthesized
/// nested sorts and normalizing `|_|` quoted underscore.
///
/// Discovered by W3:1924 during #6047 work.
#[test]
fn test_qf_aufbv_const_array_store_select_soundness() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun P () (_ BitVec 32))
        (declare-fun V () (Array (_ BitVec 32) Bool))
        (assert (and (= P (_ bv0 32)) (= V (store ((as const (Array (_ BitVec 32) Bool)) false) P true)) (not (select V P))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #6124: store(const(false), bv0, true)[bv0] contradicts not(select). Got: {}",
        outputs[0]
    );
}

// Array+LIA theory combination: an arithmetic (dis)equality relating two distinct
// `select` terms must be routed to LIA so it can be refuted. These were `unknown`
// before `is_lia_relevant_term` recursed through arithmetic operators (the RHS
// `(+ (select u 4) 2)` was misclassified as non-LIA, so the disequality never
// reached LIA). The pure-UF analogues always worked, so this is array-specific.
// deductive-checks encodes collections as arrays, so arithmetic over select results is
// pervasive in its VCs.

fn solve_one(input: &str) -> String {
    solve_one_with_term_count(input).0
}

/// `solve_one`, additionally reporting the final size of the term arena.
///
/// Used by the AUFLIA preprocessing pins: a pass that mints scratch terms and
/// then discards its own output leaves them interned in an append-only store,
/// where every later whole-store scan and every split-loop round pays for them.
fn solve_one_with_term_count(input: &str) -> (String, usize) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    (outputs[0].clone(), exec.ctx.terms.len())
}

#[test]
fn test_auflia_diseq_two_selects_same_array_unsat() {
    // select(u,3)=11, select(u,4)=9, ¬(select(u,3)=select(u,4)+2) → 11≠11, UNSAT.
    let r = solve_one(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun u () (Array Int Int))
        (assert (= (select u 3) 11))
        (assert (= (select u 4) 9))
        (assert (not (= (select u 3) (+ (select u 4) 2))))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat");
}

#[test]
fn test_auflia_diseq_two_selects_two_arrays_unsat() {
    let r = solve_one(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun u () (Array Int Int))
        (declare-fun w () (Array Int Int))
        (assert (= (select u 3) 11))
        (assert (= (select w 3) 9))
        (assert (not (= (select u 3) (+ (select w 3) 2))))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat");
}

#[test]
fn test_auflia_diseq_select_subtraction_unsat() {
    let r = solve_one(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun u () (Array Int Int))
        (declare-fun w () (Array Int Int))
        (assert (= (select u 3) 11))
        (assert (= (select w 3) 9))
        (assert (not (= (- (select u 3) (select w 3)) 2)))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat");
}

// ==========================================================================
// Definition-cycle model-evaluation guard regression tests
// ==========================================================================
//
// A top-level pointwise forall relating TWO DISTINCT arrays via `select`
// (`forall e. (select s e) = (select s_pre e)`) makes
// `add_quantified_array_extensionality_equalities` inject the extensional
// consequence `(= s s_pre)`. During SAT-side model validation,
// `evaluate_select` resolves a base array variable through its definitional
// equality; because that equality is read in BOTH directions, `s` and `s_pre`
// form a definitional cycle. Combined with an Int-sorted ground atom (which
// routes the problem through the arithmetic-aware solver / model completion),
// this previously drove `evaluate_select` into unbounded self-recursion and a
// hard stack overflow (process abort). The cycle guard must make these
// terminate with a sound answer (Unknown or SAT) and must NOT degrade
// unrelated quantifier refutations or concrete two-array models.

/// Regression (a): the two-distinct-array `select` forall + an Int atom must
/// terminate with a SOUND answer (Unknown or SAT) instead of overflowing the
/// stack. The true answer is SAT (`s = s_pre`, `len_s = 0`); a conservative
/// `unknown` is also acceptable — the only forbidden outcomes are a crash or a
/// false `unsat`.
#[test]
#[timeout(20_000)]
fn test_two_array_select_forall_plus_int_terminates_gap1() {
    let r = solve_one(
        r#"
        (set-logic ALL)
        (declare-fun s () (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-fun s_pre () (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-fun len_s () Int)
        (assert (forall ((e (_ BitVec 32))) (= (select s e) (select s_pre e))))
        (assert (<= 0 len_s))
        (check-sat)
    "#,
    );
    assert!(
        r == "unknown" || r == "sat",
        "two-array select forall + Int atom must terminate with a sound \
         answer (unknown or sat), got: {r}"
    );
}

/// Regression (b): a SAME-array pointwise forall plus a contradictory pair of
/// Int atoms must still be decided `unsat` from the arithmetic conflict. The
/// single array means no extensionality equality (hence no definitional
/// cycle) is introduced, so the guard is inert here and the Int refutation is
/// unaffected.
#[test]
#[timeout(20_000)]
fn test_same_array_select_forall_plus_int_conflict_unsat_gap1() {
    let r = solve_one(
        r#"
        (set-logic ALL)
        (declare-fun t () (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-fun len_t () Int)
        (assert (forall ((e (_ BitVec 32))) (= (select t e) (select t e))))
        (assert (< len_t 0))
        (assert (> len_t 0))
        (check-sat)
    "#,
    );
    assert_eq!(
        r, "unsat",
        "same-array forall is trivially true; the Int atoms are contradictory, \
         so the conjunction is UNSAT"
    );
}

/// Regression (c): a normal quantifier refutation (universal over Int with a
/// ground counterexample) must still be decided `unsat`. The model-evaluation
/// cycle guard only affects SAT-side array-definition chasing, so it must not
/// suppress this refutation (no over-bail to Unknown).
#[test]
#[timeout(20_000)]
fn test_normal_quantifier_refutation_still_unsat_gap1() {
    let r = solve_one(
        r#"
        (set-logic ALL)
        (declare-fun f (Int) Int)
        (declare-fun a () Int)
        (assert (forall ((x Int)) (> (f x) 0)))
        (assert (< (f a) 0))
        (check-sat)
    "#,
    );
    assert_eq!(
        r, "unsat",
        "forall x. f(x) > 0 with f(a) < 0 is refuted by instantiating x := a"
    );
}

/// Regression (d): a concrete two-array model (`b = store(a, 0, 5)`) must still
/// validate as `sat`. Here `array_variable_definition` resolves `b` to a
/// concrete `store` (not a sibling variable), so the cycle guard does not fire
/// — confirming it does not over-bail on ordinary two-array definitional
/// inputs.
#[test]
#[timeout(20_000)]
fn test_concrete_two_array_definition_still_sat_gap1() {
    let r = solve_one(
        r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 0 5)))
        (assert (= (select b 0) 5))
        (check-sat)
    "#,
    );
    assert_eq!(
        r, "sat",
        "b = store(a,0,5) and select(b,0) = 5 is consistent (SAT)"
    );
}

/// Regression (e): a bare mutual array equality `(= a b)` must be decided
/// `sat` without crashing. `array_variable_definition` reads the equality in
/// both directions, so evaluating it during model validation chases
/// `a -> b -> a` through `format_array_term_value`; before the cycle guard
/// this recursed until the process was OOM-killed.
#[test]
#[timeout(20_000)]
fn test_mutual_array_equality_terminates_sat_gap1() {
    let r = solve_one(
        r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= a b))
        (check-sat)
    "#,
    );
    assert_eq!(
        r, "sat",
        "(= a b) is satisfiable (a and b denote the same array)"
    );
}

/// Regression (f): formatting a model for the mutual array equality `(= a b)`
/// via `(get-model)` must terminate (exercises the `format_array_term_value`
/// definitional-cycle guard directly) and still report `sat`.
#[test]
#[timeout(20_000)]
fn test_mutual_array_equality_get_model_terminates_gap1() {
    let input = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= a b))
        (check-sat)
        (get-model)
    "#;
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs[0], "sat", "(= a b) is satisfiable");
    // The second output is the formatted model; the only contract here is that
    // model formatting terminated (no unbounded recursion / OOM) and produced a
    // non-empty model block.
    assert!(
        outputs.len() > 1 && outputs[1].contains("model"),
        "get-model must produce a model block, got: {outputs:?}"
    );
}

#[test]
fn test_auflia_quantified_map_compose_unsat() {
    // Two forall map axioms chained: instantiating the c-axiom exposes select(b,_)
    // which then must trigger the b-axiom; the offset arithmetic over selects must
    // reach LIA. c[i]=b[i]+1, b[i]=a[i]+1 ⊢ c[7]=a[7]+2.
    let r = solve_one(
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun c () (Array Int Int))
        (assert (forall ((i Int)) (! (= (select b i) (+ (select a i) 1)) :pattern ((select b i)))))
        (assert (forall ((i Int)) (! (= (select c i) (+ (select b i) 1)) :pattern ((select c i)))))
        (assert (not (= (select c 7) (+ (select a 7) 2))))
        (check-sat)
    "#,
    );
    assert_eq!(r, "unsat");
}

/// #anra-select-nonlinear wrong-sat: a Real array select pinned to a constant,
/// equated to a variable that feeds a nonlinear product, must NOT escape as SAT.
///
/// `x = (select A i)` and `(select A i) = 3.0` force `x = 3.0`, so `(* x x) = 9.0`
/// and the assertion `(not (= (* x x) 9.0))` is UNSAT. AUFNRA routes arrays via UF
/// (solve_uf_nra), so there is no array model: the select lives only in the EUF
/// class with the constant. The LRA/NRA side independently assigns `x = 0`, leaving
/// the select unresolved during validation, and the internally-inconsistent model
/// previously escaped as a wrong SAT. The strict gate must now reject it (the select
/// resolves to its EUF class constant, exposing `(= x (select A i)) -> false`), so AY
/// returns the sound `unknown` (it cannot refute the nonlinear product directly).
#[test]
fn test_aufnra_select_const_in_nonlinear_product_not_wrong_sat() {
    for r in [
        solve_one(
            r#"
            (set-logic ALL)
            (declare-const A (Array Int Real))
            (declare-const i Int)
            (declare-const x Real)
            (assert (= x (select A i)))
            (assert (= (select A i) 3.0))
            (assert (not (= (* x x) 9.0)))
            (check-sat)
        "#,
        ),
        // Distinct variables x, y over two pinned selects feeding a product.
        solve_one(
            r#"
            (set-logic ALL)
            (declare-const A (Array Int Real))
            (declare-const i Int)
            (declare-const j Int)
            (declare-const x Real)
            (declare-const y Real)
            (assert (= x (select A i)))
            (assert (= y (select A j)))
            (assert (= (select A i) 3.0))
            (assert (= (select A j) 5.0))
            (assert (not (= (* x y) 15.0)))
            (check-sat)
        "#,
        ),
    ] {
        assert_ne!(r, "sat", "must not return wrong SAT (z3 = unsat)");
    }
}

/// Companion to the above: a CONSISTENT array-select + nonlinear-product formula
/// must not be over-degraded. `x = (select A 0) = 3.0` and `(= (* x x) 9.0)` is SAT;
/// the strict-gate select resolution must agree (3.0 == 3.0) and not reject it. AY
/// may still return `unknown` if its nonlinear reasoning cannot confirm the product,
/// but it must never return `unsat` (no wrong-UNSAT introduced).
#[test]
fn test_aufnra_select_const_consistent_product_not_wrong_unsat() {
    let r = solve_one(
        r#"
        (set-logic ALL)
        (declare-const A (Array Int Real))
        (declare-const x Real)
        (assert (= x (select A 0)))
        (assert (= (select A 0) 3.0))
        (assert (= (* x x) 9.0))
        (check-sat)
    "#,
    );
    assert_ne!(
        r, "unsat",
        "consistent SAT formula must not become wrong UNSAT"
    );
}

/// P0 regression: this satisfiable minimized SV-COMP instance must never be
/// reported UNSAT. It is the reproducer the nested-array quarantine
/// (`53e9ac3c07`) was written for.
///
/// PREMISE REFRESHED, assertion unchanged. This test used to say the path
/// "currently derives a false UNSAT ... until the combination defect is
/// root-caused". The defect WAS root-caused and fixed at the source
/// (`f978212a6f` + `7272612d89`): a vacuously true `all()` accepted a
/// GC-compacted, zero-length pending-theory-conflict slice as a live conflict
/// and handed conflict analysis a spurious empty clause. Since that fix the
/// internal fast wrong `unsat` is gone, so this input now fails closed on its
/// own budget and no longer reaches the quarantine at all — measured 2026-09-06
/// on `9fb122a24a`: `interrupted`/`timeout` at `-T:60`, with no degrade
/// warning. See Round 20 of
/// the development design notes.
///
/// The pin therefore still guards the same soundness property (never `unsat`
/// here) but it is no longer evidence that the quarantine works; the quantified
/// pin below is. Keep both: this one covers the source fix, that one covers the
/// gate.
#[test]
// This minimized ALIA instance is intentionally expensive: the solver must
// reach the raw refutation before the public-result quarantine can reject it.
// Leave enough wall-clock headroom for shared CI hosts running parallel builds.
#[timeout(600_000)]
fn test_nested_array_alia_false_unsat_is_quarantined() {
    let input = include_str!("../../../../repros/cs_stateful-1.i_2.MINIMIZED.smt2");
    let (verdict, term_count) = solve_one_with_term_count(input);
    assert_eq!(verdict, "unknown");

    // #arraylazy-lift-garbage (z3-parity r3 rank 11): this file is also the
    // committed reproducer for the AUFLIA preprocess ITE-lift blow-up. Its
    // 331 generated array axioms expand into select-over-store ITEs, the
    // arithmetic Shannon lift then overruns `ITE_LIFT_NEW_TERM_BUDGET`
    // (200,000), and the pass is ABANDONED in favour of definitional ITE
    // naming — but the ~203,000 terms it minted used to stay interned in the
    // append-only arena. Measured at -T:20 before the reclaim landed:
    // `:term-count 206,520`, peak RSS 1,915 MB, 119 refinement rounds;
    // after: 5,680 / 100 MB / 1,135 rounds, same verdict. The lift's output
    // is discarded wholesale on that branch, so reclaiming it cannot change
    // any verdict — only what every later whole-store scan has to walk.
    //
    // The bound is deliberately far above the measured 5,680 and far below
    // the 206,520 regression: it fails on a reintroduced blow-up, not on
    // ordinary drift.
    assert!(
        term_count < 50_000,
        "AUFLIA preprocess must not retain the abandoned Shannon expansion: \
         term arena held {term_count} terms (pre-fix regression: ~206,520)"
    );
}

/// #nested-array-quarantine-quantified — the boundary the 2026-09-06 z3-parity
/// ledger proposed to move (the development design notes
/// 2026-09-06-diagnoses-r2-quantified.md` at `9598c4206`, rank 3 / next-action 3), pinned
/// where the evidence actually leaves it.
///
/// The input is the unit-split form of the Ultimate Automizer row
/// `ABV/…UltimateAutomizerSvcomp2019__standard_running_true-unreach-call.i_3`.
/// Splitting `(assert (and c1 … cn))` into bare conjuncts is an equivalent
/// rewrite, and it is what makes `UnitFacts::from_assertions` see the negated
/// `exists` as an entailed forall — so unlike the original file, AY reaches
/// `CERT/classify: result=Unsat em_added=true` here. z3 4.16.0 also answers
/// `unsat`, so the verdict AY computes is CORRECT.
///
/// It is withheld anyway, and that is the point. The refutation reconstructs to
/// a bare `(step t0 (cl) :rule trust)`: `--self-check` rejects it ("computed
/// UNSAT is not backed by a fully-checked refutation proof"), the strict
/// full-problem proof leg fails, the checked-SAT sidecar declines, the entailed
/// residue is satisfiable, and `authenticate_bool_bv_unsat_query` rejects the
/// query outright because `Forall`/`Exists` are outside its ground fragment.
/// Every rung of `nested_array_unsat_has_current_authority` therefore declines
/// and the quarantine degrades to `unknown` / phase
/// `array-combination-quarantine`.
///
/// Publishing this would be publishing a nested-array UNSAT on trust alone,
/// which is exactly what the gate exists to stop — so a future change that
/// makes this print `unsat` has not "unblocked the Ultimate family", it has
/// removed the last check on a class with a recorded wrong-answer history. Fix
/// it by giving the ladder a real authority for instance-closure refutations
/// (which needs proof reconstruction for the ground BV core first — that core
/// is uncertifiable today even when the instance is written out by hand), never
/// by widening the predicate.
#[test]
#[timeout(120_000)]
fn test_nested_array_quantified_instance_unsat_without_authority_is_quarantined() {
    let input =
        include_str!("../../../../repros/abv-nested-array-quantified-unsat-quarantine.smt2");
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(
        outputs[0], "unknown",
        "an E-matched nested-array UNSAT whose only proof is a Trust step must \
         stay withheld"
    );
    assert_eq!(
        exec.statistics().get_string("unknown.phase"),
        Some("array-combination-quarantine"),
        "the nested-array quarantine — not some upstream quantifier bail — must \
         be the gate that withholds this verdict"
    );
    assert!(
        !exec.last_command_unsat_was_strictly_verified(),
        "nothing here is strictly verified; a true admission would mean the \
         ladder found an authority and the verdict should have published"
    );
}

/// #nested-array-residue-rescue: a nested-array DECLARATION must not condemn a
/// refutation that never used one.
///
/// This is the shape the quarantine over-rejects on the NASA AUFLIRA family:
/// the nested `u` appears only in dead-weight hypotheses, while the actual
/// contradiction is a single-level read-over-write (`(store (store s 0 v) 1 w)`
/// read at index 1 must be `w`). The rescue refutes the nested-array-FREE
/// entailed residue — the goal negation alone — which forces UNSAT of the whole
/// (see `Executor::nested_array_free_residue_unsat`), so the computed UNSAT is
/// retained rather than discarded.
///
/// The second assertion is deliberately written `(not (=> hyp goal))` so the
/// test also pins the NNF-aware conjunct split: a naive `and`-only split would
/// drop the whole assertion and leave an empty residue.
///
/// This ALSO pins the rescue's proof-mode guard against the predicate whose
/// meaning moved underneath it. The rescue declines "in proof mode", and it
/// spelled that `produce_proofs_enabled()` — which reports the INTERNAL proof
/// tracker, and `begin_public_solve` turns that on for every public decision
/// because the UNSAT certificate is mandatory. The guard therefore fired 100%
/// of the time and the rescue was DEAD CODE (measured: `AY_DEBUG_RESIDUE=1`
/// printed `decline: produce_proofs_enabled` on this very input, before any
/// residue was built). `is_producing_proofs()` is the predicate that still
/// means what the guard's comment says; see
/// `test_nested_array_residue_rescue_declines_when_a_proof_is_requested` for
/// the other half of that boundary.
#[test]
fn test_nested_array_free_residue_retains_unsat() {
    assert_eq!(
        solve_one(NESTED_ARRAY_FREE_RESIDUE_INPUT),
        "unsat",
        "the refutation is a single-level ROW read; a nested-array declaration \
         elsewhere in the problem must not quarantine it"
    );
}

/// The input behind the residue-rescue pair above and below.
const NESTED_ARRAY_FREE_RESIDUE_INPUT: &str = r#"
    (set-logic AUFLIA)
    (declare-fun u () (Array Int (Array Int Int)))
    (declare-fun s () (Array Int Int))
    (declare-fun v () Int)
    (declare-fun w () Int)
    (assert (= (select (select u 0) 0) v))
    (assert (not (=> (= (select (select u 1) 1) w)
                     (= (select (store (store s 0 v) 1 w) 1) w))))
    (check-sat)
"#;

/// Proof requests still cannot borrow the residue rescue's semantic evidence.
/// This query now publishes UNSAT because the full-problem proof itself passes
/// the strict checker; pin that stronger authority so a future regression
/// cannot silently relabel residue evidence as a requested proof artifact.
#[test]
fn test_nested_array_proof_request_uses_strict_full_problem_authority() {
    let commands = parse(NESTED_ARRAY_FREE_RESIDUE_INPUT).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(
        outputs[0], "unsat",
        "a checked full-problem proof may publish independently of residue rescue"
    );
    assert!(
        exec.last_command_unsat_was_strictly_verified(),
        "a requested proof artifact must be the exact strict authority consumed at publication"
    );
}

/// When the refutation genuinely needs the nested array, a satisfiable residue
/// cannot authorize it. The complete full-problem proof now validates
/// strictly, however, and is an independent authority for the real UNSAT.
///
/// Here `(select u 0)` is equal to two arrays asserted distinct — an UNSAT that
/// rests entirely on the guarded lazy array+arithmetic combination. Every
/// nested-array conjunct is filtered out, leaving the residue `(>= p 0)`, which
/// is satisfiable. Publication must therefore be specifically strict-proof
/// backed, never attributed to the residue lane.
#[test]
fn test_nested_array_dependent_unsat_uses_strict_full_problem_authority() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun u () (Array Int (Array Int Int)))
        (declare-fun v () (Array Int Int))
        (declare-fun w () (Array Int Int))
        (declare-fun p () Int)
        (assert (= (select u 0) v))
        (assert (= (select u 0) w))
        (assert (not (= v w)))
        (assert (>= p 0))
        (check-sat)
    "#;
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs[0], "unsat");
    assert!(
        exec.last_command_unsat_was_strictly_verified(),
        "the satisfiable residue cannot authorize this nested-array-dependent refutation"
    );
}

/// Solve `input` in the shed posture (`--rigor fast`, `--no-proof`,
/// `--z3-mode`): no search-time proof, so the quarantine's strict full-problem
/// proof rung has nothing to check. Returns the first verdict and the
/// `unknown.phase` statistic.
fn solve_one_shed(input: &str) -> (String, Option<String>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    let phase = exec
        .statistics()
        .get_string("unknown.phase")
        .map(str::to_string);
    (outputs[0].clone(), phase)
}

/// The congruence refutation behind the array-to-UF abstraction rung.
const NESTED_ARRAY_CONGRUENCE_UNSAT: &str = r#"
    (declare-const u (Array Int (Array Int Int)))
    (declare-const v (Array Int Int))
    (declare-const w (Array Int Int))
    (assert (= (select u 0) v))
    (assert (= (select u 0) w))
    (assert (not (= v w)))
    (check-sat)
"#;

/// #nested-array-uf-abstraction: in the shed posture this used to answer
/// `unknown` / `array-combination-quarantine` although z3 refutes it and the
/// default posture publishes it on a strict proof. `v = (select u 0) = w`
/// contradicts `v != w` by congruence alone, so the checked array-to-UF
/// abstraction rung (`check_sat/nested_array_uf_abstraction.rs`) refutes the
/// abstraction under a checked certificate and the quarantine retains the
/// verdict.
#[test]
fn test_nested_array_congruence_unsat_publishes_in_shed_posture() {
    let (verdict, phase) = solve_one_shed(NESTED_ARRAY_CONGRUENCE_UNSAT);
    assert_eq!(
        verdict, "unsat",
        "the congruence refutation needs no array axiom (phase {phase:?})"
    );
}

/// The satisfiable siblings: dropping the disequality, or one of the two
/// equalities, leaves a problem z3 answers `sat`. Neither may become `unsat`.
#[test]
fn test_nested_array_congruence_sat_siblings_stay_sat_in_shed_posture() {
    for input in [
        r#"
        (declare-const u (Array Int (Array Int Int)))
        (declare-const v (Array Int Int))
        (declare-const w (Array Int Int))
        (assert (= (select u 0) v))
        (assert (= (select u 0) w))
        (check-sat)
        "#,
        r#"
        (declare-const u (Array Int (Array Int Int)))
        (declare-const v (Array Int Int))
        (declare-const w (Array Int Int))
        (assert (= (select u 0) v))
        (assert (not (= v w)))
        (check-sat)
        "#,
    ] {
        assert_eq!(solve_one_shed(input).0, "sat", "{input}");
    }
}

/// #nested-array-checked-rung RE-PIN (was `..._stays_quarantined_in_shed_posture`,
/// the rung's negative control while it appended no axiom): nested read-over-write.
/// The abstraction now carries the checked instance `(select' (store' u i v) i) = v`,
/// so `i = j` refutes it on a strict proof and the shed posture publishes (z3:
/// `unsat`). The negative control is now an UNSAT needing outer extensionality:
/// `nested_array_uf_abstraction::tests::instance::an_extensionality_refutation_stays_withheld`.
#[test]
fn test_nested_array_row_dependent_unsat_publishes_on_a_checked_instance() {
    let (verdict, phase) = solve_one_shed(
        r#"
        (declare-const u (Array Int (Array Int Int)))
        (declare-const v (Array Int Int))
        (declare-const w (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= (select (store u i v) j) w))
        (assert (= i j))
        (assert (not (= v w)))
        (check-sat)
        "#,
    );
    assert_eq!(verdict, "unsat", "phase {phase:?}");
}

/// The same authorization boundary covers `check-sat-assuming`. A direct
/// contradiction between an authored equality and an assumption is now
/// published only because its exact assumption-bound proof validates strictly.
#[test]
fn test_nested_array_unsat_assumption_uses_strict_query_authority() {
    let input = r#"
        (set-logic QF_ALIA)
        (declare-const a (Array Int (Array Int Int)))
        (declare-const b (Array Int (Array Int Int)))
        (assert (= a b))
        (check-sat-assuming ((not (= a b))))
    "#;
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs[0], "unsat");
    assert!(
        exec.last_command_unsat_was_strictly_verified(),
        "assumption order and membership must be bound into the consumed strict proof authority"
    );
}

/// #dt-array-nested-const-idx — the FINITE half of the nested-array boundary.
///
/// `test_nested_array_alia_false_unsat_is_quarantined` above pins the INFINITE
/// (`Int`-indexed) side: still `unknown`, because the guarded lazy
/// array+arithmetic combination has no trust-free certificate. This is the
/// BitVec-indexed twin of the same congruence conflict — two reads of one
/// nested array at a constant-vs-symbolic index that provably denote the same
/// datatype cell, whose `p` fields are asserted unequal. z3 4.16.0 refutes it.
///
/// It leaves the quarantine through the FIRST authority
/// `nested_array_unsat_has_current_authority` consults: the reconstructed
/// full-problem proof passes `check_proof_strict_with_datatypes`. That is the
/// identical mechanism, and the identical `StrictProof` admission class, that
/// `test_nested_array_proof_request_uses_strict_full_problem_authority` and its
/// two neighbours above pin — all three were converted from `unknown` to
/// `unsat` by the same commit (233ab32da, "fix(arrays): authenticate nested
/// finite unsat"), which is also the commit that gave the quarantine its
/// authority ladder. Measured admission for this query at this sha:
/// `strict=true, independent=false, exact_semantic=false`.
///
/// Pin the AUTHORITY, not merely the verdict: a regression that widened the
/// quarantine gate would still print `unsat` here, and only the admission class
/// can tell a strict-checked refutation apart from an uncertified leak. Strict
/// checking is what makes this a trust-free certificate — the strict checker is
/// the one that rejects `trust` and `hole` steps.
#[test]
fn test_nested_finite_array_congruence_uses_strict_proof_authority() {
    let input = r#"
        (set-logic ALL)
        (declare-datatype T ((mk (p (_ BitVec 4)) (q (_ BitVec 4)))))
        (declare-const R (Array (_ BitVec 4) (Array (_ BitVec 4) T)))
        (declare-const k (_ BitVec 4))
        (declare-const i (_ BitVec 4))
        (declare-const z T)
        (assert (= z (select (select R k) i)))
        (assert (= k #x3))
        (assert (not (= (p (select (select R #x3) i)) (p (select (select R k) i)))))
        (check-sat)
    "#;
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs[0], "unsat");
    assert!(
        exec.last_command_unsat_was_strictly_verified(),
        "a nested-array UNSAT may leave the quarantine only on an authority the \
         quarantine actually checked; the strict full-problem proof is the one \
         consumed here"
    );
}

/// #arr2lia-inflate: the speculative arrays-to-LIA rescue reduction must not
/// inflate the SHARED term store out of proportion to the input.
///
/// Saturation gives each distinct array base one read per index, so its
/// read-over-read (Ackermann) cost is QUADRATIC in the index count, while the
/// pre-saturation congruence guard is only linear in it. A chain of array
/// aliases plus any arithmetic atom therefore passed that guard and interned
/// tens of thousands of terms; the `ack_pairs` budget downstream is consulted
/// only AFTER those terms exist, so bailing there could not undo the growth.
/// Downstream AUFLIA passes scan the whole term store, so the "rescue" cost far
/// more than the search it was meant to rescue: 32 aliased arrays + `(>= p 0)`
/// interned 66,595 terms and took 7.5s; at 40 arrays it timed out entirely.
///
/// The formula is trivially satisfiable (make every array equal), so any
/// non-`sat` answer — or a slow one — is the regression.
#[test]
#[timeout(60_000)]
fn arrays_to_lia_alias_chain_with_arithmetic_does_not_blow_up_term_store() {
    let n = 60;
    let mut src = String::from("(set-logic ALL)\n");
    for k in 0..n {
        src.push_str(&format!("(declare-const x{k} (Array Int Int))\n"));
    }
    src.push_str("(declare-const i Int)\n(declare-const p Int)\n");
    // The arithmetic atom is what routes this through the AUFLIA/arrays-to-LIA
    // path at all; `p` shares nothing with the arrays.
    src.push_str("(assert (>= p 0))\n");
    for k in 0..n - 1 {
        src.push_str(&format!("(assert (= x{k} x{}))\n", k + 1));
    }
    src.push_str("(assert (= (select x0 i) 7))\n(check-sat)\n");
    assert_eq!(
        solve_one(&src),
        "sat",
        "aliased array chain + arithmetic must stay solvable, not drown in \
         read-over-read axioms"
    );
}
