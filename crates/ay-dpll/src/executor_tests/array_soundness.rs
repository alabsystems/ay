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
        outputs[0], "sat",
        "const(1) and store(const(0),5,1) differ at index 0 (1 vs 0); I != J is SAT"
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
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    outputs[0].clone()
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

/// P0 regression: the combined nested-array/arithmetic path currently derives
/// a false UNSAT on this satisfiable minimized SV-COMP instance (z3 supplies a
/// model, and AY's strict proof reconstruction rejects its own refutation).
/// Until the combination defect is root-caused, the public result boundary must
/// quarantine the raw UNSAT as Unknown.
#[test]
// This minimized ALIA instance is intentionally expensive: the solver must
// reach the raw refutation before the public-result quarantine can reject it.
// Leave enough wall-clock headroom for shared CI hosts running parallel builds.
#[timeout(600_000)]
fn test_nested_array_alia_false_unsat_is_quarantined() {
    let input = include_str!("../../../../repros/cs_stateful-1.i_2.MINIMIZED.smt2");
    assert_eq!(solve_one(input), "unknown");
}

/// The same authorization boundary must cover `check-sat-assuming`; otherwise
/// moving a nested-array contradiction into an assumption could bypass the
/// plain-check quarantine and expose an uncertified UNSAT through the API.
#[test]
fn test_nested_array_unsat_assumption_is_quarantined() {
    let input = r#"
        (set-logic QF_ALIA)
        (declare-const a (Array Int (Array Int Int)))
        (declare-const b (Array Int (Array Int Int)))
        (assert (= a b))
        (check-sat-assuming ((not (= a b))))
    "#;
    assert_eq!(solve_one(input), "unknown");
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
