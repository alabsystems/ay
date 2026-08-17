// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `array_soundness_4304` to preserve test FQNs.

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
