// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `array_soundness_4304` to preserve test FQNs.

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
