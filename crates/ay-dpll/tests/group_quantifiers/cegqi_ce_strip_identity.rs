// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #cegqi-ce-strip (2026-07-18): the CEGQI unsat
//! disambiguation probe must strip counterexample lemmas by CE-VARIABLE
//! MENTION, not by `TermId` identity alone.
//!
//! Failure mode fixed: for `b = store a 3 9` plus the ENTAILED
//! `forall i. i != 3 => b[i] = a[i]`, CEGQI asserts the CE hypothesis
//! `¬body(e)` and the ground solve routes to `solve_array_euf` (no
//! substantive integer arithmetic), which DESTRUCTIVELY rewrites
//! `ctx.assertions` in place: store-flat inlining re-mints the CE conjunct
//! under a fresh hash-consed id and the array-axiom fixpoint appends
//! read-over-write clauses simplified UNDER the CE units. The identity-only
//! strip (`!ce_lemma_ids.contains(a)`) missed the re-minted conjunct and the
//! CE-tainted residue, so the "ground-minus-CE" probe re-derived the same
//! CE-driven contradiction and a WRONG `unsat` shipped (z3: `sat`) — latent
//! since the initial publish commit.
//!
//! The fix never treats the rewritten live assertion set as verdict authority.
//! Rewriting under the CE hypothesis can both delete an authored constraint and
//! leave a CE-variable-free residue, so even CE-variable filtering is
//! insufficient. UNSAT is published only after a disposable verifier
//! reconstructs and refutes the snapshot ground core plus provenance-tagged
//! instances of unconditionally asserted universals. SAT separately requires a
//! solved and validated model of that exact reconstructed ground core plus the
//! per-universal refutation certificate.
//!
//! Contract pinned here, for the whole shape family (store equation +
//! guarded entailed forall, AUFLIA routing without substantive arithmetic):
//! - a satisfiable shape must NEVER answer `unsat` (sat or a fail-closed
//!   unknown are both acceptable — completeness to z3's `sat` is a separate
//!   follow-on);
//! - the exists-dual is never reported `unsat` (it may fail closed to
//!   `unknown` when no total model certificate is available);
//! - wrong-fact twins and the mixed genuinely-unsat shape must STAY `unsat`.

use ntest::timeout;

/// The satisfiable shapes: every result must be `sat` or `unknown`, never
/// `unsat`.
fn assert_never_unsat(name: &str, smt: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        results.iter().all(|r| r == "sat" || r == "unknown"),
        "{name}: satisfiable shape answered {results:?} — a wrong unsat is \
         the worst outcome (z3: sat)"
    );
}

/// The original wrong-unsat: entailed guarded forall over a store equation.
#[test]
#[timeout(10000)]
fn v01_store_entailed_forall_distinct_guard_never_unsat() {
    assert_never_unsat(
        "v01_orig",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (select a i)))))
        (check-sat)
    "#,
    );
}

/// Other index/value (negative stored value).
#[test]
#[timeout(10000)]
fn v02_other_index_value_never_unsat() {
    assert_never_unsat(
        "v02_other_index",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 100 (- 5))))
        (assert (forall ((i Int)) (=> (distinct i 100) (= (select b i) (select a i)))))
        (check-sat)
    "#,
    );
}

/// `(not (= i 3))` guard spelling.
#[test]
#[timeout(10000)]
fn v03_noteq_guard_never_unsat() {
    assert_never_unsat(
        "v03_noteq_guard",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (not (= i 3)) (= (select b i) (select a i)))))
        (check-sat)
    "#,
    );
}

/// `<=` guard: the order atom routes through the copy-based AUFLIA pipeline
/// (CE ids stay valid) — stays sound; pinned so a routing change cannot
/// silently reopen the family.
#[test]
#[timeout(10000)]
fn v04_le_guard_never_unsat() {
    assert_never_unsat(
        "v04_le_guard",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (<= i 2) (= (select b i) (select a i)))))
        (check-sat)
    "#,
    );
}

/// The exists-dual is satisfiable. A total certificate may decide `sat`; a
/// conservative `unknown` is also acceptable, but `unsat` is never sound.
#[test]
#[timeout(10000)]
fn v05_exists_dual_never_unsat() {
    assert_never_unsat(
        "v05_exists_dual",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (not (exists ((i Int)) (and (distinct i 3) (not (= (select b i) (select a i)))))))
        (check-sat)
    "#,
    );
}

/// Two stores, doubly-guarded forall.
#[test]
#[timeout(10000)]
fn v06_two_stores_never_unsat() {
    assert_never_unsat(
        "v06_two_stores",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store (store a 3 9) 5 7)))
        (assert (forall ((i Int)) (=> (and (distinct i 3) (distinct i 5)) (= (select b i) (select a i)))))
        (check-sat)
    "#,
    );
}

/// Real elements.
#[test]
#[timeout(10000)]
fn v07_real_elements_never_unsat() {
    assert_never_unsat(
        "v07_real_elems",
        r#"
        (set-logic AUFLIRA)
        (declare-fun a () (Array Int Real))
        (declare-fun b () (Array Int Real))
        (assert (= b (store a 3 9.0)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (select a i)))))
        (check-sat)
    "#,
    );
}

/// `(+ (select a i) 0)` offset body — arithmetic that does NOT count as
/// substantive, so the destructive array path still runs.
#[test]
#[timeout(10000)]
fn v08_offset_zero_body_never_unsat() {
    assert_never_unsat(
        "v08_offset_zero",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (+ (select a i) 0)))))
        (check-sat)
    "#,
    );
}

/// Unguarded (non-entailed but satisfiable) forall.
#[test]
#[timeout(10000)]
fn v09_unguarded_forall_never_unsat() {
    assert_never_unsat(
        "v09_unguarded",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (= (select b i) (select a i))))
        (check-sat)
    "#,
    );
}

/// WRONG-FACT control: `b[4] != a[4]` contradicts the forall — must STAY
/// unsat (the strip must not weaken a genuine unsat into sat/unknown).
#[test]
#[timeout(10000)]
fn v10_wrong_fact_stays_unsat() {
    let results = crate::common::solve_vec(
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (select a i)))))
        (assert (distinct (select b 4) (select a 4)))
        (check-sat)
    "#,
    );
    assert_eq!(results, vec!["unsat"], "wrong-fact control must stay unsat");
}

/// WRONG-FACT control: body `= a[i] + 1` is refuted at any i != 3 — must
/// STAY unsat.
#[test]
#[timeout(10000)]
fn v11_plus_one_body_stays_unsat() {
    let results = crate::common::solve_vec(
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (+ (select a i) 1)))))
        (check-sat)
    "#,
    );
    assert_eq!(results, vec!["unsat"], "plus-one body must stay unsat");
}

/// Or-guard spelling `(or (= i 3) ...)`.
#[test]
#[timeout(10000)]
fn v12_or_guard_never_unsat() {
    assert_never_unsat(
        "v12_or_guard",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (or (= i 3) (= (select b i) (select a i)))))
        (check-sat)
    "#,
    );
}

/// Bool elements.
#[test]
#[timeout(10000)]
fn v13_bool_elements_never_unsat() {
    assert_never_unsat(
        "v13_bool_elems",
        r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Bool))
        (declare-fun b () (Array Int Bool))
        (assert (= b (store a 3 true)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (select a i)))))
        (check-sat)
    "#,
    );
}

/// No `set-logic` at all.
#[test]
#[timeout(10000)]
fn v14_no_set_logic_never_unsat() {
    assert_never_unsat(
        "v14_no_logic",
        r#"
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (select a i)))))
        (check-sat)
    "#,
    );
}

/// Constant-target body (satisfiable, not entailed).
#[test]
#[timeout(10000)]
fn v15_const_target_body_never_unsat() {
    assert_never_unsat(
        "v15_const_target",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) 0))))
        (check-sat)
    "#,
    );
}

/// Flipped equality operands on both the store equation and the body.
#[test]
#[timeout(10000)]
fn v16_flipped_equality_operands_never_unsat() {
    assert_never_unsat(
        "v16_flipped_eq",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= (store a 3 9) b))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select a i) (select b i)))))
        (check-sat)
    "#,
    );
}

/// EQ-GUARD CANARY (review objection): a positive guard `(= i 3)` yields a
/// POSITIVE CE unit `(= e 3)` that alias substitution could constant-fold
/// AWAY, producing CE-derived residue that mentions no CE variable — the one
/// shape the mention filter cannot see. Currently fails closed via E-matching
/// BEFORE reaching the disambiguation path; pinned so a routing change that
/// re-opens the hole is caught.
#[test]
#[timeout(10000)]
fn adv1_eq_guard_positive_ce_unit_never_unsat() {
    assert_never_unsat(
        "adv1_eqguard",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (= i 3) (= (select b i) 9))))
        (check-sat)
    "#,
    );
}

/// EQ-GUARD wrong-fact twin: `b[3] = 8` contradicts the store — must STAY
/// unsat.
#[test]
#[timeout(10000)]
fn adv2_eq_guard_wrong_fact_stays_unsat() {
    let results = crate::common::solve_vec(
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (= i 3) (= (select b i) 8))))
        (check-sat)
    "#,
    );
    assert_eq!(
        results,
        vec!["unsat"],
        "eq-guard wrong-fact must stay unsat"
    );
}

/// `(or (distinct i 3) ...)` guard spelling of the eq-guard family.
#[test]
#[timeout(10000)]
fn adv3_or_distinct_guard_never_unsat() {
    assert_never_unsat(
        "adv3_notdistinct",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (or (distinct i 3) (= (select b i) 9))))
        (check-sat)
    "#,
    );
}

/// TWO FORALLS, only the first entailed (review objection: live wrong-unsat
/// at pre-fix HEAD): the second forall is satisfiable but NOT entailed
/// (a[3] is free), so no per-lemma certificate exists and the result must
/// fail closed — never unsat (z3: sat).
#[test]
#[timeout(10000)]
fn adv4_two_foralls_one_entailed_never_unsat() {
    assert_never_unsat(
        "adv4_two_foralls",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (select a i)))))
        (assert (forall ((j Int)) (=> (distinct j 5) (= (select b j) (select a j)))))
        (check-sat)
    "#,
    );
}

/// MIXED genuinely-unsat: store + entailed forall + ground contradiction at a
/// SYMBOLIC k with `k != 3` — the CE-variable strip must not delete the
/// user's own `k` facts (k is not a CE variable) and the verdict must STAY
/// unsat.
#[test]
#[timeout(10000)]
fn adv5_symbolic_ground_contradiction_stays_unsat() {
    let results = crate::common::solve_vec(
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun k () Int)
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (select a i)))))
        (assert (distinct (select a k) (select b k)))
        (assert (distinct k 3))
        (check-sat)
    "#,
    );
    assert_eq!(
        results,
        vec!["unsat"],
        "symbolic ground contradiction must stay unsat"
    );
}

/// A valid universal in an implication antecedent is not itself a SAT
/// certificate for the containing formula. CEGQI used to strip the complete
/// implication, refute the universal's counterexample, and flip the empty
/// ground remainder to `sat`, losing the contradictory consequent.
#[test]
#[timeout(10000)]
fn nested_forall_cegqi_validity_never_certifies_whole_formula_sat() {
    let results = crate::common::solve_vec(
        r#"
        (set-logic ALL)
        (declare-const c Int)
        (assert
          (=> (forall ((x Int)) (=> (> x 0) (>= x 1)))
              (and (= c 0) (= c 1))))
        (check-sat)
    "#,
    );
    assert!(
        results
            .iter()
            .all(|result| result == "unsat" || result == "unknown"),
        "the unsatisfiable formula must never be certified sat: {results:?}"
    );
}
