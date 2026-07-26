// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AUFLIA soundness gate tests for the #6846 processor benchmarks.
//!
//! These regressions exercise the Nelson-Oppen bridge path where free
//! UF-valued interface terms produce model equalities that may not converge
//! in the non-persistent split loop. The soundness property is that the solver
//! must never return `sat` on these `:status unsat` benchmarks.
//!
//! Root cause: the eager extension path (`TheoryExtension`) drops theory
//! conflicts when model equality terms lack SAT variable mappings
//! (`_ext_partial > 0`), causing Unknown/timeout instead of unsat. Fixed by
//! switching AUFLIA from eager to lazy pipeline and removing model equality
//! retry limits (#6846).

use ntest::timeout;

use super::helpers::{
    assert_not_sat, assert_not_unsat, assert_sat_validates, assert_scope_results,
    assert_unsat_with_proof, ProofExpectation,
};

/// Exact SMT-COMP add4 copy: `:status unsat` — small AUFLIA control (#3936).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn test_gate_qf_auflia_add4_not_sat() {
    assert_not_sat(include_str!("data/add4.smt2"));
}

/// Bounded add5 reduction: equal UF-backed affine indices must address the
/// same array cell, so pinning that cell to both 0 and 1 is UNSAT.
///
/// The exact industrial input remains in `data/add5.smt2` for benchmark
/// campaigns; this reduction preserves its AUFLIA bridge invariant without
/// making the default test suite solve the full processor formula.
#[test]
#[timeout(30_000)]
fn test_gate_qf_auflia_add5_reduced_not_sat_6846() {
    assert_not_sat(
        r#"
        (set-logic QF_AUFLIA)
        (declare-sort State 0)
        (declare-fun offset (State) Int)
        (declare-const a (Array Int Int))
        (declare-const s State)
        (declare-const t State)
        (assert (= (offset s) (offset t)))
        (assert (= (select a (+ (offset s) 1)) 0))
        (assert (= (select a (+ (offset t) 1)) 1))
        (check-sat)
    "#,
    );
}

/// Bounded add6 reduction: congruent array-producing and PC applications must
/// not be assigned contradictory results through nested UF arguments.
///
/// The exact campaign input remains in `data/add6.smt2`.
#[test]
#[timeout(30_000)]
fn test_gate_qf_auflia_add6_reduced_not_sat_6846() {
    assert_not_sat(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun icache (Int) (Array Int Int))
        (declare-fun pc (Int) Int)
        (declare-const s Int)
        (declare-const t Int)
        (assert (= s t))
        (assert (= (select (icache s) (pc (+ s 1))) 10))
        (assert (= (select (icache t) (pc (+ t 1))) 11))
        (check-sat)
    "#,
    );
}

// --- Consumer coverage: verification-consumer uses AUFLIA with arrays, UF, and LIA ---

/// SAT with model validation: array store/select with UF and LIA constraints.
/// Exercises the Nelson-Oppen bridge between array, EUF, and LIA solvers.
#[test]
#[timeout(30_000)]
fn test_gate_qf_auflia_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun f (Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= x 5))
        (assert (= y (f x)))
        (assert (= y 42))
        (assert (= (select (store a x y) x) 42))
        (check-sat)
    "#,
    );
}

/// UNSAT with proof envelope: array + UF + LIA contradiction.
#[test]
#[timeout(30_000)]
fn test_gate_qf_auflia_unsat_proof_envelope() {
    assert_unsat_with_proof(
        r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (assert (= (select (store a 0 10) 0) 10))
        (assert (not (= (select (store a 0 10) 0) 10)))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

/// Incremental push/pop scope: verification-consumer pattern with array constraints.
#[test]
#[timeout(30_000)]
fn test_gate_qf_auflia_incremental_scope() {
    assert_scope_results(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (assert (= x 10))
        (assert (= (select a x) 42))
        (check-sat)
        (push 1)
        (assert (not (= (select a 10) 42)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}

/// Bounded read7 reduction: after congruence identifies the two RF arrays,
/// `A = store(A, 3, 7)` forces `select(A, 3) = 7`, contradicting the explicit
/// read value 6.  The exact campaign input remains in `data/read7.smt2`.
#[test]
#[timeout(30_000)]
fn test_gate_qf_auflia_read7_reduced_not_sat_6846() {
    assert_not_sat(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun rf (Int) (Array Int Int))
        (declare-const before Int)
        (declare-const after Int)
        (assert (= before after))
        (assert (= (rf after) (store (rf before) 3 7)))
        (assert (= (select (rf before) 3) 6))
        (check-sat)
    "#,
    );
}

// --- #6820 storecomm+swap family coverage (34% gap vs Z3) ---

/// SMT-COMP storecomm (smallest instance): `:status sat` — model must validate.
/// storecomm family dominates the QF_AUFLIA performance gap (#6820).
#[test]
#[timeout(60_000)]
fn test_gate_qf_auflia_storecomm_small_not_unsat() {
    assert_not_unsat(include_str!("data/storecomm_small.smt2"));
}

/// SMT-COMP swap (smallest instance): `:status sat` — model must validate.
/// swap family is the second-largest contributor to the QF_AUFLIA gap (#6820).
#[test]
#[timeout(60_000)]
fn test_gate_qf_auflia_swap_small_not_unsat() {
    assert_not_unsat(include_str!("data/swap_small.smt2"));
}

// --- #alia-arrayext-neg-polarity wrong-UNSAT regression ---

/// `(assert (not (forall ((X0 Int)) (= (select b X0) (select cc X0)))))` is
/// trivially SAT (choose b != cc). The earlier bug added the extensional
/// consequence `(= b cc)` from a pointwise forall WITHOUT tracking polarity:
/// under the top-level `not` the forall is NEGATED, so `(= b cc)` is NOT
/// entailed — adding it made the inner forall true by congruence, flipping the
/// `(not forall)` to false and reporting a spurious UNSAT. `add_quantified_
/// array_extensionality_equalities` now only collects pointwise foralls at
/// POSITIVE polarity. z3 AND cvc5 report sat.
#[test]
#[timeout(10_000)]
fn test_gate_alia_pointwise_forall_neg_polarity_not_unsat() {
    assert_scope_results(
        r#"
        (set-logic ALIA)
        (declare-const b (Array Int Int))
        (declare-const cc (Array Int Int))
        (assert (not (forall ((X0 Int)) (= (select b X0) (select cc X0)))))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// The genuine wrong-SAT this pass was built for must STAY refuted: a top-level
/// POSITIVE pointwise forall `(forall i. a[i]=b[i])` together with `(not (= a b))`
/// is UNSAT by extensionality. The polarity restriction keeps the positive
/// occurrence collected. z3 AND cvc5 report unsat.
#[test]
#[timeout(10_000)]
fn test_gate_alia_pointwise_forall_pos_polarity_still_unsat() {
    assert_scope_results(
        r#"
        (set-logic ALIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (forall ((X0 Int)) (= (select a X0) (select b X0))))
        (assert (not (= a b)))
        (check-sat)
    "#,
        &["unsat"],
    );
}

// --- #arrayext-or-positive-over-injection wrong-UNSAT regression ---

/// A positive-polarity pointwise forall that sits under a TOP-LEVEL `(or ...)`
/// is NOT an asserted premise — the disjunction can be satisfied by the OTHER
/// disjunct (`p`) with `a != b`. The earlier bug injected the extensional
/// consequence `(= a b)` anyway (positive NNF polarity but under a disjunction),
/// which combined with the sibling `(not (= (select a k) (select b k)))` forced
/// `(select a k) = (select b k)` by congruence and reported a spurious UNSAT.
/// `collect_plain_pointwise_foralls` now requires the forall to be a top-level
/// CONJUNCT (positive AND not under any disjunction). The SOUNDNESS property is
/// that ay must NOT report `unsat` here (z3 AND cvc5 report sat); ay's quantifier
/// engine cannot construct the witnessing `a != b` model so it soundly returns
/// `unknown`, which `assert_not_unsat` accepts. Before the fix it reported a
/// spurious `unsat`.
#[test]
#[timeout(10_000)]
fn test_gate_alia_pointwise_forall_under_or_not_unsat() {
    assert_not_unsat(
        r#"
        (set-logic ALIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const k Int)
        (declare-const p Bool)
        (assert (not (= (select a k) (select b k))))
        (assert (or (forall ((i Int)) (= (select a i) (select b i))) p))
        (check-sat)
    "#,
    );
}

/// Companion: the forall under the consequent of an implication is the same
/// trap (`(=> A B)` ≡ `(or (not A) B)`), so `B`'s pointwise forall is NOT an
/// unconditional premise. ay must NOT report `unsat` (z3 AND cvc5 report sat);
/// it soundly returns `unknown`.
#[test]
#[timeout(10_000)]
fn test_gate_alia_pointwise_forall_under_implication_consequent_not_unsat() {
    assert_not_unsat(
        r#"
        (set-logic ALIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const k Int)
        (declare-const q Bool)
        (assert (not (= (select a k) (select b k))))
        (assert (=> q (forall ((i Int)) (= (select a i) (select b i)))))
        (check-sat)
    "#,
    );
}

/// Adversarial control for the OR fix: a top-level CONJUNCT pointwise forall is
/// STILL collected even when an UNRELATED disjunction is also asserted. Here the
/// forall is a direct conjunct (not under the `or`), so `(= a b)` is genuinely
/// entailed and `(not (= a b))` makes it UNSAT — the `under_disj` guard must not
/// over-suppress a sibling top-level forall. z3 reports unsat.
#[test]
#[timeout(10_000)]
fn test_gate_alia_pointwise_forall_conjunct_with_unrelated_or_still_unsat() {
    assert_scope_results(
        r#"
        (set-logic ALIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (forall ((i Int)) (= (select a i) (select b i))))
        (assert (not (= a b)))
        (assert (or p q))
        (check-sat)
    "#,
        &["unsat"],
    );
}
