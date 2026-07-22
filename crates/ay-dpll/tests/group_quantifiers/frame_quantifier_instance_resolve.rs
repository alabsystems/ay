// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Sound ground re-solve certification for array-indexing FRAME quantifiers
//! (#mbqi-completeness Q2).
//!
//! A universal whose Int binder INDEXES an array/seq — `forall k. P(a[k])`, the
//! shape of every Verus frame / postcondition-preservation obligation — is
//! flagged MBQI-unsafe (a candidate ground SAT cannot be trusted for such a
//! binder). The soundness gate in `result_mapping` therefore refuses to trust a
//! ground UNSAT that rests on its instances UNLESS the refutation can be
//! independently reconstructed. The prior reconstruction (`unsat_from_direct_
//! instance_clash`) only recognised a SYNTACTIC complementary literal pair, so a
//! genuine UNSAT that needs the solver to (a) case-split the finite-domain-
//! expanded / skolemized negated goal `(or (< a[0] 0) (< a[1] 0) (< a[2] 0))`
//! against several instances, or (b) close a pair complementary only under
//! LIA/EUF (`(< a[0] 0)` vs the instance `(<= 0 a[0])`), was wrongly degraded to
//! `unknown (quantifier-unhandled)`. These are exactly the frame conditions of
//! the VerifyThis benchmarks (swap/update preserve a per-element invariant).
//!
//! The fix re-solves the GROUND conjunction of (quantifier-free core conjuncts +
//! sound conjunctive-forall instances). Each element is entailed by the original
//! problem, so a ground UNSAT certifies the reported UNSAT; the certification
//! never rides CEGQI's valid->SAT flip and can never manufacture a wrong UNSAT.
//!
//! SOUNDNESS: the `false_control_*` tests are the gate. Each is a query whose
//! answer is genuinely SAT (a real counterexample exists, or the universal is
//! not entailed) — a regression to `unsat` there would be a catastrophic
//! false-Verified. The array-extensionality control `(forall i. a[i]=b[i]) ∧
//! a[0]=b[0]` (satisfiable) must never be certified UNSAT.

use ntest::timeout;

fn assert_unsat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "{label}: expected unsat (valid array-index frame invariant should \
         discharge), got {results:?}"
    );
    assert!(
        !results.iter().any(|r| r == "sat"),
        "{label}: must NOT return sat (the obligation is genuinely UNSAT), \
         got {results:?}"
    );
}

fn assert_not_unsat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "{label}: must NOT return unsat (the query is genuinely SAT — a false \
         Verified here is a soundness catastrophe), got {results:?}"
    );
}

// ===========================================================================
// VALID array-index frame goals that MUST now discharge (Unsat).
// ===========================================================================

/// Minimal shape: an array-indexing universal `forall k. a[k] >= 0` plus a
/// ground violation `a[0] < 0`. Instantiating at k:=0 gives `(<= 0 a[0])`, which
/// is LIA-complementary to `(< a[0] 0)` — not a syntactic Not-pair, so the old
/// syntactic clash check missed it and returned unknown.
#[test]
#[timeout(20000)]
fn array_index_forall_ground_violation_discharges_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (assert (forall ((k Int)) (>= (select a k) 0)))
        (assert (< (select a 0) 0))
        (check-sat)
    "#;
    assert_unsat(smt, "array_index_forall_ground_violation");
}

/// Bounded frame preserved across a functional update. `snew = s.update(1,val)`
/// with `val >= 0` and concrete `s[0..3]`; the goal `forall j<3. snew[j] >= 0`
/// negates to a bounded exists that finite-domain-expands to a DISJUNCTION over
/// {0,1,2}, which must be case-split against the update-axiom instances.
#[test]
#[timeout(20000)]
fn array_frame_invariant_preserved_across_update_discharges_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun s () (Array Int Int))
        (declare-fun snew () (Array Int Int))
        (declare-fun val () Int)
        (assert (= (select s 0) 10))
        (assert (= (select s 1) 20))
        (assert (= (select s 2) 30))
        (assert (>= val 0))
        (assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k)))))
        (assert (exists ((j Int)) (and (<= 0 j) (< j 3) (< (select snew j) 0))))
        (check-sat)
    "#;
    assert_unsat(smt, "array_frame_invariant_preserved_across_update");
}

/// The full Verus-faithful shape: the skolemized `u64` witness carries BOTH the
/// tight goal bound `(< j 3)` AND the type range guard `(< j 2^64)`. The huge
/// bound must not defeat the finite-domain expansion nor the certification.
#[test]
#[timeout(20000)]
fn array_frame_u64_guarded_witness_discharges_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun s () (Array Int Int))
        (declare-fun snew () (Array Int Int))
        (declare-fun val () Int)
        (assert (= (select s 0) 10))
        (assert (= (select s 1) 20))
        (assert (= (select s 2) 30))
        (assert (>= val 0))
        (assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k)))))
        (assert (exists ((j Int))
            (and (>= j 0) (< j 18446744073709551616) (< j 3) (< (select snew j) 0))))
        (check-sat)
    "#;
    assert_unsat(smt, "array_frame_u64_guarded_witness");
}

// ===========================================================================
// FALSE controls — genuinely SAT queries that MUST stay unproved (soundness).
// ===========================================================================

/// Array-extensionality control (ay #8729 / Z3 #6303 wrong-SAT concern, dual):
/// `(forall i. a[i]=b[i]) ∧ a[0]=b[0]` is satisfiable (both instance and ground
/// fact are positive equalities — no contradiction). The certifier's ground
/// re-solve of `{a[0]=b[0], a[t]=b[t]...}` is SAT, so it must NOT certify UNSAT.
#[test]
#[timeout(20000)]
fn false_control_ext_eq_weak_fact_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (forall ((i Int)) (= (select a i) (select b i))))
        (assert (= (select a 0) (select b 0)))
        (check-sat)
    "#;
    assert_not_unsat(smt, "false_control_ext_eq_weak_fact");
}

/// Non-entailed goal: `forall k<3. a[k] >= 0` does not entail `a[j] > 100` for a
/// bounded `j` — `a[j]` may be any value in `[0, 100]`. The negated goal is
/// satisfiable and must not be proved unsat.
#[test]
#[timeout(20000)]
fn false_control_nonentailed_goal_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (assert (forall ((k Int)) (=> (and (<= 0 k) (< k 3)) (>= (select a k) 0))))
        (assert (exists ((j Int)) (and (<= 0 j) (< j 3) (> (select a j) 100))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "false_control_nonentailed_goal");
}

/// GENUINE counterexample: the update writes `-1` at index 0, so the frame
/// `forall j<2. anew[j] >= 0` is FALSE at j=0. The query is SAT (witness j=0) and
/// must not be certified unsat — the certifier's instance at j=0 gives
/// `anew[0] = -1`, and the ground re-solve is SAT.
#[test]
#[timeout(20000)]
fn false_control_genuine_frame_violation_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun anew () (Array Int Int))
        (assert (= (select a 0) 5))
        (assert (= (select a 1) 7))
        (assert (forall ((k Int)) (= (select anew k) (ite (= k 0) (- 1) (select a k)))))
        (assert (exists ((j Int)) (and (<= 0 j) (< j 2) (< (select anew j) 0))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "false_control_genuine_frame_violation");
}

/// Unconstrained update value: `snew = s.update(1,val)` with `val` NOT asserted
/// non-negative. `snew[1] = val` can be negative, so `exists j<3. snew[j] < 0` is
/// SAT (witness j=1). Must not be proved unsat.
#[test]
#[timeout(20000)]
fn false_control_unconstrained_update_value_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun s () (Array Int Int))
        (declare-fun snew () (Array Int Int))
        (declare-fun val () Int)
        (assert (= (select s 0) 10))
        (assert (= (select s 1) 20))
        (assert (= (select s 2) 30))
        (assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k)))))
        (assert (exists ((j Int)) (and (<= 0 j) (< j 3) (< (select snew j) 0))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "false_control_unconstrained_update_value");
}

// ===========================================================================
// BOOL-BINDER completeness: a MIXED `forall (b Bool) (k Int) …` whose k INDEXES
// an array (MBQI-unsafe) previously skipped the WHOLE forall in the direct-
// instance-clash reconstruction (the `Sort::Bool` binder hit `continue 'forall`),
// so a refutation that needs a specific Bool case degraded to unknown. A Bool
// binder ranges over exactly {true, false}, so instantiating at both is sound
// (each a consequence) AND complete for the binder; the reconstruction can only
// ADD genuine UNSATs (it never emits sat), so there is no wrong-verdict hazard.
// ===========================================================================

/// Mixed `forall (b Bool) (k Int). p(b, a[k])` (array-index unsafe) + a ground
/// violation `¬p(false, a[0])`. The refutation needs the `b := false` instance,
/// which the old Bool-skip never produced — so this returned unknown. Now the
/// `b := false, k := 0` instance `p(false, a[0])` is a syntactic complement of
/// the ground literal ⇒ genuine UNSAT.
#[test]
#[timeout(20000)]
fn bool_binder_forall_ground_violation_discharges_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun p (Bool Int) Bool)
        (assert (forall ((b Bool) (k Int)) (p b (select a k))))
        (assert (not (p false (select a 0))))
        (check-sat)
    "#;
    assert_unsat(smt, "bool_binder_forall_ground_violation");
}

/// SOUNDNESS control: the same shape but the universal only constrains the
/// `b = true` leg (`(=> b (p b a[k]))`), so `¬p(false, a[0])` is about the
/// UNCONSTRAINED `b = false` case and the query is genuinely SAT. Adding the
/// (now-produced) `b := false` instance must NOT manufacture an unsat — its
/// antecedent is false, so the instance is vacuously true.
#[test]
#[timeout(20000)]
fn false_control_bool_binder_unconstrained_leg_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun p (Bool Int) Bool)
        (assert (forall ((b Bool) (k Int)) (=> b (p b (select a k)))))
        (assert (not (p false (select a 0))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "false_control_bool_binder_unconstrained_leg");
}
