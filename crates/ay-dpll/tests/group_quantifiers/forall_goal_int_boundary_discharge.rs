// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Discharge of a fully-quantified per-element invariant across an inductive
//! "push"/grow step (#forall-goal-boundary).
//!
//! The motivating obligation is the loop invariant
//! `forall i. i < db.len() ==> entailed(db[i])` MAINTAINED when one element is
//! appended: the goal's index range extends by one (`< (+ len 1)`) and the new
//! boundary index `len` reads the just-pushed element. Discharging the GOAL
//! skolemizes its negation to a fresh witness `k` bounded `... < (+ len 1)`;
//! refuting the new-element case requires pinning `k = len` so the congruence
//! closure can read the appended element. Over the integers the skolemizer
//! surfaces that bound as `(not (<= (+ len 1) k))` (and the lower bound as
//! `(not (<= k (- len 1)))`) — strict bounds in disguise — and ay-lia only
//! EXPORTS an implied equality from POSITIVE non-strict two-sided bounds, so
//! `k` was never pinned to `len` and the universal stayed Unknown / Sat.
//!
//! `tighten_ground_int_strict_bounds` (run after Skolemization, before the
//! ground solve) normalizes every ground integer strict order atom to the
//! equivalent positive `<=` form, feeding the existing (sound) export so the
//! boundary case closes.
//!
//! SOUNDNESS: the normalization is an exact integer equivalence, so it can only
//! turn a previously-Unknown VALID goal into Unsat — never an invalid one. The
//! `*_false_control_*` tests assert that a NON-valid universal (the appended
//! element is not entailed, or some in-range element violates the predicate)
//! must NOT be proved (stays sat/unknown); a regression to `unsat` there would
//! be a catastrophic false-Verified.

use ntest::timeout;
use std::collections::BTreeSet;

use ay_core::term::TermData;
use ay_core::{AletheRule, ProofStep, Symbol, TermId};

fn solve_with_proofs(smt: &str) -> (Vec<String>, ay_dpll::Executor) {
    let commands = ay_frontend::parse(smt).expect("proof-mode boundary input must parse");
    let mut exec = ay_dpll::Executor::new();
    exec.set_produce_proofs(true);
    let results = exec
        .execute_all(&commands)
        .expect("proof-mode boundary input must execute");
    (results, exec)
}

fn step_derives_empty(step: &ProofStep) -> bool {
    match step {
        ProofStep::Resolution { clause, .. }
        | ProofStep::TheoryLemma { clause, .. }
        | ProofStep::Step { clause, .. } => clause.is_empty(),
        _ => false,
    }
}

fn is_skolem_antisymmetry_split(exec: &ay_dpll::Executor, term: TermId) -> bool {
    let TermData::App(Symbol::Named(or_name), disjuncts) = exec.terms().get(term) else {
        return false;
    };
    if or_name != "or" || disjuncts.len() != 3 {
        return false;
    }
    let TermData::App(Symbol::Named(eq_name), operands) = exec.terms().get(disjuncts[0]) else {
        return false;
    };
    eq_name == "="
        && operands.len() == 2
        && operands.iter().any(|&operand| {
            matches!(exec.terms().get(operand), TermData::Var(name, _)
                if exec.terms().is_skolem_symbol(name))
        })
}

fn assert_proof_authority(exec: &ay_dpll::Executor, label: &str) {
    let proof = exec
        .last_proof()
        .expect("proof mode must retain a proof for the boundary UNSAT");
    // Pin both internal rule validity and source authority. The strict checker
    // validates every rule; the problem-scoped exporter independently rejects
    // any reachable Assume that is not an authored source premise.
    ay_proof::check_proof_strict(proof, exec.terms())
        .expect("boundary UNSAT proof must pass the strict checker");
    let alethe = exec
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("boundary UNSAT must retain a problem-scoped proof")
        .expect("boundary UNSAT problem-scoped Alethe export must succeed");
    assert!(
        alethe.contains(":rule la_disequality"),
        "{label}: Alethe proof must export the arithmetic antisymmetry lemma"
    );
    assert!(
        alethe.contains(":rule sko_forall") && alethe.contains("(anchor :step"),
        "{label}: Alethe proof must expand the certified Skolem step in a scoped anchor"
    );
    assert!(
        !alethe
            .lines()
            .any(|line| line.starts_with("(declare-fun sk!")),
        "{label}: the certified Skolem witness must render as choice, not a free declaration"
    );
    assert!(
        !alethe.contains(":rule trust"),
        "{label}: load-bearing Alethe proof must not contain trust: {alethe}"
    );

    // Audit only the transitive dependency cone of the empty clause. Orphaned
    // bookkeeping steps cannot authorize a verdict and are intentionally
    // irrelevant. Problem-source authority itself is enforced by the
    // production problem-scoped exporter above; `exec.context().assertions`
    // contains post-preprocessing terms and is not an authority source.
    let mut reachable = vec![false; proof.steps.len()];
    let mut stack = Vec::new();
    for (idx, step) in proof.steps.iter().enumerate() {
        if step_derives_empty(step) {
            reachable[idx] = true;
            stack.push(idx);
        }
    }
    while let Some(idx) = stack.pop() {
        let mut push = |premise: ay_core::ProofId| {
            let premise = premise.0 as usize;
            assert!(
                premise < proof.steps.len(),
                "{label}: reachable proof step references missing premise {premise}"
            );
            if !reachable[premise] {
                reachable[premise] = true;
                stack.push(premise);
            }
        };
        match &proof.steps[idx] {
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                push(*clause1);
                push(*clause2);
            }
            ProofStep::Step { premises, .. } => {
                for &premise in premises {
                    push(premise);
                }
            }
            _ => {}
        }
    }

    let mut tracked_split_terms = BTreeSet::new();
    for (idx, step) in proof.steps.iter().enumerate() {
        if !reachable[idx] {
            continue;
        }
        match step {
            ProofStep::Step {
                rule: AletheRule::LaDisequality,
                clause,
                ..
            } if clause.len() == 1 && is_skolem_antisymmetry_split(exec, clause[0]) => {
                tracked_split_terms.insert(clause[0]);
            }
            _ => {}
        }
    }
    assert!(
        !tracked_split_terms.is_empty(),
        "{label}: reachable proof must contain the tracked Skolem antisymmetry la_disequality lemma"
    );
    assert!(
        proof.steps.iter().all(|step| !matches!(step,
            ProofStep::Assume(term) if tracked_split_terms.contains(term))),
        "{label}: antisymmetry split must be a theory lemma, never an Assume"
    );
}

fn assert_unsat_with_certified_proof(smt: &str, label: &str) {
    // Exercise proof mode directly as well as the default no-proof API. The
    // latter internally corroborates non-string-Seq UNSAT under proof mode, but
    // this direct lane also pins proof construction and checking itself.
    let (proof_results, exec) = solve_with_proofs(smt);
    assert!(
        proof_results.iter().any(|r| r == "unsat"),
        "{label} (proof mode): expected unsat, got {proof_results:?}"
    );
    assert!(
        !proof_results.iter().any(|r| r == "sat"),
        "{label} (proof mode): must NOT return sat, got {proof_results:?}"
    );
    assert_proof_authority(&exec, label);

    assert_unsat(smt, label);
}

fn assert_unsat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "{label}: expected unsat (valid per-element invariant should discharge), got {results:?}"
    );
    assert!(
        !results.iter().any(|r| r == "sat"),
        "{label}: must NOT return sat (the obligation is genuinely UNSAT), got {results:?}"
    );
}

fn assert_not_unsat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "{label}: must NOT return unsat (the universal is NOT valid — a false \
         Verified here is a soundness catastrophe), got {results:?}"
    );

    // The tracked Skolem antisymmetry split is proof-mode-only, so every false
    // control must also run there: a false UNSAT in this lane would be
    // catastrophic.
    let (proof_results, _) = solve_with_proofs(smt);
    assert!(
        !proof_results.iter().any(|r| r == "unsat"),
        "{label} (proof mode): must NOT return unsat, got {proof_results:?}"
    );
}

// ===========================================================================
// VALID forall-goals that MUST now discharge (Unsat).
// ===========================================================================

/// The boundary case in isolation: a skolem `k` with `(<= len k)` and
/// `(< k (+ len 1))` must be pinned to `len` so the just-appended element
/// `seq.nth db2 len = e` (entailed) closes `not (entailed (seq.nth db2 k))`.
#[test]
#[timeout(20000)]
fn seq_boundary_index_pin_discharges_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun entailed (Int) Bool)
        (declare-const db2 (Seq Int))
        (declare-const e Int)
        (declare-const len Int)
        (assert (>= len 0))
        (assert (= (seq.nth db2 len) e))
        (assert (entailed e))
        (assert (not (forall ((i Int))
            (=> (and (<= len i) (< i (+ len 1))) (entailed (seq.nth db2 i))))))
        (check-sat)
    "#;
    assert_unsat_with_certified_proof(smt, "seq_boundary_index_pin");
}

/// Same boundary pin over an SMT array carrier (`select` / opaque element fact).
#[test]
#[timeout(20000)]
fn array_boundary_index_pin_discharges_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun entailed (Int) Bool)
        (declare-const db2 (Array Int Int))
        (declare-const e Int)
        (declare-const len Int)
        (assert (>= len 0))
        (assert (= (select db2 len) e))
        (assert (entailed e))
        (assert (not (forall ((i Int))
            (=> (and (<= len i) (< i (+ len 1))) (entailed (select db2 i))))))
        (check-sat)
    "#;
    assert_unsat(smt, "array_boundary_index_pin");
}

/// Full per-element invariant maintained across a push, opaque-Seq encoding:
/// inductive hypothesis over `[0, len)`, new element `e` at index `len`, goal
/// over the extended range `[0, len+1)`. Requires both the E-matched IH (for
/// `k < len`) and the boundary pin (for `k = len`).
#[test]
#[timeout(20000)]
fn seq_per_element_invariant_across_push_discharges_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun entailed (Int) Bool)
        (declare-const db2 (Seq Int))
        (declare-const e Int)
        (declare-const len Int)
        (assert (>= len 0))
        (assert (= (seq.nth db2 len) e))
        (assert (entailed e))
        (assert (forall ((i Int))
            (=> (and (<= 0 i) (< i len)) (entailed (seq.nth db2 i)))))
        (assert (not (forall ((i Int))
            (=> (and (<= 0 i) (< i (+ len 1))) (entailed (seq.nth db2 i))))))
        (check-sat)
    "#;
    assert_unsat(smt, "seq_per_element_invariant_across_push");
}

/// The same per-element invariant over the structural `seq.++` append encoding
/// of `Vec::push` (`db2 = db ++ unit(e)`), IH over the old `db`.
#[test]
#[timeout(20000)]
fn seq_append_per_element_invariant_discharges_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun entailed (Int) Bool)
        (declare-const db (Seq Int))
        (declare-const e Int)
        (assert (forall ((i Int))
            (=> (and (<= 0 i) (< i (seq.len db))) (entailed (seq.nth db i)))))
        (assert (entailed e))
        (assert (not (forall ((i Int))
            (=> (and (<= 0 i) (< i (seq.len (seq.++ db (seq.unit e)))))
                (entailed (seq.nth (seq.++ db (seq.unit e)) i))))))
        (check-sat)
    "#;
    assert_unsat(smt, "seq_append_per_element_invariant");
}

/// The boundary pin when the upper bound is a SEPARATE variable `new_len` pinned
/// by an asserted GROUND equation `(= new_len (+ len 1))` — instead of the inline
/// `(+ len 1)` of `seq_boundary_index_pin_discharges_unsat`. The range
/// `[len, new_len) = [len, len+1) = {len}`; `seq.nth db2 len = e` and `entailed e`,
/// so the universal holds and its negation is UNSAT. Requires folding the ground
/// length equation into the strict boundary atom so `(< k new_len)` resolves to
/// the pinnable `(<= k len)` (#ground-length-equation). Without the fold this
/// query returns a spurious `sat`.
#[test]
#[timeout(20000)]
fn seq_boundary_index_pin_separate_len_var_discharges_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun entailed (Int) Bool)
        (declare-const db2 (Seq Int))
        (declare-const e Int)
        (declare-const len Int)
        (declare-const new_len Int)
        (assert (>= len 0))
        (assert (= new_len (+ len 1)))
        (assert (= (seq.nth db2 len) e))
        (assert (entailed e))
        (assert (not (forall ((i Int))
            (=> (and (<= len i) (< i new_len)) (entailed (seq.nth db2 i))))))
        (check-sat)
    "#;
    assert_unsat_with_certified_proof(smt, "seq_boundary_index_pin_separate_len_var");
}

// ===========================================================================
// FALSE controls — the universal is NOT valid and MUST stay unproved.
// ===========================================================================

/// SOUNDNESS GATE for the ground-length-equation fold. Same separate-`new_len`
/// shape as `seq_boundary_index_pin_separate_len_var_discharges_unsat`, but the
/// appended element `e` is NOT asserted `entailed`, so the grown invariant is
/// FALSE at the boundary index `len`. Folding `new_len = len + 1` still pins
/// `k = len`, but the predicate is unconstrained there, so the negation is
/// satisfiable and MUST NOT be proved unsat — a regression to `unsat` here would
/// be a catastrophic false-Verified.
#[test]
#[timeout(20000)]
fn false_control_separate_len_var_unentailed_new_element_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun entailed (Int) Bool)
        (declare-const db2 (Seq Int))
        (declare-const e Int)
        (declare-const len Int)
        (declare-const new_len Int)
        (assert (>= len 0))
        (assert (= new_len (+ len 1)))
        (assert (= (seq.nth db2 len) e))
        (assert (not (forall ((i Int))
            (=> (and (<= len i) (< i new_len)) (entailed (seq.nth db2 i))))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "false_control_separate_len_var_unentailed_new_element");
}

/// The appended element `e` is NOT entailed, so the grown invariant is FALSE at
/// the boundary index. The negation is satisfiable — must NOT be proved unsat.
#[test]
#[timeout(20000)]
fn false_control_unentailed_new_element_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun entailed (Int) Bool)
        (declare-const db2 (Seq Int))
        (declare-const e Int)
        (declare-const len Int)
        (assert (>= len 0))
        (assert (= (seq.nth db2 len) e))
        (assert (forall ((i Int))
            (=> (and (<= 0 i) (< i len)) (entailed (seq.nth db2 i)))))
        (assert (not (forall ((i Int))
            (=> (and (<= 0 i) (< i (+ len 1))) (entailed (seq.nth db2 i))))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "false_control_unentailed_new_element");
}

/// An in-range element violates the predicate (`db[1] < 0` while the goal
/// claims `forall i < len+1. db[i] >= 0`). The universal is false; the
/// normalization must not let it be spuriously proved.
#[test]
#[timeout(20000)]
fn false_control_in_range_violation_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const db (Seq Int))
        (declare-const len Int)
        (assert (= len (seq.len db)))
        (assert (>= len 2))
        (assert (< (seq.nth db 1) 0))
        (assert (not (forall ((i Int))
            (=> (and (<= 0 i) (< i (+ len 1))) (>= (seq.nth db i) 0)))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "false_control_in_range_violation");
}

/// Boundary-only false control: the new element is not asserted entailed, so the
/// single-index `forall i in [len, len+1)` goal is not valid.
#[test]
#[timeout(20000)]
fn false_control_boundary_only_unentailed_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun entailed (Int) Bool)
        (declare-const db2 (Seq Int))
        (declare-const e Int)
        (declare-const len Int)
        (assert (>= len 0))
        (assert (= (seq.nth db2 len) e))
        (assert (not (forall ((i Int))
            (=> (and (<= len i) (< i (+ len 1))) (entailed (seq.nth db2 i))))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "false_control_boundary_only_unentailed");
}
