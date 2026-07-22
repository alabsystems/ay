// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Combined-lane (DT+X) derived constructor-cycle soundness (stage-4 review
//! F1, #dt-model-recheck).
//!
//! The D0 e-graph pass closed the `min-pred` wrong-SAT on the lanes whose
//! `TheoryCombiner` hosts it — but ONE irrelevant declaration of another
//! theory re-routes the same instance to a sibling combined lane. The BV
//! routes bit-blast (no combiner hosts the pass, and no acyclicity depth
//! axioms exist without an arithmetic sort), so `min-pred` plus a single
//! unused-for-the-cycle BV constant answered `sat` with the same fabricated
//! `succ^6(zero)` model (z3: unsat). These tests pin the fix — the post-`Sat`
//! model-e-graph recheck in `solve_with_dt_axioms` plus D0 registration on
//! every combiner-backed DT+X lane — across the BV/LIA/LRA siblings, with sat
//! controls guarding against over-firing.

use ntest::timeout;

/// The min-pred core: `x5 != zero` plus a selector-chain ite forcing
/// `x5 = pred(pred(x5))` — tester instantiation closes the e-graph cycle
/// `x5 = succ(succ(x5))`; no well-founded value exists (z3-confirmed unsat).
fn min_pred_core() -> &'static str {
    r#"
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const x5 nat)
        (assert (not (= x5 zero)))
        (assert (= x5 (ite ((_ is succ) (ite ((_ is succ) x5) (pred x5) zero))
                           (pred (ite ((_ is succ) x5) (pred x5) zero))
                           zero)))
    "#
}

/// UNSAT (stage-4 review F1 repro, z3-confirmed): min-pred plus one
/// irrelevant BV declaration routes to the bit-blasting DT+BV lane, which
/// historically accepted the cycle (`sat` with `x5 = succ^6(zero)`).
/// MUST be `unsat` (never `sat`; `unknown` would be a completeness, not
/// soundness, regression — keep it at full strength).
#[test]
#[timeout(60_000)]
fn test_min_pred_with_bv_declaration_unsat() {
    let smt = format!(
        r#"
        (set-logic ALL)
        {}
        (declare-const v (_ BitVec 8))
        (assert (bvult v #xff))
        (check-sat)
    "#,
        min_pred_core()
    );
    let result = crate::common::solve(&smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "min-pred + one BV declaration (DT+BV lane) must never be sat (F1 wrong-SAT regression)"
    );
}

/// UNSAT: min-pred plus one irrelevant Int declaration (DT+LIA lane).
#[test]
#[timeout(60_000)]
fn test_min_pred_with_lia_declaration_unsat() {
    let smt = format!(
        r#"
        (set-logic ALL)
        {}
        (declare-const k Int)
        (assert (> k 0))
        (check-sat)
    "#,
        min_pred_core()
    );
    let result = crate::common::solve(&smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "min-pred + one Int declaration (DT+LIA lane) must never be sat"
    );
}

/// UNSAT: min-pred plus one irrelevant Real declaration (DT+LRA lane).
#[test]
#[timeout(60_000)]
fn test_min_pred_with_lra_declaration_unsat() {
    let smt = format!(
        r#"
        (set-logic ALL)
        {}
        (declare-const r Real)
        (assert (> r 0.5))
        (check-sat)
    "#,
        min_pred_core()
    );
    let result = crate::common::solve(&smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "min-pred + one Real declaration (DT+LRA lane) must never be sat"
    );
}

/// UNSAT: the direct two-constant constructor cycle on the DT+BV lane —
/// covers the derived-cycle rule without the ite/tester indirection.
#[test]
#[timeout(60_000)]
fn test_two_constant_cycle_with_bv_declaration_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const a nat)
        (declare-const b nat)
        (declare-const v (_ BitVec 8))
        (assert (bvult v #xff))
        (assert (= a (succ b)))
        (assert (= b (succ a)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "a = succ(b), b = succ(a) is a structural cycle on the DT+BV lane too"
    );
}

/// SAT control (DT+BV lane): an acyclic selector chain plus a BV constraint
/// must STAY sat — guards the recheck against over-firing / budget-degrading
/// genuinely satisfiable DT+BV instances.
#[test]
#[timeout(60_000)]
fn test_acyclic_chain_with_bv_declaration_stays_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const x nat)
        (declare-const v (_ BitVec 8))
        (assert (bvult v #x10))
        (assert (not (= x zero)))
        (assert (= (pred x) (succ zero)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "acyclic selector chain + BV constraint must stay sat on the DT+BV lane"
    );
}

/// SAT control (DT+BV lane): wrong-constructor selector application is
/// under-specified-but-fixed — `(pred zero)` may equal `(succ zero)`.
#[test]
#[timeout(60_000)]
fn test_wrong_ctor_selector_with_bv_declaration_stays_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const y nat)
        (declare-const v (_ BitVec 8))
        (assert (bvult v #xff))
        (assert (= y (pred zero)))
        (assert (= y (succ zero)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "(pred zero) is unconstrained by selector semantics; DT+BV lane must stay sat"
    );
}

/// Control (DT+LIA lane): a satisfiable acyclic chain plus an Int constraint
/// must NEVER answer unsat — the recheck's injected clauses are datatype
/// tautologies and cannot prune a genuine model. NOTE: this lane answers
/// `unknown` on both the branch AND main binaries (pre-existing DT+LIA
/// model-gate incompleteness: the acyclicity depth-axiom oracle rejects the
/// candidate model — the finite-list family gap), so `sat` cannot be pinned
/// yet; the assertion is the soundness half only. Tighten to `sat` when the
/// lane gap is fixed.
#[test]
#[timeout(60_000)]
fn test_acyclic_chain_with_lia_declaration_never_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const x nat)
        (declare-const k Int)
        (assert (> k 3))
        (assert (not (= x zero)))
        (assert (= (pred x) (succ zero)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_ne!(
        result.trim(),
        "unsat",
        "satisfiable acyclic chain + Int constraint must never answer unsat on the DT+LIA lane"
    );
}
