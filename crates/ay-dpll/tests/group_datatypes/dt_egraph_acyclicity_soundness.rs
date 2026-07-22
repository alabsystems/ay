// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Derived constructor-cycle soundness for recursive datatypes (D0 e-graph
//! pass, `DESIGN_lazy_dt.md`; M1 `min-pred` wrong-SAT).
//!
//! The eager DtAx lane's occurs-check only sees *asserted* equalities; a
//! well-foundedness cycle closed through EUF merges of tester-instantiated
//! constructor shapes (axiom (C)) was invisible, and the model gates could
//! not reject the resulting non-representable "model" (structural resolution
//! diverges on a cyclic value), producing a wrong SAT. The D0 pass
//! (`ay_dt::DtEgraphPass`, run from `TheoryCombiner::check()` at the
//! Nelson-Oppen fixpoint) now derives the clash/cycle conflict inside the
//! solver, so these instances answer `unsat`.

use ntest::timeout;

/// UNSAT (M1 minimal repro, z3-confirmed): `x5 != zero` plus a selector-chain
/// ite forcing `x5 = pred(pred(x5))`. Instantiating `nat`'s testers yields
/// `x5 = succ(pred x5)`, `pred x5 = succ(pred (pred x5))`, i.e. an e-graph
/// constructor-argument cycle `x5 = succ(succ(x5))` — no well-founded value
/// exists. Historically answered `sat` with a fabricated `succ^6(zero)` model.
/// MUST be `unsat` (never `sat`; `unknown` would be a completeness, not
/// soundness, regression — keep it at full strength).
#[test]
#[timeout(60_000)]
fn test_min_pred_derived_selector_cycle_unsat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const x5 nat)
        (assert (not (= x5 zero)))
        (assert (= x5 (ite ((_ is succ) (ite ((_ is succ) x5) (pred x5) zero))
                           (pred (ite ((_ is succ) x5) (pred x5) zero))
                           zero)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "min-pred shape: x5 = pred(pred(x5)) with x5 != zero forces the \
         e-graph cycle x5 = succ(succ(x5)) (wrong-SAT regression, M1)"
    );
}

/// UNSAT: the same derived cycle asserted directly through two constants —
/// covers the two-class cycle regardless of ite lifting.
#[test]
#[timeout(60_000)]
fn test_two_constant_constructor_cycle_unsat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const a nat)
        (declare-const b nat)
        (assert (= a (succ b)))
        (assert (= b (succ a)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "a = succ(b) and b = succ(a) is a structural cycle"
    );
}

/// SAT control: an acyclic selector chain must STAY sat and produce the
/// standard model `x = succ(succ(zero))` (guards against the cycle rule
/// over-firing on acyclic chains).
#[test]
#[timeout(60_000)]
fn test_selector_chain_control_stays_sat_with_standard_model() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const x nat)
        (assert (not (= x zero)))
        (assert (= (pred x) (succ zero)))
        (check-sat)
        (get-value (x))
    "#;
    let result = crate::common::solve(smt);
    let verdict = crate::common::sat_result(&result);
    assert_eq!(
        verdict,
        Some("sat"),
        "acyclic selector chain must stay sat; got:\n{result}"
    );
    assert!(
        result.contains("(succ (succ zero))"),
        "standard model expected: x = succ(succ(zero)); got:\n{result}"
    );
}

/// SAT control: a selector applied to a WRONG-constructor value is
/// under-specified-but-fixed (SMT-LIB total selector semantics) — the solver
/// may pin `(pred zero)` to any nat, so this must remain sat.
#[test]
#[timeout(60_000)]
fn test_wrong_constructor_selector_underspecification_stays_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const y nat)
        (assert (= y (pred zero)))
        (assert (= y (succ zero)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "(pred zero) is unconstrained by selector semantics and may equal (succ zero)"
    );
}

/// SAT control: self-referential selector identity on the RIGHT constructor —
/// `x = succ(pred x)` alone (with `x != zero`) is satisfiable by every
/// non-zero nat; the cycle rule must not fire on `x ~ succ(pred x)` since the
/// constructor-argument edge x -> pred(x) leads to a class with no
/// constructor application.
#[test]
#[timeout(60_000)]
fn test_constructor_identity_on_own_selector_stays_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
        (declare-const x nat)
        (assert (not (= x zero)))
        (assert (= x (succ (pred x))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "x = succ(pred x) holds for every succ-built x"
    );
}
