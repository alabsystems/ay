// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! D1 lazy tester/selector propagation soundness (`DESIGN_lazy_dt.md` stage
//! D1, `ay_dt::DtLazyPropagator`, hosted by `TheoryCombiner` on the
//! `array_euf`/DtAx lane).
//!
//! Each shape here forces a constructor commitment through a DERIVED e-graph
//! merge (an equality chain, not a syntactic constructor equality) and then
//! contradicts (unsat cases) or agrees with (sat controls) a tester/selector
//! consequence. The unsat cases must stay `unsat` and — critically — the sat
//! controls must stay `sat`: an over-firing propagation rule (wrong polarity,
//! wrong-constructor selector, cross-datatype tester) would prune real models
//! and surface here as `unsat`/`unknown` on the controls.

use ntest::timeout;

/// Tester evaluation through a derived two-step merge: `x = y`,
/// `y = stack(a, empty)` commits x's class to `stack`; asserting
/// `(_ is empty) x` contradicts constructor distinctness. MUST be unsat.
#[test]
#[timeout(60_000)]
fn test_derived_merge_tester_conflict_unsat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (declare-const a blk)
        (assert (= x y))
        (assert (= y (stack a empty)))
        (assert ((_ is empty) x))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "x ~ stack(...) contradicts is-empty(x)"
    );
}

/// Sat control for the tester rule: the SAME commitment with the AGREEING
/// tester must stay sat (guards against wrong-polarity tester emission).
#[test]
#[timeout(60_000)]
fn test_derived_merge_tester_agreement_stays_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (declare-const a blk)
        (assert (= x y))
        (assert (= y (stack a empty)))
        (assert ((_ is stack) x))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "sat", "agreeing tester must not be pruned");
}

/// Selector evaluation through a derived merge: `x ~ stack(a, empty)` forces
/// `top(x) = a`; the asserted disequality contradicts it. MUST be unsat.
#[test]
#[timeout(60_000)]
fn test_derived_merge_selector_conflict_unsat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (declare-const a blk)
        (assert (= x y))
        (assert (= y (stack a empty)))
        (assert (not (= (top x) a)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "x ~ stack(a, ...) forces top(x) = a"
    );
}

/// Total-selector semantics control: a WRONG-constructor selector application
/// is unconstrained, so `top(x) != a` with `x ~ empty` must stay sat (guards
/// against the selector rule firing across constructors).
#[test]
#[timeout(60_000)]
fn test_wrong_constructor_selector_stays_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (declare-const a blk)
        (assert (= x y))
        (assert (= y empty))
        (assert (not (= (top x) a)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "selector of a non-matching constructor is unconstrained (total semantics)"
    );
}

/// Tester exclusion across a merged, constructor-free class: two POSITIVE
/// testers for distinct constructors on `x ~ y`. MUST be unsat.
#[test]
#[timeout(60_000)]
fn test_cross_term_tester_exclusion_unsat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (assert (= x y))
        (assert ((_ is stack) x))
        (assert ((_ is empty) y))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "merged class cannot satisfy two distinct testers"
    );
}

/// Tester transfer control: agreeing testers across the merge must stay sat.
#[test]
#[timeout(60_000)]
fn test_cross_term_tester_transfer_stays_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (assert (= x y))
        (assert ((_ is stack) x))
        (assert ((_ is stack) y))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "agreeing testers across a merge must stay sat"
    );
}

/// Blocksworld-shaped frame chain: state copies `s2 = s1 = s0 = stack(A,
/// empty)` (the BMC frame-equality pattern) with a goal tester on the LAST
/// copy. Exercises multi-hop explanations (reason = the whole chain). Unsat
/// direction plus sat control.
#[test]
#[timeout(60_000)]
fn test_frame_chain_commitment_unsat_and_control() {
    let unsat_smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const s0 tower)
        (declare-const s1 tower)
        (declare-const s2 tower)
        (assert (= s0 (stack A empty)))
        (assert (= s1 s0))
        (assert (= s2 s1))
        (assert (or ((_ is empty) s2) (= (top s2) B)))
        (check-sat)
    "#;
    let result = crate::common::solve(unsat_smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "s2 ~ stack(A, empty): is-empty(s2) and top(s2)=B are both impossible"
    );

    let sat_smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const s0 tower)
        (declare-const s1 tower)
        (declare-const s2 tower)
        (assert (= s0 (stack A empty)))
        (assert (= s1 s0))
        (assert (= s2 s1))
        (assert (or ((_ is empty) s2) (= (top s2) A)))
        (check-sat)
    "#;
    let result = crate::common::solve(sat_smt);
    assert_eq!(result.trim(), "sat", "top(s2) = A is the real model");
}
