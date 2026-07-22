// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for issue #5975: CEGQI refinement false-UNSAT on mixed
//! UF+arithmetic quantifiers.
//!
//! When CEGQI refinement re-solves and gets UNSAT, disambiguation is needed
//! to determine whether the UNSAT is genuine or CE-induced. Without
//! disambiguation, satisfiable formulas may nondeterministically return UNSAT.
//!
//! The fix adds `disambiguate_cegqi_unsat` to both `try_cegqi_arith_refinement`
//! and `try_cegqi_neighbor_enumeration`, which re-solves without CE lemmas to
//! check if UNSAT is genuine.

use ntest::timeout;

/// Genuinely UNSAT: forall constrains f(x), but free variable contradicts.
///
/// `forall x. f(x) >= 0` combined with `f(0) < 0` is genuinely UNSAT.
/// The disambiguation should still return UNSAT here — the ground assertions
/// alone (with E-matching instance f(0) >= 0 and f(0) < 0) are contradictory.
#[test]
#[timeout(10000)]
fn test_uflia_forall_genuinely_unsat() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (< (f 0) 0))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "Genuinely contradictory formula should return UNSAT"
    );
}

/// Mixed UF+LIA with both forall and ground constraints. SAT.
///
/// `forall x in [0,10]. f(x) + x >= 0` with `a = 5` is satisfiable.
/// Uses bounded integer guard so CEGQI enters the refinement loop.
#[test]
#[timeout(10000)]
fn test_uflia_forall_with_ground_sat() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun a () Int)
        (assert (= a 5))
        (assert (forall ((x Int)) (=> (and (>= x 0) (<= x 10)) (>= (+ (f x) x) 0))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "Mixed UF+LIA with ground should return SAT"
    );
}

/// Pure LIA forall with bounded integer range — refinement loop test.
///
/// `forall i in [0,5]. i < 100` is a tautology over range [0,5].
/// Finite domain expansion handles this, but CEGQI refinement should also
/// not produce false UNSAT if it enters the loop.
#[test]
#[timeout(10000)]
fn test_lia_forall_bounded_refinement_sat() {
    let smt = r#"
        (set-logic LIA)
        (assert (forall ((i Int)) (=> (and (<= 0 i) (<= i 5)) (< i 100))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "bounded LIA tautology should be sat");
}

/// CEGQI disambiguation: CE-induced UNSAT detected and corrected to SAT.
///
/// Uses the pattern from quantifier_loop.rs:626-637:
///   `forall x. (f(x) > 0 => x >= 1)` is a valid formula (SAT).
/// E-matching adds `f(0) <= 0` (for x=0). The CE lemma adds
/// `f(__ce_x) > 0 AND __ce_x < 1`. The solver may unify __ce_x=0,
/// creating contradiction `f(0) > 0` vs `f(0) <= 0`. But ground-only
/// (without CE lemma) is SAT, so disambiguation should return SAT.
///
/// This exercises the `disambiguate_cegqi_unsat` code path where:
/// 1. Initial solve with CE lemma returns UNSAT
/// 2. Re-solve without CE lemma returns SAT (ground is satisfiable)
/// 3. Disambiguation concludes: forall is valid → overall SAT
#[test]
#[timeout(10000)]
fn test_uflia_disambiguation_ce_induced_unsat_returns_sat() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (=> (> (f x) 0) (>= x 1))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "CE-induced UNSAT should be disambiguated to SAT (forall is valid)"
    );
}

/// SOUNDNESS pin for the UF-GRAPH pin leg's DEFAULT choice (#cegqi-mdef v2):
/// `forall x in [0,10]. f(x) <= -1` is genuinely SAT (f ≡ -1), but the
/// re-completion default (0 for Int) FALSIFIES the body, so the UF-pin
/// certificate must fail closed rather than mint a verdict from the wrong
/// default. Unknown is acceptable; unsat is a soundness bug.
#[test]
#[timeout(20000)]
fn test_uflia_forall_wrong_default_fails_closed() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (=> (and (>= x 0) (<= x 10)) (<= (f x) (- 1)))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_ne!(
        results,
        vec!["unsat"],
        "wrong-default completion must not decide unsat"
    );
}
