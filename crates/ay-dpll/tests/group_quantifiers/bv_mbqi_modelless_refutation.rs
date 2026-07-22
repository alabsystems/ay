// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Completeness regression tests for the model-less refute-only BV-MBQI mode
//! (#broadcast-vacuity empty-ground).
//!
//! A conjunctive-position pure-BV `forall` whose problem has an EMPTY ground
//! slice (e.g. a lone broadcast axiom, as asserted by deductive-checks's
//! broadcast-vacuity precheck) produces a ground Sat WITHOUT a model, and
//! `try_bv_mbqi_refinement` used to bail out before trying a single candidate —
//! leaving even a forall falsified at the boundary value 0 undecided
//! (`unknown (incomplete quantifier-unhandled)`).
//!
//! The model-less mode enumerates the boundary candidates, CONSTANT-FOLDS each
//! ground instance, and asserts the ones that fold to a definite `false`. Every
//! asserted instance is entailed by the (conjunctive-position) universal, so
//! the mode can only drive the re-solve to a genuine UNSAT; it grants no
//! SAT-acceptance authority (the exhaustive-Sat conclusion is disabled while
//! model-less).
//!
//! History: the old wrong-SAT on these exact shapes (interpreted trigger heads
//! counted as vacuity certificates) was removed by the patterned-forall P0 fix;
//! these tests pin the SOUND part of the recovered completeness — the refutation
//! direction only.

use ntest::timeout;

fn assert_unsat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "{label}: expected unsat, got {results:?}"
    );
    assert!(
        !results.iter().any(|r| r == "sat"),
        "{label}: must NOT return sat (formula is UNSAT), got {results:?}"
    );
}

fn assert_not_sat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "{label}: must NOT return sat (formula is UNSAT), got {results:?}"
    );
}

fn assert_not_unsat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "{label}: must NOT return unsat (formula is satisfiable), got {results:?}"
    );
}

/// The deductive-checks "evil" broadcast alone (empty ground slice): `forall x:BV32.
/// x*x < 0` (signed) with its interpreted trigger `(bvmul x x)`. Falsified at
/// the boundary candidate x=0 (`bvslt #x0 #x0` is false) — must be UNSAT.
///
/// Pre-fix: `unknown` (BV-MBQI bailed with no model). The old-pin `sat` was a
/// wrong-SAT and must never come back.
#[test]
#[timeout(60000)]
fn test_evil_bv32_square_negative_forall_pattern_is_unsat() {
    assert_unsat(
        "(set-logic ALL)
         (assert (forall ((x (_ BitVec 32)))
           (! (bvslt (bvmul x x) #x00000000) :pattern ((bvmul x x)))))
         (check-sat)",
        "evil broadcast, patterned",
    );
}

/// Same universal without the pattern annotation — the refutation must not
/// depend on trigger bookkeeping.
#[test]
#[timeout(60000)]
fn test_evil_bv32_square_negative_forall_unpatterned_is_unsat() {
    assert_unsat(
        "(set-logic ALL)
         (assert (forall ((x (_ BitVec 32))) (bvslt (bvmul x x) #x00000000)))
         (check-sat)",
        "evil broadcast, no pattern",
    );
}

/// The deductive-checks evil main-goal query shape: the evil BV32 forall PLUS an
/// Int/mod-wrapped skolemized negated goal. The forall alone is already
/// refutable at x=0, so the conjunction is UNSAT. At minimum it must never be
/// sat (the old pin's answer, a wrong-SAT).
#[test]
#[timeout(60000)]
fn test_evil_forall_plus_int_skolem_goal_not_sat() {
    assert_not_sat(
        "(set-logic ALL)
         (declare-const v (_ BitVec 32))
         (declare-const i Int)
         (assert (forall ((x (_ BitVec 32)))
           (! (bvslt (bvmul x x) #x00000000) :pattern ((bvmul x x)))))
         (assert (and (<= (- 2147483648) i) (< i 2147483648)
           (not (= (+ (mod (+ (* i i) 2147483648) 4294967296) (- 2147483648))
                   (+ (mod (+ (mod (+ (* i i) 2147483648) 4294967296) 1) 4294967296)
                      (- 2147483648))))))
         (check-sat)",
        "evil forall + Int skolem goal",
    );
}

/// The deductive-checks "good" broadcast alone: `forall x:BV32. x*x >= 0` (signed).
/// ALSO genuinely UNSAT (x = 46341 wraps signed-negative: 46341^2 = 2147488281
/// > 2^31-1), but the refuting witness is NOT a boundary candidate, so the
/// model-less refute-only mode leaves it undecided. The pinned requirement is
/// soundness: it must never be `sat` (the old pin's wrong-SAT). If a later
/// change decides it, the only admissible verdict is `unsat`.
#[test]
#[timeout(60000)]
fn test_good_bv32_square_nonnegative_forall_never_sat() {
    assert_not_sat(
        "(set-logic ALL)
         (assert (forall ((x (_ BitVec 32)))
           (! (bvsle #x00000000 (bvmul x x)) :pattern ((bvmul x x)))))
         (check-sat)",
        "good broadcast (UNSAT at x=46341)",
    );
}

/// The good broadcast plus a satisfiable ground conjunct (`v = 5`): still
/// UNSAT overall (the forall is false); must never be sat.
#[test]
#[timeout(60000)]
fn test_good_bv32_square_forall_plus_ground_never_sat() {
    assert_not_sat(
        "(set-logic ALL)
         (declare-const v (_ BitVec 32))
         (assert (= v #x00000005))
         (assert (forall ((x (_ BitVec 32)))
           (! (bvsle #x00000000 (bvmul x x)) :pattern ((bvmul x x)))))
         (check-sat)",
        "good broadcast + ground v=5 (UNSAT at x=46341)",
    );
}

/// Control (refute-only guarantee): a genuinely VALID closed BV32 universal
/// with the same interpreted-trigger shape must NOT be refuted by the
/// model-less mode — no boundary instance of a valid forall folds to `false`,
/// so no instance is asserted and the verdict stays sat/unknown.
#[test]
#[timeout(60000)]
fn test_valid_bv32_reflexive_forall_never_unsat() {
    assert_not_unsat(
        "(set-logic ALL)
         (assert (forall ((x (_ BitVec 32)))
           (! (bvuge (bvmul x x) (bvmul x x)) :pattern ((bvmul x x)))))
         (check-sat)",
        "valid reflexive forall",
    );
}

/// Control: a valid GUARDED universal (`x < 16 => x <= 255` unsigned) — the
/// guard shape exercises the guard-constant extraction path; must never be
/// refuted.
#[test]
#[timeout(60000)]
fn test_valid_guarded_bv32_forall_never_unsat() {
    assert_not_unsat(
        "(set-logic ALL)
         (assert (forall ((x (_ BitVec 32)))
           (=> (bvult x #x00000010) (bvule x #x000000ff))))
         (check-sat)",
        "valid guarded forall",
    );
}

/// A DISJUNCTIVE-position false forall must NOT be refuted by instance
/// assertion: `(or (forall x. x*x < 0) true-disjunct)` is satisfiable. Guards
/// the conjunctive-position gate the model-less mode relies on.
#[test]
#[timeout(60000)]
fn test_disjunctive_position_false_forall_not_refuted() {
    assert_not_unsat(
        "(set-logic ALL)
         (declare-const b Bool)
         (assert (or b (forall ((x (_ BitVec 32))) (bvslt (bvmul x x) #x00000000))))
         (check-sat)",
        "false forall in disjunctive position",
    );
}

/// API surface (the deductive-checks lowering path, `try_forall_with_triggers`): the
/// evil broadcast asserted ALONE — an empty ground slice, so the ground solve
/// yields Sat with NO model and only the model-less refute-only mode can try
/// the boundary candidate x=0. Must be UNSAT.
#[test]
#[timeout(60000)]
fn test_api_evil_bv32_square_negative_triggered_forall_is_unsat() {
    use ay_dpll::api::{Logic, Solver, Sort};

    let mut s = Solver::new(Logic::All);
    let x = s.fresh_var("x", Sort::bitvec(32));
    let xx = s.bvmul(x, x);
    let zero = s.bv_const(0, 32);
    let body = s.bvslt(xx, zero);
    let ax = s
        .try_forall_with_triggers(&[x], body, &[&[xx]])
        .expect("forall_with_triggers");
    s.try_assert_term(ax).expect("assert");
    let r = s.try_check_sat().expect("check_sat");
    assert!(
        r.is_unsat(),
        "API evil broadcast alone: expected unsat, got {r:?}"
    );
}

/// API surface, refute-only control: the "good" broadcast alone (`x*x >= 0`,
/// UNSAT only at a non-boundary witness) must never be reported sat.
#[test]
#[timeout(60000)]
fn test_api_good_bv32_square_nonnegative_triggered_forall_never_sat() {
    use ay_dpll::api::{Logic, Solver, Sort};

    let mut s = Solver::new(Logic::All);
    let x = s.fresh_var("x", Sort::bitvec(32));
    let xx = s.bvmul(x, x);
    let zero = s.bv_const(0, 32);
    let body = s.bvsle(zero, xx);
    let ax = s
        .try_forall_with_triggers(&[x], body, &[&[xx]])
        .expect("forall_with_triggers");
    s.try_assert_term(ax).expect("assert");
    let r = s.try_check_sat().expect("check_sat");
    assert!(
        !r.is_sat(),
        "API good broadcast alone is UNSAT (x=46341); must never be sat, got {r:?}"
    );
}
