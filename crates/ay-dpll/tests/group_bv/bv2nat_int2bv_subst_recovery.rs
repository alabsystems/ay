// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The `bv2nat`/`int2bv` ROUND-TRIP: a variable eliminated by substitution must
//! be recovered at its DEFINED value (#bv2nat-subst-recover).
//!
//! ## What was wrong
//!
//! `(= V (bv2nat ((_ int2bv 64) V1)))` is a top-level definition, so AUFLIA
//! preprocessing eliminates `V` and records `V -> bv2nat(((_ int2bv 64) V1))`.
//! Model recovery then replays that RHS through `eval_lia_int_under_values`,
//! which treated `bv2nat` as an OPAQUE Int atom and read the LIA model back by
//! TermId. Two things go wrong at once:
//!
//!   * the SAME substitution pass rewrote the surviving assertions, so the atom
//!     the LIA model actually valued is `bv2nat(((_ int2bv 64) 100))` — a
//!     DIFFERENT TermId from the recorded RHS. The lookup misses.
//!   * even on a hit, an opaque assignment is free to disagree with the bits.
//!
//! `V` therefore reached model completion with no value, was defaulted, and the
//! published model read `V = 1` against `V1 = 100`. The independent model-check
//! gate — working exactly as designed — refuted it and fail-closed a decidable
//! query to `unknown`:
//!
//! ```text
//! [AY SOUNDNESS GATE] caught an INVALID model
//!     assertion: (= V (bv2nat ((_ int2bv 64) V1)))
//!     falsified under model: V = 1, V1 = 100
//! ```
//!
//! 17,085 of the 17,586 caught invalid models in the fleet's 2026-08-27
//! trust-verification logs are this one shape — `(= <var> (bv2nat <bv expr>))`
//! over `((_ int2bv w) <int>)`, `bvand`, `bvshl`, `bvor`, `concat`, `extract`,
//! `bvlshr`, `bvxor`, `sign_extend`.
//!
//! ## The fix, and what it must NOT be
//!
//! `bv2nat` is INTERPRETED, so its value is a function of its argument's bits.
//! `eval_lia_bv_under_values` computes that argument structurally from the Int
//! leaves the model already values, and `eval_lia_int_under_values` prefers it
//! over the opaque read. Evaluation-side only: no assertion is added or
//! removed, and the gate is untouched — the cases below still go through it.
//!
//! The gate is the reason a WRONG recovery cannot hide, so the `*_unsat_*` and
//! `*_stays_sat_*` cases are the real guard: recovering a value must not turn a
//! genuinely-SAT query `unsat`, nor a refuted one `sat`.

use ntest::timeout;

fn verdict(smt: &str) -> String {
    crate::common::solve_vec(smt)
        .into_iter()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "<none>".to_string())
}

fn outputs(smt: &str) -> String {
    crate::common::solve_vec(smt).join("\n")
}

/// The minimal round-trip: `bv2nat(int2bv_64(100))` is 100, so the query is SAT
/// and `V` must print as 100. Red before the fix (`unknown`, gate-refuted).
#[test]
#[timeout(60_000)]
fn bv2nat_int2bv_roundtrip_recovers_the_defined_value() {
    let smt = r#"
        (set-logic ALL)
        (declare-const V Int)
        (declare-const V1 Int)
        (assert (= V1 100))
        (assert (= V (bv2nat ((_ int2bv 64) V1))))
        (check-sat)
        (get-value (V))
    "#;
    let out = outputs(smt);
    assert!(out.contains("sat"), "expected sat, got:\n{out}");
    assert!(
        !out.contains("unsat"),
        "a satisfiable round-trip must never be refuted:\n{out}"
    );
    assert!(
        out.contains("(V 100)"),
        "V must be recovered as bv2nat(int2bv_64(100)) = 100:\n{out}"
    );
}

/// The dominant field shape, verbatim from the verify logs:
/// `(= V (bv2nat (bvand ((_ int2bv 64) V1) ((_ int2bv 64) V2))))`. With
/// `V1 = 3, V2 = 3` the answer is `3 & 3 = 3`; the pre-fix model claimed 8.
#[test]
#[timeout(60_000)]
fn bv2nat_bvand_int2bv_family_recovers_the_defined_value() {
    let smt = r#"
        (set-logic ALL)
        (declare-const V Int)
        (declare-const V1 Int)
        (declare-const V2 Int)
        (assert (= V1 3))
        (assert (= V2 3))
        (assert (= V (bv2nat (bvand ((_ int2bv 64) V1) ((_ int2bv 64) V2)))))
        (check-sat)
        (get-value (V))
    "#;
    let out = outputs(smt);
    assert!(out.contains("sat"), "expected sat, got:\n{out}");
    assert!(out.contains("(V 3)"), "3 & 3 = 3, not 8:\n{out}");
}

/// A masked shift, exercising `bvshl` + a BV literal operand (186 field hits
/// of `(= _6 (bv2nat (bvshl #x00000001 ((_ int2bv 32) n))))`).
#[test]
#[timeout(60_000)]
fn bv2nat_bvshl_literal_operand_recovers_the_defined_value() {
    let smt = r#"
        (set-logic ALL)
        (declare-const V Int)
        (declare-const n Int)
        (assert (= n 5))
        (assert (= V (bv2nat (bvshl #x00000001 ((_ int2bv 32) n)))))
        (check-sat)
        (get-value (V))
    "#;
    let out = outputs(smt);
    assert!(out.contains("sat"), "expected sat, got:\n{out}");
    assert!(out.contains("(V 32)"), "1 << 5 = 32:\n{out}");
}

/// SOUNDNESS GUARD (the direction that matters): the recovered value must be
/// the RIGHT one, so pinning `V` to a wrong constant alongside the definition
/// is UNSAT. A recovery that merely invented some in-range number would leave
/// this satisfiable.
#[test]
#[timeout(60_000)]
fn bv2nat_bvand_wrong_pin_is_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const V Int)
        (declare-const V1 Int)
        (declare-const V2 Int)
        (assert (= V1 3))
        (assert (= V2 3))
        (assert (= V (bv2nat (bvand ((_ int2bv 64) V1) ((_ int2bv 64) V2)))))
        (assert (= V 8))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "unsat", "3 & 3 is 3, so V = 8 is refutable");
}

/// COMPLETENESS GUARD: the companion of the case above must stay satisfiable.
/// Together these two show the solver is DECIDING the predicate rather than
/// rubber-stamping it.
#[test]
#[timeout(60_000)]
fn bv2nat_bvand_correct_pin_stays_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const V Int)
        (declare-const V1 Int)
        (declare-const V2 Int)
        (assert (= V1 12))
        (assert (= V2 10))
        (assert (= V (bv2nat (bvand ((_ int2bv 64) V1) ((_ int2bv 64) V2)))))
        (assert (= V 8))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "sat", "12 & 10 = 8");
}

/// THE HOLE THE RECOVERY UNCOVERED, and the guard that closes it.
///
/// `v = a & 1` lies in `{0,1}`, the quantifier forces `f` above 100 there, and
/// `f(v) < 50` — so this is UNSAT. It was `unknown` before the recovery fix
/// (`v` had no value at all, so the round-trip assertion tripped the gate);
/// WITH the recovery and WITHOUT the companion guard it became a WRONG `sat`,
/// published as `((a 2) (v 0) ((f v) 1) ((f 0) 101))` — an `f` that is not a
/// function. The conflicting row `f(0) = 101` comes from a quantifier
/// instantiation whose assertion model validation SKIPS, so no single conjunct
/// evaluates false and the compositional walk never sees the pair; only the
/// model's own function table does. `unsat` would be better still, and is not
/// what this asserts — `sat` is the one answer that must never come back.
#[test]
#[timeout(60_000)]
fn recovered_value_must_not_publish_a_non_functional_model() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const v Int)
        (assert (and (<= 0 a) (< a 4)))
        (assert (= v (bv2nat (bvand ((_ int2bv 64) a) ((_ int2bv 64) 1)))))
        (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 1)) (> (f x) 100))))
        (assert (< (f v) 50))
        (check-sat)
    "#;
    let got = verdict(smt);
    assert!(
        got != "sat",
        "UNSAT query reported {got}: the published model has f(v)=1 with v=0 and f(0)=101"
    );
}

/// A `bv2nat` over a FREE BitVec variable has no Int leaves to compute from, so
/// the structural walk declines and the old opaque behaviour stands. Recorded
/// so a later widening of the walk does not silently start inventing values for
/// unmodelled bits: `unknown` here is honest, `unsat` would be a false theorem.
#[test]
#[timeout(60_000)]
fn bv2nat_over_free_bitvec_var_is_never_refuted() {
    let smt = r#"
        (set-logic ALL)
        (declare-const V Int)
        (declare-const b (_ BitVec 64))
        (assert (= b (_ bv3 64)))
        (assert (= V (bv2nat b)))
        (check-sat)
    "#;
    let got = verdict(smt);
    assert!(
        got == "sat" || got == "unknown",
        "a satisfiable query must never be reported unsat; got {got}"
    );
}
