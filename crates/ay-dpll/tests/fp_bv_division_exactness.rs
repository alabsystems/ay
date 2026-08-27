// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The BV division/remainder family inside the FP bit-blaster.
//!
//! `bitblast_bv_app_value` had no arm for `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/
//! `bvsmod`, so any QF_BVFP query mentioning one of them fell through to
//! `None` and `solve_fp` published `unknown (:reason-unknown unsupported)` in
//! ~0.02 s — a pure capability gap with zero search. Every assertion below
//! returned `unknown` before the division arm existed; the expected verdicts
//! are the ones z3 4.16.0, cvc5 1.3.0 and bitwuzla 0.9.1 all agree on.
//!
//! Two classes of canary live here and both must stay:
//!
//! * **Capability** — the two shapes lifted from the Inc Equality_MachineArith
//!   division bucket (`exp_loop`'s `(= e (bvsdiv x (_ bv2 32)))` and
//!   `image_filter`'s `((_ to_fp 11 53) RNE (bvsdiv i (_ bv10 32)))`). They
//!   fail the moment the arm stops being reachable.
//! * **Exactness** — fully symbolic laws with no constant anywhere for a
//!   folding pass to evaluate, so they can only be decided by the emitted
//!   circuit. A quotient that is off by one, a sign fix-up applied to the
//!   wrong operand, or a missing `bvsmod` zero-guard turns each of these
//!   `unsat`s into a `sat`, i.e. into a wrong answer rather than a silent
//!   incompleteness.

mod common;

use common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

const DIV_TIMEOUT_SECS: u64 = 60;

fn check(name: &str, smt: &str, expected: SolverOutcome) {
    let outcome = run_executor_smt_with_timeout(smt, DIV_TIMEOUT_SECS)
        .unwrap_or_else(|err| panic!("{name}: executor error: {err}"));
    assert_eq!(outcome, expected, "{name}");
}

/// `exp_loop` shape: `(= e (bvsdiv x (_ bv2 32)))` with FP in scope.
/// A non-negative dividend can never divide up to something larger.
#[test]
#[timeout(120_000)]
fn sdiv_by_two_under_fp_is_refuted() {
    check(
        "sdiv_by_two_under_fp_is_refuted",
        r#"
        (set-logic QF_BVFP)
        (declare-const x (_ BitVec 32))
        (declare-const e (_ BitVec 32))
        (declare-const f (_ FloatingPoint 8 24))
        (assert (fp.isNaN f))
        (assert (= e (bvsdiv x (_ bv2 32))))
        (assert (bvsge x (_ bv0 32)))
        (assert (bvsgt e x))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// Same shape, SAT direction: a negative quotient must be reachable. Model
/// validation is armed, so a `sat` here is a validated model, not a guess.
#[test]
#[timeout(120_000)]
fn sdiv_by_two_under_fp_is_satisfiable() {
    check(
        "sdiv_by_two_under_fp_is_satisfiable",
        r#"
        (set-logic QF_BVFP)
        (declare-const x (_ BitVec 32))
        (declare-const e (_ BitVec 32))
        (declare-const f (_ FloatingPoint 8 24))
        (assert (fp.isNaN f))
        (assert (= e (bvsdiv x (_ bv2 32))))
        (assert (= e (bvneg (_ bv3 32))))
        (check-sat)
        "#,
        SolverOutcome::Sat,
    );
}

/// `image_filter` shape: the quotient is the argument of a `to_fp` conversion.
/// `0 <= i < 1000` forces `i / 10 < 100`, so the converted float cannot exceed
/// 100.0.
#[test]
#[timeout(120_000)]
fn sdiv_feeding_to_fp_is_refuted() {
    check(
        "sdiv_feeding_to_fp_is_refuted",
        r#"
        (set-logic QF_BVFP)
        (declare-const i (_ BitVec 32))
        (declare-const g (_ FloatingPoint 11 53))
        (assert (= g ((_ to_fp 11 53) RNE (bvsdiv i (_ bv10 32)))))
        (assert (bvsge i (_ bv0 32)))
        (assert (bvslt i (_ bv1000 32)))
        (assert (fp.gt g ((_ to_fp 11 53) RNE 100.0)))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// Signed division/remainder identity, fully symbolic: `m = (m/n)*n + (m%n)`.
/// An off-by-one quotient or a misplaced sign fix-up makes this `sat`.
#[test]
#[timeout(120_000)]
fn signed_div_rem_identity_holds_under_fp() {
    check(
        "signed_div_rem_identity_holds_under_fp",
        r#"
        (set-logic QF_BVFP)
        (declare-const m (_ BitVec 8))
        (declare-const n (_ BitVec 8))
        (declare-const f (_ FloatingPoint 8 24))
        (assert (fp.isNaN f))
        (assert (not (= n (_ bv0 8))))
        (assert (not (= m (bvadd (bvmul (bvsdiv m n) n) (bvsrem m n)))))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// Unsigned division/remainder identity, fully symbolic.
#[test]
#[timeout(120_000)]
fn unsigned_div_rem_identity_holds_under_fp() {
    check(
        "unsigned_div_rem_identity_holds_under_fp",
        r#"
        (set-logic QF_BVFP)
        (declare-const m (_ BitVec 8))
        (declare-const n (_ BitVec 8))
        (declare-const f (_ FloatingPoint 8 24))
        (assert (fp.isNaN f))
        (assert (not (= n (_ bv0 8))))
        (assert (not (= m (bvadd (bvmul (bvudiv m n) n) (bvurem m n)))))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// `bvsrem` takes the sign of the DIVIDEND — pin which operand the fix-up
/// reads. Swapping it to the divisor makes this `sat`.
#[test]
#[timeout(120_000)]
fn srem_takes_the_sign_of_the_dividend() {
    check(
        "srem_takes_the_sign_of_the_dividend",
        r#"
        (set-logic QF_BVFP)
        (declare-const m (_ BitVec 8))
        (declare-const n (_ BitVec 8))
        (declare-const f (_ FloatingPoint 8 24))
        (assert (fp.isNaN f))
        (assert (not (= n (_ bv0 8))))
        (assert (bvslt m (_ bv0 8)))
        (assert (bvsgt (bvsrem m n) (_ bv0 8)))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// `bvsmod` takes the sign of the DIVISOR — the other half of the pair, and
/// the canary for the `u = 0` guard in the SMT-LIB `ite` chain.
#[test]
#[timeout(120_000)]
fn smod_takes_the_sign_of_the_divisor() {
    check(
        "smod_takes_the_sign_of_the_divisor",
        r#"
        (set-logic QF_BVFP)
        (declare-const m (_ BitVec 8))
        (declare-const n (_ BitVec 8))
        (declare-const f (_ FloatingPoint 8 24))
        (assert (fp.isNaN f))
        (assert (bvsgt n (_ bv0 8)))
        (assert (bvslt (bvsmod m n) (_ bv0 8)))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// `INT_MIN` is where a magnitude taken with `bvnot` instead of `bvneg` — or
/// an overflow guard that clamps — diverges from SMT-LIB. `x / -1 = -x` holds
/// at EVERY 32-bit `x`, `INT_MIN` included: both sides wrap back to `INT_MIN`.
#[test]
#[timeout(120_000)]
fn sdiv_by_minus_one_negates_at_every_input() {
    check(
        "sdiv_by_minus_one_negates_at_every_input",
        r#"
        (set-logic QF_BVFP)
        (declare-const x (_ BitVec 32))
        (declare-const f (_ FloatingPoint 8 24))
        (assert (fp.isNaN f))
        (assert (not (= (bvsdiv x (bvneg (_ bv1 32))) (bvneg x))))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}

/// SMT-LIB total semantics for a zero divisor: `bvudiv x 0 = all-ones` and
/// `bvurem x 0 = x`. The restoring loop produces both without a special case;
/// this pins that it really does.
#[test]
#[timeout(120_000)]
fn division_by_zero_follows_smtlib() {
    check(
        "division_by_zero_follows_smtlib",
        r#"
        (set-logic QF_BVFP)
        (declare-const x (_ BitVec 32))
        (declare-const f (_ FloatingPoint 8 24))
        (assert (fp.isNaN f))
        (assert (not (and (= (bvudiv x (_ bv0 32)) (bvnot (_ bv0 32)))
                          (= (bvurem x (_ bv0 32)) x))))
        (check-sat)
        "#,
        SolverOutcome::Unsat,
    );
}
