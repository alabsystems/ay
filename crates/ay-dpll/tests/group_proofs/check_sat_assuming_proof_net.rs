// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! `check-sat-assuming` must reach the publication funnel WITH a proof.
//!
//! The mandatory UNSAT funnel (`executor/unsat_cert.rs`) refuses to publish
//! `unsat` without a certificate. On the plain `check-sat` path that is
//! guaranteed by two backstops — `check_sat.rs:2388` and `:3608`, each
//! `if result.is_unsat() && self.produce_proofs_enabled() && self.last_proof.is_none()
//! { self.build_unsat_proof(); }` — plus UNSAT-implies-proof `debug_assert`s
//! at `:2655` and `:3631`.
//!
//! `check_sat_assuming` had NEITHER. Its terminal
//! `finish_check_sat_assuming_result` asserted only that
//! `last_assumption_core` was populated. Any lane that returned a bare
//! `Ok(SolveResult::unsat())` without building a proof therefore reached the
//! funnel with `last_proof == None`, and a CORRECT refutation was published as
//! `unknown` with
//!
//! ```text
//! computed UNSAT rejected by mandatory strict certification:
//!   the provisional UNSAT verdict has no proof
//! ```
//!
//! Note this is NOT about proof tracking being disabled: `begin_public_solve`
//! (`lifecycle.rs:302`) enables the tracker unconditionally for every public
//! decision, precisely so that "proof-backed UNSAT correctness" cannot be
//! switched off by `:produce-proofs false`.
//!
//! The bar these tests set is deliberately a PARITY bar, not "always unsat":
//! the same conjunction asserted directly must not beat the same conjunction
//! split into assertions + assumptions. Where plain `check-sat` says `unsat`,
//! `check-sat-assuming` must not degrade to `unknown`.
//!
//! Shapes whose refutation carries no proof artifact AT ALL are out of scope
//! and are documented as such below (datatype acyclicity is the known case:
//! `ay-theories/dt/src/conflicts.rs` discards its cycle witness, and no
//! `TheoryLemmaKind` for acyclicity exists).

/// Assert that splitting a conjunction into assertions + assumptions does not
/// lose a refutation the solver finds when the same terms are all asserted.
fn assert_assuming_matches_plain(label: &str, plain: &str, assuming: &str) {
    let plain_verdict = crate::common::solve(plain);
    let plain_verdict = plain_verdict.trim();
    // The premise of the parity claim must hold; otherwise the comparison is
    // vacuous and the test must fail explicitly.
    assert_eq!(
        plain_verdict, "unsat",
        "{label}: PRECONDITION FAILED — plain check-sat must be `unsat` for the \
         parity comparison to mean anything"
    );

    let assuming_verdict = crate::common::solve(assuming);
    let assuming_verdict = assuming_verdict.trim();
    assert_eq!(
        assuming_verdict, "unsat",
        "{label}: plain check-sat proves this UNSAT, but check-sat-assuming on the \
         SAME conjunction degraded to {assuming_verdict:?}. A refutation must not be \
         lost by moving a conjunct into the assumption slot — if this reads \
         `unknown`, the assumptions path reached the publication funnel without a \
         proof (see this file's module docs)."
    );
}

/// QF_SLIA: `len(s) = 3` with `s = "ab"` is UNSAT (2 != 3).
///
/// This is the minimal reproducer. Plain `check-sat` emits a full Alethe proof
/// and publishes `unsat`; before the fix the assuming form published `unknown`
/// with "the provisional UNSAT verdict has no proof".
#[test]
fn slia_length_literal_conflict_survives_assumption_split() {
    assert_assuming_matches_plain(
        "QF_SLIA len/literal",
        r#"
            (set-logic QF_SLIA)
            (declare-fun s () String)
            (assert (= (str.len s) 3))
            (assert (= s "ab"))
            (check-sat)
        "#,
        r#"
            (set-logic QF_SLIA)
            (declare-fun s () String)
            (assert (= (str.len s) 3))
            (check-sat-assuming ((= s "ab")))
        "#,
    );
}

/// QF_LIA control: a pure-arithmetic conflict through the assumption slot.
///
/// Guards against a fix that special-cases strings. `x > 5` with `x < 2` is
/// UNSAT by any linear-arithmetic lane.
#[test]
fn lia_bound_conflict_survives_assumption_split() {
    assert_assuming_matches_plain(
        "QF_LIA bounds",
        r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (assert (> x 5))
            (assert (< x 2))
            (check-sat)
        "#,
        r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (assert (> x 5))
            (check-sat-assuming ((< x 2)))
        "#,
    );
}

/// QF_UF control: an EUF congruence conflict through the assumption slot.
#[test]
fn euf_congruence_conflict_survives_assumption_split() {
    assert_assuming_matches_plain(
        "QF_UF congruence",
        r#"
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun f (U) U)
            (declare-fun a () U)
            (declare-fun b () U)
            (assert (= a b))
            (assert (distinct (f a) (f b)))
            (check-sat)
        "#,
        r#"
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun f (U) U)
            (declare-fun a () U)
            (declare-fun b () U)
            (assert (= a b))
            (check-sat-assuming ((distinct (f a) (f b))))
        "#,
    );
}

/// SOUNDNESS DIRECTION. A genuinely SATISFIABLE assumption set must stay `sat`.
///
/// A "fix" that manufactured proofs could push a satisfiable query to `unsat`.
/// Nothing here may ever read `unsat`.
#[test]
fn satisfiable_assumption_is_never_refuted() {
    for (label, smt) in [
        (
            "QF_SLIA sat",
            r#"
                (set-logic QF_SLIA)
                (declare-fun s () String)
                (assert (= (str.len s) 2))
                (check-sat-assuming ((= s "ab")))
            "#,
        ),
        (
            "QF_LIA sat",
            r#"
                (set-logic QF_LIA)
                (declare-fun x () Int)
                (assert (> x 5))
                (check-sat-assuming ((< x 20)))
            "#,
        ),
        (
            "QF_UF sat",
            r#"
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun f (U) U)
                (declare-fun a () U)
                (declare-fun b () U)
                (assert (= a b))
                (check-sat-assuming ((= (f a) (f b))))
            "#,
        ),
    ] {
        let verdict = crate::common::solve(smt);
        let verdict = verdict.trim();
        assert_ne!(
            verdict, "unsat",
            "{label}: this assumption set is SATISFIABLE — publishing `unsat` here \
             would be a wrong answer, not an incompleteness"
        );
    }
}

/// The empty assumption list must behave exactly like plain `check-sat`.
///
/// `(check-sat-assuming ())` shares the assumptions plumbing but has no
/// assumption literals at all, so it is the cleanest test that the funnel is
/// reached with a proof.
#[test]
fn empty_assumption_list_matches_plain_check_sat() {
    assert_assuming_matches_plain(
        "empty assumption list",
        r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (assert (> x 5))
            (assert (< x 2))
            (check-sat)
        "#,
        r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (assert (> x 5))
            (assert (< x 2))
            (check-sat-assuming ())
        "#,
    );
}
