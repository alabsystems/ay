// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Cardinal soundness spec: a quantified wrong-SAT must not ship in DEFAULT
//! mode either (#quantified-deferred-default).
//!
//! These fixtures originally exposed a default-mode publication hole that only
//! `--self-check` closed. The mandatory independent-model boundary now rejects
//! `CannotConfirm` and deferred quantified evidence in every mode, so all tests
//! in this file are green guards for that universal policy. The dated corpus
//! counts below describe the pre-boundary defect, not current public behavior.
//!
//! The goal is a complete Z3 FUNCTIONAL replacement. A replacement may answer
//! `unknown` where Z3 answers `unsat` — that is an incompleteness, and it is
//! visible to the caller. It may not answer `sat` where Z3 answers `unsat`:
//! that is a wrong answer, it is silent, and no downstream consumer can detect
//! it. Every mode must therefore fail closed when no sound SAT certificate
//! exists.
//!
//! Spec (the contract this file pins):
//!   A syntactic quantified-UF shape classifier is not SAT authority. AY must
//!   not answer `sat` unless it has a constructed/rechecked model or a narrow
//!   semantic certificate whose premises are actually established. Otherwise
//!   `unknown` is the sound visible answer; an independently proved `unsat` is
//!   also valid.
//!
//! Three fixtures, all `(set-info :status unsat)` and agreed UNSAT by z3 4.15.4:
//! * `AR-fixpoint-5` — the original representative. At 0.4.0+build.5825
//!   (`2068d68d`) AY DECIDES this one correctly (`unsat`), so it no longer
//!   exercised the wrong-SAT channel. Kept as a non-regression guard.
//! * `small-synabs-fixpoint-2` — selected on 2026-07-26 as a live wrong `sat`,
//!   the smallest of the 7 then-remaining UFBV instances from the scoreboard's
//!   13 disagreements.
//! * `small-pipeline-fixpoint-1` — one of six wrong `sat`s in the 2026-07-29
//!   family sweep and its smallest reproducer by four orders of magnitude.
//!
//! **CURRENCY NOTE (2026-07-29): both fixtures now PASS, and this file was
//! written expecting the second one to fail.** It was authored against
//! `2068d68d`, where `small-synabs-fixpoint-2` really did answer `sat`. Rebasing
//! onto `main` — 400 commits ahead — made it green: AY now computes `unsat` on it
//! and withholds the verdict as MODEL-UNCONFIRMED rather than shipping `sat`.
//!
//! Those two fixtures no longer demonstrate the defect; they are kept as
//! non-regression guards. A 2026-07-29 sweep at build 6235 found six wrong
//! candidate `sat` verdicts in the then-open default publication channel. The
//! third fixture is one of those six and now proves the universal boundary
//! withholds it. This does not prove quantified-search completeness: returning
//! `unknown` is sound but remains a replacement-capability gap.

const WINTERSTEIGER_DEFERRED_WRONG_SAT: &str =
    include_str!("../fixtures/ufbv_wintersteiger_fixpoint_deferred_wrong_sat.smt2");

/// `small-synabs-fixpoint-2` — a wrong `sat` at `2068d68d`, retained as a
/// historical regression.
const SMALL_SYNABS_WRONG_SAT_REGRESSION: &str =
    include_str!("../fixtures/ufbv_small_synabs_fixpoint_2_wrong_sat.smt2");

/// `small-pipeline-fixpoint-1` — a wrong `sat` at historical build 6235
/// (`de03e266`), found by the 2026-07-29 family sweep. 17 lines and 7.5 KB, the
/// smallest of the 6 by four orders of magnitude (the others are 9–55 MB), and it
/// historically failed in 5 ms.
///
/// Ground truth is triple-confirmed: the file's own `:status unsat`, z3 4.15.4
/// (`unsat` in 11 ms), and a hand refutation that needs no solver. The single
/// `forall` is `∀v⃗. premise ⇒ conclusion` over 13 BitVec-32 binders and one Bool.
/// The premise pins the `_64_0` state to zero and DEFINES the `_64_1` state from
/// it, but leaves `dataIn_64_0`, `c1_64_0`, `c2_64_0` and `reset_64_0` free. Among
/// the conclusion's conjuncts are `f1(v⃗) = 0` and `stageOne_64_1 = f1(v⃗)`, and the
/// premise gives `stageOne_64_1 = dataIn_64_0 + c1_64_0`. Together they demand
/// `dataIn_64_0 + c1_64_0 = 0` for ALL values of two free 32-bit binders, which
/// fails at `dataIn_64_0 = c1_64_0 = 1`. So the universal is false, the assertion
/// is unsatisfiable, and `sat` is a wrong answer.
const SMALL_PIPELINE_WRONG_SAT_REGRESSION: &str =
    include_str!("../fixtures/ufbv_small_pipeline_fixpoint_1_wrong_sat.smt2");

/// THE default-mode regression: this quantified UNSAT must never be answered
/// `sat` by a plain `check-sat` with no flags.
#[test]
fn ufbv_wintersteiger_fixpoint_never_default_sat() {
    let results = crate::common::solve_authored_vec(WINTERSTEIGER_DEFERRED_WRONG_SAT);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "quantified UFBV fixpoint check is UNSAT (z3, cvc5, and its own \
         `:status unsat` agree) — DEFAULT mode must not answer `sat` for a \
         quantified assertion without constructive SAT authority. \
         `unknown` is the sound answer; got {results:?}"
    );
}

/// THE default-mode regression. `small-synabs-fixpoint-2` is UNSAT (z3 4.15.4
/// and its own `:status`). AY answered `sat` here at 0.4.0+build.5825, so this
/// now guards the repair rather than stating a current bug.
#[test]
fn ufbv_small_synabs_fixpoint_2_never_default_sat() {
    let results = crate::common::solve_authored_vec(SMALL_SYNABS_WRONG_SAT_REGRESSION);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "`small-synabs-fixpoint-2` is UNSAT (z3 4.15.4 and its own \
         `:status unsat` agree) — DEFAULT mode must not answer `sat` for a \
         quantified assertion without a valid SAT certificate. `unknown` is \
         the sound answer; got {results:?}"
    );
}

/// The same input under `--self-check`. Pins that the default-mode repair did
/// not loosen the independently checked mode.
#[test]
fn ufbv_small_synabs_fixpoint_2_selfcheck_failclosed() {
    let results = crate::common::solve_authored_selfcheck_vec(SMALL_SYNABS_WRONG_SAT_REGRESSION);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "`--self-check` must stay fail-closed on `small-synabs-fixpoint-2`; \
         got {results:?}"
    );
}

/// Regression for the formerly open obligation (red at build 6235,
/// `de03e266`); the current publication boundary must keep it green.
///
/// `small-pipeline-fixpoint-1` is UNSAT by its own `:status`, by z3 4.15.4, and by
/// the hand refutation recorded on `SMALL_PIPELINE_WRONG_SAT_REGRESSION`. At
/// build 6235 it answered `sat` in 5 ms with zero E-matching instances and an
/// empty model — it granted satisfiability without ever instantiating the
/// single quantifier.
///
/// `unknown` is an acceptable pass (sound and visible), while `unsat` is ideal.
#[test]
fn ufbv_small_pipeline_fixpoint_1_never_default_sat() {
    let results = crate::common::solve_authored_vec(SMALL_PIPELINE_WRONG_SAT_REGRESSION);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "WRONG SAT: `small-pipeline-fixpoint-1` is UNSAT (its own `:status`, z3 \
         4.15.4, and a hand refutation at `dataIn_64_0 = c1_64_0 = 1` all agree). \
         A syntactic UF-completion classifier must never grant `sat`; `unknown` \
         is the sound answer when no total model is certified. Got {results:?}"
    );
}

/// `--self-check` reaches the same mandatory SAT-publication boundary. Pin it
/// separately so the stricter workflow cannot regress into the wrong `sat`.
#[test]
fn ufbv_small_pipeline_fixpoint_1_selfcheck_failclosed() {
    let results = crate::common::solve_authored_selfcheck_vec(SMALL_PIPELINE_WRONG_SAT_REGRESSION);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "`--self-check` must stay fail-closed on `small-pipeline-fixpoint-1` \
         (measured `unknown` with `:reason-unknown incomplete`); got {results:?}"
    );
}

/// The fail-closed mode must stay fail-closed: the default-mode repair must not
/// loosen `--self-check`.
#[test]
fn ufbv_wintersteiger_fixpoint_selfcheck_still_failclosed() {
    let results = crate::common::solve_authored_selfcheck_vec(WINTERSTEIGER_DEFERRED_WRONG_SAT);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "`--self-check` must remain fail-closed on an unverified quantified \
         assertion; got {results:?}"
    );
}

/// Sanity: the fixture is the input this spec claims it is. A malformed or
/// truncated fixture would make the verdict assertions pass vacuously — the
/// exact failure mode that let the wrong-SAT canary sit un-tested (0060eb4c59).
#[test]
fn fixture_is_the_declared_unsat_quantified_ufbv_benchmark() {
    assert!(
        WINTERSTEIGER_DEFERRED_WRONG_SAT.contains("(set-info :status unsat)"),
        "fixture must carry its declared UNSAT ground truth"
    );
    assert!(
        WINTERSTEIGER_DEFERRED_WRONG_SAT.contains("forall"),
        "fixture must be the quantified benchmark"
    );
    assert!(
        ay_frontend::parse(WINTERSTEIGER_DEFERRED_WRONG_SAT).is_ok(),
        "fixture must parse — a parse failure would make the verdict assertions vacuous"
    );
    assert!(
        SMALL_SYNABS_WRONG_SAT_REGRESSION.contains("(set-info :status unsat)"),
        "historical regression fixture must carry its declared UNSAT ground truth"
    );
    assert!(
        SMALL_SYNABS_WRONG_SAT_REGRESSION.contains("forall"),
        "historical regression fixture must be quantified"
    );
    assert!(
        ay_frontend::parse(SMALL_SYNABS_WRONG_SAT_REGRESSION).is_ok(),
        "historical regression fixture must parse — else its verdict assertions are vacuous"
    );
    assert!(
        SMALL_PIPELINE_WRONG_SAT_REGRESSION.contains("(set-info :status unsat)"),
        "the small-pipeline fixture must carry its declared UNSAT ground truth"
    );
    assert!(
        SMALL_PIPELINE_WRONG_SAT_REGRESSION.contains("forall"),
        "the small-pipeline fixture must be quantified"
    );
    assert!(
        ay_frontend::parse(SMALL_PIPELINE_WRONG_SAT_REGRESSION).is_ok(),
        "the small-pipeline fixture must parse — else its verdict assertion is vacuous"
    );
    // The hand refutation depends on these two binders being FREE in the premise
    // (only their sum is constrained, via `stageOne_64_1`). If a future corpus
    // refresh changed the file, the recorded ground-truth argument would no
    // longer apply to it.
    assert!(
        SMALL_PIPELINE_WRONG_SAT_REGRESSION.contains("Verilog__main.dataIn_64_0")
            && SMALL_PIPELINE_WRONG_SAT_REGRESSION.contains("Verilog__main.c1_64_0"),
        "the small-pipeline fixture must still contain the two free binders the \
         recorded hand refutation instantiates (`dataIn_64_0`, `c1_64_0`)"
    );
}
