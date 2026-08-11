// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Cardinal soundness spec for a wrong REFUTATION in quantified AUFLIA
//! (#auflia-exists-eq-false-unsat). GREEN as of `832c8861ba`.
//!
//! This began as a red spec: at 0.4.0+build.5825 (`2068d68d`) AY answered
//! `unsat` on a problem that is provably satisfiable. The fix — E-matching
//! refusing to instantiate an `Exists` and conjoin the instance — landed on
//! `main` in `832c8861ba` WITHOUT a test. This file is that test, so the repair
//! is pinned rather than merely believed.
//!
//! Ground truth needs no oracle. The fixture is satisfied by interpreting every
//! predicate as universally FALSE: each guarded universal becomes vacuous and
//! the negated existential holds. z3 4.15.4 independently answers `sat`. So
//! `sat` is correct, `unknown` is a sound incompleteness, and `unsat` is a wrong
//! refutation — the most dangerous verdict AY can emit, because it silently
//! discharges an obligation that is in fact satisfiable and no consumer can
//! detect it.
//!
//! Provenance and localization (2026-07-26). Found by re-running the 13
//! disagreements in the development design notes at HEAD: 8 were
//! still wrong, 7 of them the open quantified-UFBV wrong-`sat` class (see
//! `group_quantifiers/ufbv_deferred_default_mode_wrong_sat.rs`), and this one —
//! the only wrong refutation.
//! It was reduced from the SMT-LIB `AUFLIA/20170829-Rodin`
//! `smt4579745768945200905` benchmark (10 assertions) to a 4-assertion core by
//! delta debugging, then re-authored from scratch as the fixture here so the
//! workspace does not vendor a CC BY-NC input.
//!
//! Three ingredients were each NECESSARY to reproduce — dropping any one made
//! AY return a sound `unknown` even before the fix:
//!   1. the one-point idiom `(exists ((j Idx)) (and (= j i) (tab u j)))`, which
//!      is logically just `(tab u i)`; inlining it by hand kills the bug, so the
//!      handling of existential-with-equality is implicated;
//!   2. a biconditional body under a predicate-guarded universal;
//!   3. a vacuous guard axiom whose consequent occurs nowhere else — which
//!      suggests the trigger is instantiation/relevancy selection, not the
//!      Boolean core.
//!
//! The idiom ALONE never misbehaved (asserted in isolation AY returns
//! `unknown`), so what surfaced the defect was the interaction, not the
//! one-point rewrite by itself. `--self-check` was sound throughout; the repair
//! made default mode sound too, which is what this file guards.

const AUFLIA_EXISTS_EQ_WRONG_UNSAT: &str =
    include_str!("../fixtures/auflia_exists_eq_biconditional_wrong_unsat.smt2");

/// THE guard: AY must never refute this satisfiable problem.
#[test]
fn auflia_exists_eq_biconditional_is_never_unsat() {
    let results = crate::common::solve_vec(AUFLIA_EXISTS_EQ_WRONG_UNSAT);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "WRONG REFUTATION: this problem is satisfiable (all predicates false is \
         a model; z3 4.15.4 agrees) — `unsat` silently discharges a satisfiable \
         obligation. `sat` or `unknown` are both acceptable; got {results:?}"
    );
}

/// The fail-closed mode is sound here today. Pin it so a future fix to default
/// mode cannot regress `--self-check` into the wrong refutation.
#[test]
fn auflia_exists_eq_biconditional_selfcheck_is_never_unsat() {
    let results = crate::common::solve_selfcheck_vec(AUFLIA_EXISTS_EQ_WRONG_UNSAT);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "`--self-check` must not certify a wrong refutation here; got {results:?}"
    );
}

/// The one-point idiom in isolation must also never be refuted unsoundly. This
/// passes today and guards the narrower rewrite while the interaction bug above
/// is open.
#[test]
fn one_point_exists_equality_idiom_alone_is_never_unsat() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun P (S) Bool)
        (declare-fun Q (S) Bool)
        (declare-fun c () S)
        (assert (forall ((i S)) (=> (Q i) (exists ((j S)) (and (= j i) (P j))))))
        (assert (not (exists ((k S)) (and (= k c) (P k)))))
        (check-sat)
    "#;
    // Satisfiable: P and Q universally false.
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "satisfiable (P, Q all false) — `unsat` is a wrong refutation; got {results:?}"
    );
}

/// Sanity: the fixture is the satisfiable input this spec claims, so a mangled
/// fixture cannot make the guards pass vacuously.
#[test]
fn fixture_is_the_declared_sat_quantified_auflia_problem() {
    assert!(
        AUFLIA_EXISTS_EQ_WRONG_UNSAT.contains("(set-info :status sat)"),
        "fixture must declare its SAT ground truth"
    );
    assert!(
        AUFLIA_EXISTS_EQ_WRONG_UNSAT.contains("exists")
            && AUFLIA_EXISTS_EQ_WRONG_UNSAT.contains("forall"),
        "fixture must retain the quantifier alternation that triggers the defect"
    );
    assert!(
        ay_frontend::parse(AUFLIA_EXISTS_EQ_WRONG_UNSAT).is_ok(),
        "fixture must parse — else the verdict assertions are vacuous"
    );
}
