// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Cardinal soundness spec: the STRICT UF-completion certificate must not grant
//! `sat` for a quantifier E-matching never instantiated
//! (#ufbv-strict-uf-completion-no-coverage).
//!
//! At 0.5.0+build.6243 this regression was red: the strict leg proposed `sat`
//! without a coverage premise. The mandatory independent-model boundary now
//! withholds any such unconfirmed proposal in every mode, so this is a green
//! publication-soundness guard. The strict leg still needs real coverage to
//! recover a definitive answer instead of sound `unknown`.
//!
//! Ground truth needs no oracle. Instantiate the single universal at
//! `x = #x00000001`: the conjuncts demand `f(1) = 0` and `1 = f(1)`, hence
//! `1 = 0`. The universal is false, so the assertion set is UNSATISFIABLE. z3
//! 4.15.4 agrees. `sat` is therefore a wrong answer; `unsat` is ideal and
//! `unknown` is an acceptable sound incompleteness.
//!
//! WHY THIS IS SEPARATE from `ufbv_deferred_default_mode_wrong_sat.rs`: that file
//! guards corpus instances of the `(=> premise conclusion)` shape, which the
//! multi-point `premise_forced_binder_refutation` probe can refute by sampling
//! premise models. This body is a BARE CONJUNCTION with no premise, so that probe
//! declines by construction and cannot ever fix this case. The two files pin the
//! two search shapes; this one pins the bare-conjunction publication boundary.
//!
//! The defect, traced with `AY_DEBUG_CERT=1`: `quantifiers_supported_by_uf_completion`
//! (`quantifier_loop/mod.rs:746`) is a conjunction carrying NO coverage term, so
//! zero instantiations cannot block it, while its sibling `..._given_sat` leg IS
//! gated on `!has_uninstantiated && !reached_limit && !deferred_exists`
//! (`mod.rs:937`). Only one leg got the discipline. Compounding it,
//! `term_supported_by_uf_completion`'s `and` arm (`mbqi.rs:1339`) accepts each
//! conjunct independently and nothing requires a defined head to be defined once,
//! so the contradictory pair `(= (f x) 0)` / `(= x (f x))` is certified as freely
//! completable. The pairwise-distinct-head check that would catch it exists only
//! on the `given_sat` leg (`mod.rs:816`).
//!
//! CAUTION for whoever fixes this: a blanket coverage gate on the strict leg is
//! NOT free. Measured across every quantified in-tree test, 27 `sat` verdicts ride
//! the gate's `deferred` channel and 24 of them assert `sat` STRICTLY — 13 in
//! `group_auflia/auflia_verification_consumer_9185_reducers.rs` alone, plus
//! `group_quantifiers/ufbv_fixpoint_premise_forced_unsat.rs:235`, which is a
//! strict two-`sat` assertion on this very family's shape. The decisive
//! satisfiable case is `∀s. 0 ≤ seq_len(s)`, which is obviously satisfiable
//! (`seq_len ≡ 0`) and which a blanket gate answers `unknown`. Those verdicts are
//! statistically INDISTINGUISHABLE from this wrong one at the gate — identical
//! `deferred` / `cannot-confirm` / zero-instance statistics — so the separating
//! evidence has to be constructed (a materialized completion re-checked against
//! the assertions), not read off existing flags.

const STRICT_LEG_WRONG_SAT: &str =
    include_str!("../fixtures/ufbv_uf_completion_strict_leg_wrong_sat.smt2");

/// Regression for the formerly open wrong-`sat` publication obligation.
#[test]
fn strict_uf_completion_never_grants_sat_without_coverage() {
    let results = crate::common::solve_vec(STRICT_LEG_WRONG_SAT);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "WRONG SAT: this problem is UNSATISFIABLE — instantiating at \
         x = #x00000001 demands f(1) = 0 and 1 = f(1), hence 1 = 0 (z3 4.15.4 \
         agrees `unsat`). AY grants `sat` off the STRICT UF-completion \
         certificate, whose condition carries no coverage term, having created \
         ZERO instances of the one quantifier. `unknown` is the sound answer, \
         `unsat` is ideal; got {results:?}"
    );
}

/// `--self-check` reaches the same mandatory publication boundary. Pin it so
/// later certificate work cannot regress the stricter workflow.
#[test]
fn strict_uf_completion_selfcheck_failclosed() {
    let results = crate::common::solve_selfcheck_vec(STRICT_LEG_WRONG_SAT);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "`--self-check` must stay fail-closed here (measured `unknown` with \
         `:reason-unknown incomplete`); got {results:?}"
    );
}

/// Sanity: the fixture is the input this spec claims, so it cannot pass vacuously.
#[test]
fn fixture_is_the_minimal_unsat_strict_leg_witness() {
    assert!(
        STRICT_LEG_WRONG_SAT.contains("(set-info :status unsat)"),
        "fixture must declare its UNSAT ground truth"
    );
    assert!(
        STRICT_LEG_WRONG_SAT.contains("forall"),
        "fixture must be quantified"
    );
    // Both conjuncts are load-bearing: the constant-valued definition of `f` AND
    // the equation against the BARE bound variable. Lose either and the shape no
    // longer exercises the strict leg's missing distinct-head discipline.
    assert!(
        STRICT_LEG_WRONG_SAT.contains("(= (f x) (_ bv0 32))")
            && STRICT_LEG_WRONG_SAT.contains("(= x (f x))"),
        "fixture must retain BOTH contradictory definitions of `f` — the \
         constant-valued one and the bare-bound-variable one"
    );
    assert!(
        ay_frontend::parse(STRICT_LEG_WRONG_SAT).is_ok(),
        "fixture must parse — else the verdict assertion is vacuous"
    );
}
