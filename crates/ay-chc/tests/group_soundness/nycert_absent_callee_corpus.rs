// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::panic)]

//! Verdict pins for the real ny-cert panic-freedom CHC corpus.
//!
//! See `../fixtures/nycert_absent_callee/README.md` for provenance. In short:
//! the dominant `ny-cert` panic-freedom frontier bucket is NOT an ay engine gap.
//! Those obligations lower to Horn systems whose `error` relation is fed by a
//! clause with the *literal* constraint `true` — the
//! `[trust-absent-callee-assumption]` may-panic marker for a callee whose body
//! was not in the lowered bundle. When the marked block is reachable the system
//! is unsatisfiable **by construction**.
//!
//! Two pins, in both directions:
//!
//! * SOUNDNESS (false-proof canary). ay must never answer `Safe` on the
//!   absent-callee-poisoned systems. These are production artefacts, not
//!   synthesised ones, so any future generalisation/abstraction/widening lever
//!   that starts minting SAFE here is caught against real campaign input rather
//!   than against a hand-written model of it.
//!
//! * COMPLETENESS (banked-proof canary). ay must keep answering `Safe` on the
//!   two obligations in the same ny-cert run that genuinely ARE safe. Those two
//!   are the only ones of 24 consecutive full-verifier obligations that the
//!   production verifier proved; losing them is a silent regression of banked
//!   proof credit.
//!
//! The two directions together are what makes this corpus load-bearing: a
//! change that satisfies only the soundness pin can do so by answering `Unknown`
//! everywhere, and a change that satisfies only the completeness pin can do so
//! by answering `Safe` everywhere.

use ay_chc::{testing, ChcParser, PdrConfig, PortfolioConfig, PortfolioResult};
use ntest::timeout;
use std::time::Duration;

const RAT_IS_NEGATIVE_UNSAFE: &str =
    include_str!("../fixtures/nycert_absent_callee/rat_is_negative_absent_callee_unsafe.smt2");
const NEGATED_COEFFS_UNSAFE: &str = include_str!(
    "../fixtures/nycert_absent_callee/selfcheck_negated_coeffs_absent_callee_unsafe.smt2"
);
const RATIONAL_VAL_SAFE: &str =
    include_str!("../fixtures/nycert_absent_callee/rational_val_safe.smt2");
const RATIONAL_VAL_CLOSURE_SAFE: &str =
    include_str!("../fixtures/nycert_absent_callee/rational_val_closure_safe.smt2");

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Safe,
    Unsafe,
    Unknown,
}

fn solve(smt2: &str) -> Verdict {
    let problem = ChcParser::parse(smt2).expect("ny-cert corpus fixture must parse");
    let config = PortfolioConfig::test_default().parallel_timeout(Some(Duration::from_mins(1)));
    let solver = testing::new_portfolio_solver(problem.clone(), config);
    match solver.solve() {
        PortfolioResult::Safe(model) => {
            // Never take a bare `Safe` at face value: re-validate the invariant
            // against the original problem, exactly as `soundness_vs_z3` does.
            let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
            assert!(
                verifier.verify_model(&model),
                "ay returned Safe with a model that does not validate against the \
                 original problem — that is a false proof, not a completeness win"
            );
            Verdict::Safe
        }
        PortfolioResult::Unsafe(_) => Verdict::Unsafe,
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => Verdict::Unknown,
        other => panic!("unexpected portfolio result variant: {other:?}"),
    }
}

/// The `error` relation of every absent-callee-poisoned ny-cert obligation is
/// fed by a `constraint = true` clause from a reachable block, so the Horn
/// system has no model. `Safe` here is a false proof; `Unsafe` and `Unknown`
/// are both sound.
#[test]
#[timeout(180_000)]
fn nycert_absent_callee_systems_are_never_safe() {
    for (name, smt2) in [
        (
            "ny_cert::rational::Rat::is_negative",
            RAT_IS_NEGATIVE_UNSAFE,
        ),
        ("ny_cert::selfcheck::negated_coeffs", NEGATED_COEFFS_UNSAFE),
    ] {
        let verdict = solve(smt2);
        assert_ne!(
            verdict,
            Verdict::Safe,
            "FALSE PROOF: ay reported Safe for `{name}`, whose lowered CHC derives \
             `error` unconditionally from a reachable basic block \
             (a [trust-absent-callee-assumption] may-panic marker). No model exists."
        );
    }
}

/// Stronger form of the pin above: on this corpus ay actually decides the
/// refutation rather than timing out, so hold that line too. If a future change
/// degrades these to `Unknown` that is sound but is a real capability loss, and
/// it should be a deliberate, visible decision.
#[test]
#[timeout(180_000)]
fn nycert_absent_callee_systems_are_refuted() {
    assert_eq!(
        solve(RAT_IS_NEGATIVE_UNSAFE),
        Verdict::Unsafe,
        "ay should still refute the 7-predicate `Rat::is_negative` absent-callee system"
    );
    assert_eq!(
        solve(NEGATED_COEFFS_UNSAFE),
        Verdict::Unsafe,
        "ay should still refute the 16-predicate `negated_coeffs` absent-callee system"
    );
}

/// The two genuinely-safe obligations from the same ny-cert run. These are the
/// proofs the campaign has actually banked on this path; they must not regress.
#[test]
#[timeout(180_000)]
fn nycert_genuinely_safe_obligations_stay_proved() {
    assert_eq!(
        solve(RATIONAL_VAL_SAFE),
        Verdict::Safe,
        "regression: ay no longer proves `ny_cert::rational::val` panic-free"
    );
    assert_eq!(
        solve(RATIONAL_VAL_CLOSURE_SAFE),
        Verdict::Safe,
        "regression: ay no longer proves `ny_cert::rational::val::{{closure#0}}` panic-free"
    );
}

/// Guards the corpus itself, not the engine: if a future edit ever strips the
/// unconditional error clause out of a fixture, the soundness pins above become
/// vacuous (the mutated system is satisfiable, so `Safe` would be correct and
/// `assert_ne!(Safe)` would be testing nothing). Pin the marker's presence.
#[test]
fn unsafe_fixtures_still_carry_an_unconditional_error_clause() {
    for (name, smt2) in [
        ("rat_is_negative", RAT_IS_NEGATIVE_UNSAFE),
        ("negated_coeffs", NEGATED_COEFFS_UNSAFE),
    ] {
        // Identify `error` from the query clause itself — several of these
        // systems declare more than one nullary predicate, so "first nullary
        // declaration" is not the error relation.
        let error_pred = smt2
            .lines()
            .find_map(|l| {
                l.strip_prefix("(assert (=> ")
                    .and_then(|rest| rest.strip_suffix(" false))"))
                    .filter(|p| !p.contains(' '))
            })
            .unwrap_or_else(|| panic!("{name}: lost the `error => false` query clause"))
            .to_string();
        assert!(
            smt2.contains(&format!("(declare-fun {error_pred} () Bool)")),
            "{name}: query target `{error_pred}` is not a nullary predicate"
        );
        let unconditional = smt2.lines().any(|l| {
            l.starts_with("(assert (forall")
                && l.trim_end().ends_with(&format!("{error_pred})))"))
                && !l.contains("(and (")
        });
        assert!(
            unconditional,
            "{name}: lost the unconditional `... => {error_pred}` may-panic marker; \
             the soundness pins in this file are now vacuous"
        );
    }
}
