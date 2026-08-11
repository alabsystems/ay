// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! A symbolic-divisor `mod` over a UF APPLICATION loses the model's UF values.
//!
//! Isolated by controlled variant. BOTH ingredients are required — a symbolic
//! divisor alone is fine, and a UF application alone is fine:
//!
//! | formula                              | AY        | z3    |
//! |--------------------------------------|-----------|-------|
//! | `(= (f k) (g k))`                    | `sat`     | `sat` |
//! | `(= (f k) (mod (g k) 8))` const div  | `sat`     | `sat` |
//! | `(= a (mod b d))` plain vars         | `sat`     | `sat` |
//! | `(= (f k) (mod (g k) d))`            | `unknown` | `sat` |
//!
//! The gate is RIGHT to refuse — it reports
//!
//! ```text
//! :model_check_gate.cannot_confirm_reason
//!     "model commits no value for this application of `f`"
//! :unknown.phase "independent-model-check-gate"
//! ```
//!
//! and the published witness genuinely does not pin it. Compare the
//! constant-divisor case, which publishes complete interpretations:
//!
//! ```text
//! (define-fun f ((x0 Int)) Int 0)
//! (define-fun g ((x0 Int)) Int 0)
//! ```
//!
//! THE CAUSE IS ROUTING, AND NOTHING EVER SOLVES THIS. `mod_div_elim` does not
//! run on this input at all. Measured: `:decisions 0`, `:num-vars 0`,
//! `:num-clauses 0`, and `:term-count` 8 in / 8 out — the elimination mints a
//! `(q, r)` pair and a guarded disjunction, so it cannot have run and left the
//! store untouched. The constant-divisor control reaches `:decisions 9`,
//! `:term-count 43`.
//!
//! The chain: the window is `QfUflia`, but `has_int_div_mod` makes
//! `has_only_uf_lia_theories` false, so it dispatches to `solve_auf_lia`.
//! AUFLIA preprocessing runs only `eliminate_int_mod_div_by_constant`, so a
//! SYMBOLIC divisor survives and `post_preprocess_features.has_int_div_mod` is
//! still set. That enters the div/mod bail ladder in
//! `executor/theories/combined/mod.rs`, whose third rung
//! `try_sat_via_quantifier_consumer_completion_preprocess` accepts the window — every
//! assertion mentions a completable UF — and returns `Sat` after installing a
//! deliberately EMPTY `Model`: `euf_model: None`, `lia_model: None`,
//! `completed_values: {}`, with `sat_validated_by_mod_div_or_branch = true`.
//!
//! So the `Sat` was granted on an interpretation nothing ever built, and the
//! independent gate was the ONLY thing between it and a published wrong answer
//! — `mbqi.rs` names that exact construct as the #quantifier_consumer-arith wrong-SAT
//! hazard. The gate was right, for the fifth time.
//!
//! FIX: route an array-free symbolic-divisor window to the NIA lane before the
//! shortcut can claim it. `solve_uf_lia` already did this; AUFLIA lacked the
//! branch. Proof it is purely routing — the byte-identical formula under
//! `(set-logic QF_UFNIA)` returns `sat` with full `f` and `g` interpretations
//! and `:model_check_gate.result "confirmed-sat"`.
//!
//! FALSIFIED HYPOTHESIS — do not retry. Adding `self_check_authored_assertions`
//! to the model-completion root walks at `completion.rs:908` and `:1184`
//! changes NOTHING here. Now explained: there is no solve and no model to
//! complete FROM, so gathering more completion candidates cannot help.
//!
//! Two-sided assertions naming the exact verdict: a one-sided pin is how a
//! wrong `unsat` hid in this suite for an entire session.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

fn verdict(smt: &str) -> SolverOutcome {
    run_executor_smt_with_timeout(smt, 30).expect("execution should succeed")
}

/// The defect, minimal.
#[test]
#[timeout(30_000)]
fn symbolic_divisor_mod_over_uf_application_is_sat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(declare-fun k2 () Int)
(declare-fun d () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (f k2) (mod (g k2) d)))
(check-sat)
"#
        ),
        SolverOutcome::Sat,
        "satisfiable — z3 agrees; AY computes it but cannot publish a witness \
         that pins `f`, so the gate correctly declines"
    );
}

/// CONTROL: a CONSTANT divisor over the same UF applications already works and
/// publishes complete interpretations. Must keep passing.
#[test]
#[timeout(30_000)]
fn constant_divisor_mod_over_uf_application_is_sat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(declare-fun k2 () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (f k2) (mod (g k2) 8)))
(check-sat)
"#
        ),
        SolverOutcome::Sat,
        "control: constant divisor pins both UF interpretations"
    );
}

/// CONTROL: a symbolic divisor over PLAIN VARIABLES already works. Must keep
/// passing — together with the one above it pins that BOTH ingredients are
/// needed, so a fix must not simply disable the rewrite.
#[test]
#[timeout(30_000)]
fn symbolic_divisor_mod_over_plain_variables_is_sat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun d () Int)
(assert (= a (mod b d)))
(check-sat)
"#
        ),
        SolverOutcome::Sat,
        "control: symbolic divisor alone is fine"
    );
}

/// The UF application does NOT have to feed the `mod`. Pins the corrected
/// account: any completable UF in the window satisfies the shortcut's admission
/// guard, so a plain-variable dividend fails the same way.
#[test]
#[timeout(30_000)]
fn symbolic_divisor_mod_with_uf_only_on_the_other_side_is_sat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(declare-fun k2 () Int)
(declare-fun b () Int)
(declare-fun d () Int)
(declare-fun f (Int) Int)
(assert (= (f k2) (mod b d)))
(check-sat)
"#
        ),
        SolverOutcome::Sat,
        "the UF application need not be the mod's argument — the shortcut's \
         guard only asks that SOME assertion mentions a completable UF"
    );
}

/// REJECTING DIRECTION. `0 <= (mod x d) < d` for `d > 0`, so `(f k2) >= d` is a
/// contradiction. z3 agrees `unsat`.
///
/// This is the load-bearing canary for the re-route: it is refuted by rung 1 of
/// the ladder (`try_unsat_via_mod_free_subset`, which injects the Euclidean
/// bound axioms), which runs BEFORE the new NIA branch. A fix inserted at the
/// wrong rung would swallow this refutation and publish `sat` — a wrong SAT.
#[test]
#[timeout(30_000)]
fn a_remainder_at_least_the_divisor_is_still_unsat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(declare-fun k2 () Int)
(declare-fun d () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (> d 0))
(assert (= (f k2) (mod (g k2) d)))
(assert (>= (f k2) d))
(check-sat)
"#
        ),
        SolverOutcome::Unsat,
        "a remainder cannot reach its positive divisor — deciding this window \
         must not lose the refutation"
    );
}

/// REJECTING DIRECTION, lower bound. A remainder is non-negative for `d > 0`.
#[test]
#[timeout(30_000)]
fn a_negative_remainder_is_still_unsat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(declare-fun k2 () Int)
(declare-fun d () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (> d 0))
(assert (= (f k2) (mod (g k2) d)))
(assert (< (f k2) 0))
(check-sat)
"#
        ),
        SolverOutcome::Unsat,
        "a remainder is non-negative for a positive divisor"
    );
}

/// REJECTING DIRECTION, and the reason the route guard reads the POST-
/// preprocessing window.
///
/// `n` is symbolic in the source but `(= n 8)` constant-folds it during
/// preprocessing, so the `mod` is fully eliminated and the ordinary AUFLIA
/// route decides this. `(g k) = 10`, so `(f k) = 10 mod 8 = 2`, and
/// `(distinct (f k) 2)` contradicts it. z3 agrees `unsat`.
///
/// A guard that tests the PRE-preprocessing window sees a symbolic divisor
/// here, diverts the window, and loses the refutation — measured 3/3
/// deterministic `unsat` -> `unknown` on exactly this idiom, which is the
/// hashmap bucket-index shape this whole area is about. Keep this test next to
/// the symbolic cases so the distinction cannot be quietly dropped.
#[test]
#[timeout(30_000)]
fn a_divisor_that_constant_folds_is_still_decided_unsat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(declare-fun k () Int)
(declare-fun n () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= n 8))
(assert (= (f k) (mod (g k) n)))
(assert (= (g k) 10))
(assert (distinct (f k) 2))
(check-sat)
"#
        ),
        SolverOutcome::Unsat,
        "10 mod 8 = 2, so `(distinct (f k) 2)` is contradictory — a divisor \
         that constant-folds must keep taking the route that decides it"
    );
}

/// The `div` twin of the case above, same reasoning: `10 div 8 = 1`.
#[test]
#[timeout(30_000)]
fn a_div_divisor_that_constant_folds_is_still_decided_unsat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(declare-fun k () Int)
(declare-fun n () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= n 8))
(assert (= (f k) (div (g k) n)))
(assert (= (g k) 10))
(assert (distinct (f k) 1))
(check-sat)
"#
        ),
        SolverOutcome::Unsat,
        "10 div 8 = 1"
    );
}
