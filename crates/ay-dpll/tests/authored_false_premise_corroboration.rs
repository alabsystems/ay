// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored assertion that ELABORATES to the Boolean constant `false` is
//! still a premise of the query, and the certification funnel must be able to
//! say so.
//!
//! `proof_export_scope_assertions` strips a `false` premise whose PARSED
//! surface is not literally `false`. That rule is about the exported SURFACE —
//! an external checker matches `(assume h false)` against the input text, and
//! `(assert (= 0 1))` does not spell it — and it stays. What it is NOT is a
//! statement about authorship: elaboration folds `(= 0 1)` onto the canonical
//! constant, so the premise is genuinely the user's.
//!
//! Read as authorship, the strip produced a WRONG ANSWER rather than a missing
//! artifact. On the fixture below it removed the only contradictory premise
//! from the strict-proof problem; the corroboration guard in
//! `authored_corroboration_scope` then read the true authored scope as
//! non-monotone and fell back to that deficient problem; and the deferred-trust
//! discharge re-solved only the two SATISFIABLE assertions that remained. A
//! correct ground refutation was withdrawn to
//! `unknown (incomplete self-check-rejected)` — AY reporting that its own
//! fail-closed checker had refuted its own verdict.
//!
//! The ground contradiction here needs the quantifier beside it: without one
//! the query never reaches the deferred-trust arm at all, so the whole class
//! stayed invisible to every plain ground regression.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Runs a script and returns every `check-sat` verdict in order.
fn verdicts(script: &str) -> Vec<String> {
    let commands = parse(script).expect("parse probe script");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("execute probe script")
}

/// A ground contradiction that constant-folds, an E-matched quantifier to force
/// the deferred-trust arm, and a trigger term to fire it.
fn folded_false_with_quantifier(contradiction: &str) -> String {
    format!(
        "(set-logic AUFLIA)
(declare-fun flag () Bool)
(declare-fun P (Int) Bool)
(assert {contradiction})
(assert (= flag (not (forall ((x Int)) (! (P x) :pattern ((P x)))))))
(assert (P 0))
(check-sat)
"
    )
}

/// The exact shape that regressed: `(= 0 1)` is refuted by evaluation alone, so
/// the query is UNSAT whatever the quantifier does.
#[test]
#[timeout(120_000)]
fn assertion_folding_to_false_still_certifies_unsat() {
    assert_eq!(
        verdicts(&folded_false_with_quantifier("(= 0 1)")),
        vec!["unsat"],
        "an authored assertion that elaborates to `false` is a premise of the \
         query; dropping it from the corroboration scope leaves a SATISFIABLE \
         remainder and withdraws a correct refutation to `unknown`"
    );
}

/// The same defect is reachable through every folding route, not just `(= 0 1)`
/// — each of these elaborates to the one canonical `false` term, so each lands
/// on the identical stripped-premise path.
#[test]
#[timeout(120_000)]
fn every_folding_route_onto_false_certifies_unsat() {
    for contradiction in [
        "(< 1 0)",
        "(not (= 3 3))",
        "(and true false)",
        "(distinct 7 7)",
    ] {
        assert_eq!(
            verdicts(&folded_false_with_quantifier(contradiction)),
            vec!["unsat"],
            "`{contradiction}` folds onto the canonical `false` term and must \
             keep its premise status"
        );
    }
}

/// CONTROL: a literally authored `(assert false)` already earned premise status
/// through the parsed surface. It must keep answering exactly as before — the
/// fix widens authorship, it does not reroute the case that already worked.
#[test]
#[timeout(120_000)]
fn literally_authored_false_is_unaffected() {
    assert_eq!(
        verdicts(&folded_false_with_quantifier("false")),
        vec!["unsat"]
    );
}

/// SOUNDNESS CONTROL, and the reason authorship is read from the elaborator's
/// concrete `assert` records rather than from assertion-stack membership.
///
/// The admission must be scoped to the LIVE query. Here the folded-false
/// assertion is popped before the second `check-sat`, whose remaining
/// assertions are satisfiable. If a stale authorship record survived the pop,
/// `false` would be re-admitted to a scope it no longer belongs to and the
/// trivially-UNSAT re-solve would certify a WRONG `unsat`.
///
/// The honest second verdict is a fail-closed `unknown`: AY cannot authorize a
/// total model for the quantified remainder. What it must never be is `unsat`.
#[test]
#[timeout(120_000)]
fn popped_folded_false_grants_no_authority_to_the_next_query() {
    let results = verdicts(
        "(set-logic AUFLIA)
(declare-fun flag () Bool)
(declare-fun P (Int) Bool)
(push 1)
(assert (= 0 1))
(check-sat)
(pop 1)
(assert (= flag (not (forall ((x Int)) (! (P x) :pattern ((P x)))))))
(assert (P 0))
(check-sat)
",
    );
    assert_eq!(
        results[0], "unsat",
        "inside the frame the folded-false premise still refutes"
    );
    assert_ne!(
        results[1], "unsat",
        "the popped premise must not authorize a refutation of the satisfiable \
         assertions that outlive its frame"
    );
}

/// SOUNDNESS CONTROL: nothing about the widened authorship may manufacture a
/// premise where the user never asserted one. The same quantified assertions
/// WITHOUT any contradiction must not be refuted.
#[test]
#[timeout(120_000)]
fn quantified_remainder_alone_is_never_refuted() {
    let results = verdicts(
        "(set-logic AUFLIA)
(declare-fun flag () Bool)
(declare-fun P (Int) Bool)
(assert (= flag (not (forall ((x Int)) (! (P x) :pattern ((P x)))))))
(assert (P 0))
(check-sat)
",
    );
    assert_ne!(
        results[0], "unsat",
        "these assertions are satisfiable; a `false` premise may only ever come \
         from an authored assert"
    );
}
