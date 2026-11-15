// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The gate's confirming obligations and `discharged-trust` (mutation tests
//! for `GateUnsat::Confirms`).
//!
//! When a universal's truth under the emitted model is decided by a nested
//! refutation of its negated instance, the published `sat` rests on that
//! refutation. On fcdf5b51e the model check refused one vouched for only by a
//! fresh executor running the same code, and the gate then accepted the very
//! same class for the same obligation, at every rigor, and recorded
//! `confirmed` (measured on `∀v w. v > |c| → v + |w| ≥ 0` with `c < 0`). Now
//! strict rigor refuses it, and default rigor (where a directly published
//! `unsat` on the class is admitted too) records `confirmed-discharged-trust`.
//! Controlled candidates isolate the gate from search, as in
//! `affine_substitution_tests`.

#![cfg(test)]

use ay_frontend::parse;
use ay_lia::LiaModel;
use num_bigint::BigInt;

use super::*;
use crate::executor::quantifier_loop::result_mapping::trust_forge::ForgedTrustGuard;

/// FALSE at `c = -1` (`v = 2`, `w = 0`): `|w|` keeps the body nonlinear in a
/// binder, so neither exact evaluation nor the affine route decides it and
/// the gate refutes the negated instance under the pin for `c`.
const FALSIFIED: &str = "(set-logic ALL)(declare-const c Int)\
    (assert (forall ((v Int) (w Int)) (=> (> v (abs c)) (>= (+ v (abs w)) 5))))";

/// TRUE at `c = 5`, decided by a nested refutation that has a checked proof.
const HOLDS: &str = "(set-logic ALL)(declare-const c Int)\
    (assert (forall ((v Int) (w Int)) (=> (and (> v c) (> w v)) (> w 3))))";

fn candidate(source: &str, value: i64, strict_rigor: bool) -> Executor {
    let mut exec = Executor::new();
    exec.set_strict_grant_evidence_required(strict_rigor);
    let commands = parse(source).expect("valid source");
    let outputs = exec.execute_all(&commands).expect("load without solving");
    assert!(outputs.is_empty(), "fixtures must not run a query");
    exec.begin_external_decision_query(false);
    let mut values = DetHashMap::default();
    let c = exec.ctx.terms.mk_var("c", Sort::Int);
    values.insert(c, BigInt::from(value));
    let mut model = Model::empty();
    model.lia_model = Some(LiaModel { values });
    exec.last_model = Some(model);
    exec
}

fn label(outcome: &QuantifiedModelCheck) -> &'static str {
    match outcome {
        QuantifiedModelCheck::Confirmed => "confirmed",
        QuantifiedModelCheck::Refuted { .. } => "refuted",
        QuantifiedModelCheck::Indeterminate(reason) => reason,
        QuantifiedModelCheck::Deferred => "deferred",
    }
}

/// `(outcome, forged)` for the root under candidate `c = value`, optionally
/// with every sat-authority probe forged as a `discharged-trust` refutation.
fn check(
    source: &str,
    value: i64,
    strict_rigor: bool,
    forge: bool,
) -> (QuantifiedModelCheck, usize) {
    let mut exec = candidate(source, value, strict_rigor);
    let root = *exec.ctx.assertions.last().expect("quantified root");
    let guard = forge.then(ForgedTrustGuard::sat_authority_probes);
    let outcome = exec.check_quantified_conjunct_against_model(root);
    (outcome, guard.map_or(0, |guard| guard.forged()))
}

/// `(published, record, forged)` through the public funnel.
fn publish(
    source: &str,
    value: i64,
    strict_rigor: bool,
    forge: bool,
) -> (SolveResult, Option<String>, usize) {
    let mut exec = candidate(source, value, strict_rigor);
    let guard = forge.then(ForgedTrustGuard::sat_authority_probes);
    let published = exec.apply_quantified_model_failclosed_gate(SolveResult::Sat);
    let forged = guard.map_or(0, |guard| guard.forged());
    let record = exec
        .last_statistics
        .get_string("model_check_gate.quantified")
        .map(str::to_owned);
    (published, record, forged)
}

/// Under strict rigor a forged trust refutation confirms nothing: neither the
/// falsified universal (where accepting it is a wrong `sat`) nor a true one.
/// `forged > 0` is the non-vacuity check.
#[test]
fn a_forged_trust_refutation_confirms_nothing_under_strict_rigor() {
    for (name, source, value) in [("falsified", FALSIFIED, -1), ("holds", HOLDS, 5)] {
        let (outcome, forged) = check(source, value, true, true);
        assert!(
            forged > 0,
            "{name}: the gate must reach a confirming obligation"
        );
        assert!(
            !matches!(outcome, QuantifiedModelCheck::Confirmed),
            "{name}: only checked evidence confirms under --rigor strict; got {}",
            label(&outcome)
        );
        let (published, record, forged) = publish(source, value, true, true);
        assert!(
            forged > 0,
            "{name}: the funnel must reach a confirming obligation"
        );
        assert_eq!(published, SolveResult::Unknown, "{name}: record {record:?}");
    }
}

/// At default rigor the class is admitted, as a directly published `unsat` on
/// it is, but the record says so: a confirmation resting on a forged trust
/// refutation is `confirmed-discharged-trust`, never `confirmed`.
#[test]
fn a_trust_confirmation_is_recorded_as_such_at_default_rigor() {
    for (name, source, value) in [("falsified", FALSIFIED, -1), ("holds", HOLDS, 5)] {
        let (published, record, forged) = publish(source, value, false, true);
        assert!(
            forged > 0,
            "{name}: the funnel must reach a confirming obligation"
        );
        assert_eq!(published, SolveResult::Sat, "{name}: record {record:?}");
        assert_eq!(
            record.as_deref(),
            Some("confirmed-discharged-trust"),
            "{name}: a trust-resting confirmation must be recorded as such"
        );
    }
}

/// The negative twin: without forging, the same confirming route decides the
/// universal on checked evidence at either rigor (it holds at `c = 5`, a
/// checked witness refutes it at `c = -1`), and the record is `confirmed`.
#[test]
fn checked_evidence_still_decides_and_is_recorded_confirmed() {
    for strict_rigor in [false, true] {
        let (outcome, _) = check(HOLDS, 5, strict_rigor, false);
        assert!(
            matches!(outcome, QuantifiedModelCheck::Confirmed),
            "strict={strict_rigor}: c = 5 satisfies the universal; got {}",
            label(&outcome)
        );
        let (published, record, _) = publish(HOLDS, 5, strict_rigor, false);
        assert_eq!(published, SolveResult::Sat, "strict={strict_rigor}");
        assert_eq!(
            record.as_deref(),
            Some("confirmed"),
            "strict={strict_rigor}"
        );
        let (outcome, _) = check(FALSIFIED, -1, strict_rigor, false);
        assert!(
            matches!(outcome, QuantifiedModelCheck::Refuted { .. }),
            "strict={strict_rigor}: c = -1 falsifies the universal; got {}",
            label(&outcome)
        );
    }
}
