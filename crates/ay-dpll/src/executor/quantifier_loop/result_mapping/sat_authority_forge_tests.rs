// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-certificate producers and `discharged-trust`, end to end (mutation
//! tests for `CheckedIsolatedMode::SatAuthorityDecision` and the trust
//! booking of the certificates the publication gate defers to).
//!
//! Inside a `ForgedTrustGuard::sat_authority_probes` scope every probe whose
//! UNSAT would confirm a quantified conjunct (the gate's confirming
//! obligations, BV-MBQI's symbolic entailment, the finite-table, default-row
//! and constant-interpretation certificates, the CEGQI counterexample-lemma
//! theorems) answers a forged UNSAT of that class, whatever the query: the
//! threat is a WRONG refutation that only a fresh executor running the same
//! code vouches for. Measured before this booking existed: on [`WRONG_SAT`]
//! (unsatisfiable) the forged class published `sat` recorded
//! `deferred-certified-const-interp`.

use crate::executor::quantifier_loop::result_mapping::trust_forge::ForgedTrustGuard;
use crate::Executor;

/// UNSATISFIABLE (z3 4.8.12: `unsat`): at `x = 0` the universal needs
/// `|c| ≥ 5`, against `|c| < 3`.
const WRONG_SAT: &str = "(set-logic ALL)(declare-fun c () Int)\
    (assert (forall ((x (_ BitVec 32))) (>= (+ (bv2nat x) (abs c)) 5)))\
    (assert (< (abs c) 3))(check-sat)";

/// SATISFIABLE (any `c < 0` and `f`); measured: certified by the constant
/// interpretation certificate on checked refutations at strict rigor (at
/// default rigor a finite-table certificate on a `discharged-trust`
/// refutation gets there first, and is recorded as such).
const CERTIFIED: &str = "(set-logic ALL)(declare-fun c () Int)(declare-fun f (Int) Int)\
    (assert (forall ((v Int)) (=> (> v (abs c)) (> (+ v (f v)) (f v)))))\
    (assert (< c 0))(check-sat)";

/// What one solve published, and how many probes the guard forged.
struct Published {
    verdicts: Vec<String>,
    record: Option<String>,
    forged: usize,
}

fn solve(smt: &str, best_effort_proofs: bool, strict_rigor: bool, forge: bool) -> Published {
    let commands = ay_frontend::parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::from_secs(20)));
    exec.set_strict_grant_evidence_required(strict_rigor);
    if best_effort_proofs {
        exec.set_best_effort_produce_proofs(1_000_000);
    }
    let guard = forge.then(ForgedTrustGuard::sat_authority_probes);
    let outputs = exec.execute_all(&commands).expect("execute");
    let forged = guard.map_or(0, |guard| guard.forged());
    let verdicts = outputs
        .into_iter()
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect();
    let record = exec
        .statistics()
        .get_string("model_check_gate.quantified")
        .map(str::to_owned);
    Published {
        verdicts,
        record,
        forged,
    }
}

fn published_sat(published: &Published) -> bool {
    published.verdicts.iter().any(|verdict| verdict == "sat")
}

/// Under strict rigor a forged trust refutation certifies nothing: the
/// unsatisfiable fixture is never published `sat`, in the library and the
/// CLI's default proof posture. `forged > 0` is the non-vacuity check.
#[test]
fn a_forged_trust_refutation_never_publishes_sat_under_strict_rigor() {
    for best_effort_proofs in [false, true] {
        let published = solve(WRONG_SAT, best_effort_proofs, true, true);
        assert!(
            published.forged > 0,
            "proofs={best_effort_proofs}: must reach a probe"
        );
        assert!(
            !published_sat(&published),
            "proofs={best_effort_proofs}: a sat resting on a forged trust refutation is the \
             wrong side (z3: unsat); got {:?}, record {:?}",
            published.verdicts,
            published.record
        );
    }
}

/// At default rigor the class is admitted, as a directly published `unsat` on
/// it is, but never recorded as checked: whatever the forged refutations
/// publish carries a `discharged-trust` record.
#[test]
fn a_forged_trust_certificate_is_recorded_as_such_at_default_rigor() {
    for best_effort_proofs in [false, true] {
        let published = solve(WRONG_SAT, best_effort_proofs, false, true);
        assert!(
            published.forged > 0,
            "proofs={best_effort_proofs}: must reach a probe"
        );
        if published_sat(&published) {
            let record = published.record.as_deref().unwrap_or("none");
            assert!(
                record.starts_with("deferred-discharged-trust-")
                    || record == "confirmed-discharged-trust",
                "proofs={best_effort_proofs}: a sat resting on forged trust refutations \
                 was recorded {record}"
            );
        }
    }
}

/// The negative twin: without forging, checked refutations still certify the
/// satisfiable fixture under strict rigor, recorded as certified; and the
/// same certificate is lost under forged refutations, so it really rests on
/// those probes.
#[test]
fn checked_refutations_still_certify() {
    let published = solve(CERTIFIED, true, true, false);
    assert_eq!(published.verdicts, ["sat"]);
    let record = published.record.as_deref().unwrap_or("none");
    assert!(
        record.starts_with("deferred-certified-"),
        "recorded {record}"
    );
    let forged = solve(CERTIFIED, true, true, true);
    assert!(forged.forged > 0);
    assert!(!published_sat(&forged), "record {:?}", forged.record);
    let unforged = solve(WRONG_SAT, true, false, false);
    assert!(!published_sat(&unforged), "{:?}", unforged.verdicts);
}
