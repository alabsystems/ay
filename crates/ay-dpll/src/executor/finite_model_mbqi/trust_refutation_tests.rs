// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A model-check truth decision never rests on a `discharged-trust`
//! refutation, end to end (mutation tests for the probe mode's refusal and the
//! installer's second line).
//!
//! Each auxiliary UNSAT of the model check DECIDES a quantifier's truth value
//! under the fixed candidate model, and that value is what the published `sat`
//! rests on: the gate defers to the grant without re-deciding the quantifier.
//! A refutation vouched for only by a fresh executor running the same code is
//! no check of that decision. Measured on fcdf5b51e: the CLI's default posture
//! published `(forall ((v Int)) (= (* (abs c) v) v))` with `c < 0` as `sat`
//! on such a refutation (`deferred-discharged-trust-full-domain`), and
//! `--rigor strict`, where a directly published `unsat` on the same class is
//! withheld, did the same.

use crate::executor::quantifier_loop::result_mapping::trust_forge::ForgedTrustGuard;
use crate::Executor;

/// The auflia hashmap invariant's unsatisfiable twin: `no_double_binding` is
/// false everywhere, so the invariant's universal fails at `i = 0`. z3 4.8.12
/// answers `unsat`. The model check engages (two leaves, one refinable) and
/// today declines it to `unknown`. Under forged refutations it would decide
/// both universals TRUE, and the residual's confirm solve (never forged) is
/// satisfiable, so a model check that accepted those refutations would
/// publish a WRONG `sat` (measured with the probe mode and the installer both
/// admitting the forged class: `sat` behind a deferred full-domain grant).
const UNSAT_TWIN: &str = "(set-logic ALL)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-fun self () MyHashMap)
(declare-fun good_arg () List)
(declare-fun seq_len_proxy () Int)
(declare-fun invariant (MyHashMap) Bool)
(declare-fun buckets (MyHashMap) (Seq Int))
(declare-fun index_logic ((Seq Int) Int) Int)
(declare-fun good_bucket (MyHashMap List Int) Bool)
(declare-fun no_double_binding (Int) Bool)
(assert (= (invariant self)
           (and (< 0 seq_len_proxy)
                (forall ((i Int))
                  (! (or (and (good_bucket self good_arg i)
                              (no_double_binding (index_logic (buckets self) i)))
                         (not (<= 0 i))
                         (not (< i seq_len_proxy)))
                     :pattern ((good_bucket self good_arg i)))))))
(assert (invariant self))
(assert (= seq_len_proxy 1))
(assert (forall ((x Int)) (not (no_double_binding x))))
(check-sat)
";

/// The satisfiable sibling: the invariant's definition alone (no assertion
/// that it holds). z3 answers `sat`, and the model check decides it in every
/// posture: on checked refutations wherever proofs are produced, and under
/// shedding on the posture's raw admission (`admits_shed_raw_unsat`), which
/// the grant's record does not tell apart.
const SAT_SIBLING: &str = "(set-logic ALL)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-fun self () MyHashMap)
(declare-fun good_arg () List)
(declare-fun seq_len_proxy () Int)
(declare-fun invariant (MyHashMap) Bool)
(declare-fun buckets (MyHashMap) (Seq Int))
(declare-fun index_logic ((Seq Int) Int) Int)
(declare-fun good_bucket (MyHashMap List Int) Bool)
(declare-fun no_double_binding (Int) Bool)
(assert (= (invariant self)
           (and (< 0 seq_len_proxy)
                (forall ((i Int))
                  (! (or (and (good_bucket self good_arg i)
                              (no_double_binding (index_logic (buckets self) i)))
                         (not (<= 0 i))
                         (not (< i seq_len_proxy)))
                     :pattern ((good_bucket self good_arg i)))))))
(check-sat)
";

#[derive(Clone, Copy, Debug)]
enum Posture {
    /// `Executor::new()`: no proof demand.
    Library,
    /// The CLI's default: the best-effort proof sidecar.
    BestEffortProofs,
    /// `--z3-mode`: proof work shed, auxiliary UNSATs admitted raw.
    Shedding,
    /// `--self-check`.
    SelfCheck,
}

const POSTURES: [Posture; 4] = [
    Posture::Library,
    Posture::BestEffortProofs,
    Posture::Shedding,
    Posture::SelfCheck,
];

/// What one solve published.
struct Published {
    verdicts: Vec<String>,
    /// The `model_check_gate.quantified` record.
    record: Option<String>,
    /// Model-check refutations the lane booked as `discharged-trust`.
    trust_refutations: u64,
}

fn solve(smt: &str, posture: Posture) -> Published {
    let commands = ay_frontend::parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::from_secs(30)));
    match posture {
        Posture::Library => {}
        Posture::BestEffortProofs => exec.set_best_effort_produce_proofs(1_000_000),
        Posture::Shedding => exec.set_competition_mode(true),
        Posture::SelfCheck => exec.set_self_check(true),
    }
    let outputs = exec.execute_all(&commands).expect("execute");
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
        trust_refutations: exec.finite_model_lane.discharged_trust_refutations,
    }
}

/// A forged `discharged-trust` refutation decides nothing in any posture: the
/// unsatisfiable twin is never published `sat`, and no full-domain grant is
/// deferred to. `forged > 0` is the non-vacuity check: the solve really
/// reached the model check's refutations. The lane books no trust refutation
/// either: the probe mode refused every forged one before the installer (the
/// second line) ever saw it, so this catches a relaxed mode on its own.
#[test]
fn a_forged_trust_refutation_never_publishes_sat() {
    for posture in POSTURES {
        let guard = ForgedTrustGuard::model_check_refutations();
        let published = solve(UNSAT_TWIN, posture);
        let forged = guard.forged();
        drop(guard);
        let Published {
            verdicts,
            record,
            trust_refutations,
        } = published;
        assert!(
            forged > 0,
            "{posture:?}: the fixture must reach the model check's refutation probes"
        );
        assert!(
            !verdicts.iter().any(|verdict| verdict == "sat"),
            "{posture:?}: a sat resting on a forged trust refutation is the wrong side \
             (z3: unsat); got {verdicts:?}, record {record:?}"
        );
        assert_ne!(
            record.as_deref(),
            Some("deferred-certified-bv-full-domain"),
            "{posture:?}: no grant may rest on a trust refutation"
        );
        assert_eq!(
            trust_refutations, 0,
            "{posture:?}: the probe mode must refuse every forged trust refutation"
        );
    }
}

/// The negative twin: without forging, the model check still decides the
/// satisfiable sibling, and the gate defers to its grant. The refusal costs
/// the trust class only. Under shedding only the verdict is pinned: that grant
/// rests on raw refutations its `certified` record does not tell apart, and
/// this test must not pin that label as correct.
#[test]
fn checked_refutations_still_publish_the_model_check_sat() {
    for posture in POSTURES {
        let published = solve(SAT_SIBLING, posture);
        assert_eq!(published.verdicts, ["sat"], "{posture:?}: z3 answers sat");
        assert_eq!(published.trust_refutations, 0, "{posture:?}");
        if matches!(posture, Posture::Shedding) {
            continue;
        }
        assert_eq!(
            published.record.as_deref(),
            Some("deferred-certified-bv-full-domain"),
            "{posture:?}: the sat rests on the model check's checked grant"
        );
    }
}
