// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::thread;
use std::time::{Duration, Instant};

use num_bigint::BigInt;

use super::*;
use crate::EvidenceShape;

mod held_writer;
mod refusal_profile;

fn replay_claim(name: &str) -> crate::cert_io::ReplayClaim {
    crate::cert_io::ReplayClaim {
        claim: name.to_owned(),
        device: "test-device".to_owned(),
        method: "test-method".to_owned(),
        arithmetic: "exact".to_owned(),
        nodes_visited: None,
        node_budget: 0,
        outcome: "exhausted".to_owned(),
        nondeterminism: Vec::new(),
        reproduce: "unit test".to_owned(),
        tcb: "unit-test".to_owned(),
    }
}

fn optimal(value: i64) -> Outcome {
    Outcome::Optimal {
        value: BigRational::from_integer(BigInt::from(value)),
        model_values: vec![BigRational::zero()],
        cert: None,
    }
}

fn infeasible() -> Outcome {
    Outcome::Infeasible {
        cert: None,
        tree_cert: None,
    }
}

fn objective_session() -> (BabSession, Vec<(u32, f64)>) {
    let mut model = Model::new();
    let x = model.add_binary_col();
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    let objective = vec![(x.index() as u32, 1.0)];
    (
        BabSession::new(model, &SolveOpts::new()).expect("valid test session"),
        objective,
    )
}

#[test]
fn timed_session_checks_materialize_fresh_deadlines_and_restore_caller_options() {
    let _ = take_attempt_observations();
    let mut model = Model::new();
    let x = model.add_col(0.0, 1.0);
    model.add_row(0.0, 1.0, &[(x, 1.0)]);
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(30));
    let mut session = BabSession::new(model, &opts).expect("valid timed session");

    let _ = session.check().expect("first check");
    assert_eq!(session.opts.time_limit, Some(Duration::from_secs(30)));
    assert_eq!(session.opts.deadline, opts.deadline);
    thread::sleep(Duration::from_millis(1));
    let _ = session.check().expect("second check");
    assert_eq!(session.opts.time_limit, Some(Duration::from_secs(30)));
    assert_eq!(session.opts.deadline, opts.deadline);

    let attempts = take_attempt_observations();
    assert_eq!(attempts.len(), 2);
    assert!(attempts[0].deadline.is_some());
    assert!(attempts[1].deadline > attempts[0].deadline);
    assert!(attempts
        .iter()
        .all(|attempt| attempt.time_limit == Some(Duration::from_secs(30))));
}

#[test]
fn caught_attempt_panic_restores_caller_options_and_session_reuse() {
    let _ = take_attempt_observations();
    let mut model = Model::new();
    model.add_col(0.0, 1.0);
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(30));
    let mut session = BabSession::new(model, &opts).expect("valid timed session");
    panic_after_next_attempt_deadline();

    let panic = catch_unwind(AssertUnwindSafe(|| session.check()));
    assert!(panic.is_err());
    assert_eq!(session.opts.time_limit, Some(Duration::from_secs(30)));
    assert_eq!(session.opts.deadline, opts.deadline);
    let _ = session.check().expect("session remains reusable");
    let attempts = take_attempt_observations();
    assert_eq!(attempts.len(), 2);
    assert!(attempts
        .iter()
        .all(|attempt| attempt.time_limit == Some(Duration::from_secs(30))));
}

#[test]
fn pinned_deadline_retains_configured_certificate_budget_duration() {
    let started = Instant::now();
    let mut short = SolveOpts::new().with_time_limit(Duration::from_secs(4));
    short.deadline = short.effective_deadline(started);
    let pinned = short.deadline.expect("time limit must materialize");

    assert_eq!(short.time_limit, Some(Duration::from_secs(4)));
    assert_eq!(
        short.effective_deadline(started + Duration::from_secs(1)),
        Some(pinned),
        "later nested deadline calculations must keep the first absolute pin"
    );
    assert_eq!(configured_cert_grace(&short), Duration::from_secs(1));

    let long = SolveOpts::new().with_time_limit(Duration::from_mins(1));
    assert_eq!(configured_native_cert_cap(&long), Duration::from_secs(9));
}

#[test]
fn unrepresentable_native_certificate_cap_retains_the_bounded_budget() {
    let now = Instant::now();
    assert!(now.checked_add(Duration::MAX).is_none());
    let fallback = now + Duration::from_secs(5);

    let budget = cap_native_cert_budget(
        Budget {
            deadline: Some(fallback),
            max_iters: 17,
        },
        now,
        Duration::MAX,
    );
    assert_eq!(budget.deadline, Some(fallback));
    assert_eq!(budget.max_iters, 17);
}

#[test]
fn deferred_optimum_names_the_below_floor_dual_claim() {
    let _ = crate::cert_io::ledger::take();
    let (mut session, objective) = objective_session();
    let solved = SolvedObjective {
        coeffs: &objective,
        sense: Sense::Minimize,
        offset: 0.0,
        exact: None,
    };
    assert!(session
        .admit_or_defer(
            &crate::claim::SPECIALIZED_PB_REPLAY,
            optimal(0),
            &solved,
            vec![replay_claim("held-optimum")],
            Finisher::ExactReduction,
        )
        .is_none());
    assert_eq!(
        session.deferred_lane(),
        Some(("specialized-pb", "no-better-than"))
    );
}

#[test]
fn resolver_trap_retains_claim_and_rejects_all_decided_disagreements() {
    let _ = crate::cert_io::ledger::take();
    let (mut session, objective) = objective_session();
    let solved = SolvedObjective {
        coeffs: &objective,
        sense: Sense::Minimize,
        offset: 0.0,
        exact: None,
    };
    session.deferred_claim = Some(crate::claim::Deferred {
        lane: "held-refutation",
        outcome: infeasible(),
        replay_claims: vec![replay_claim("retained-refutation")],
        first_refusal: crate::claim::AnchorFirstRefusal {
            until: Instant::now() + Duration::from_secs(1),
        },
    });
    let point = Outcome::Feasible {
        model_values: vec![BigRational::zero()],
        incumbent_only: true,
        dual_bound: None,
    };
    let result = session.publish_deferred_if_native_did_not_decide(point, &solved);
    assert!(matches!(
        result,
        Outcome::Unknown {
            reason: UnknownReason::WitnessRejected { .. }
        }
    ));
    assert_eq!(
        crate::cert_io::ledger::take()[0].claim,
        "retained-refutation"
    );

    assert!(!outcomes_are_compatible(
        &optimal(1),
        &optimal(2),
        &session.model
    ));
    assert!(!outcomes_are_compatible(
        &Outcome::Unbounded,
        &optimal(1),
        &session.model
    ));
    assert!(!outcomes_are_compatible(
        &optimal(1),
        &Outcome::Unbounded,
        &session.model
    ));
    assert!(outcomes_are_compatible(
        &Outcome::Unbounded,
        &Outcome::Feasible {
            model_values: vec![BigRational::zero()],
            incumbent_only: true,
            dual_bound: None,
        },
        &session.model,
    ));
}

#[test]
fn compatibility_uses_only_rigorous_bounds_and_rejects_better_points() {
    for sense in [Sense::Minimize, Sense::Maximize] {
        let mut model = Model::new();
        let x = model.add_col(0.0, 2.0);
        model.set_objective(&[(x, 1.0)], sense);
        let bounded = Outcome::Bound {
            dual_bound: BigRational::from_integer(BigInt::from(1)),
            rigorous: true,
        };
        let bounded_point = Outcome::Feasible {
            model_values: vec![BigRational::from_integer(BigInt::from(1))],
            incumbent_only: true,
            dual_bound: Some(BigRational::from_integer(BigInt::from(1))),
        };
        assert!(!outcomes_are_compatible(
            &Outcome::Unbounded,
            &bounded,
            &model
        ));
        assert!(!outcomes_are_compatible(
            &bounded_point,
            &Outcome::Unbounded,
            &model
        ));
        let heuristic_bound = Outcome::Bound {
            dual_bound: BigRational::from_integer(BigInt::from(1)),
            rigorous: false,
        };
        assert!(outcomes_are_compatible(
            &Outcome::Unbounded,
            &heuristic_bound,
            &model
        ));
        assert!(outcomes_are_compatible(
            &heuristic_bound,
            &Outcome::Unbounded,
            &model
        ));

        let claimed = match sense {
            Sense::Minimize => BigRational::from_integer(BigInt::from(1)),
            Sense::Maximize => BigRational::zero(),
        };
        let better = match sense {
            Sense::Minimize => BigRational::zero(),
            Sense::Maximize => BigRational::from_integer(BigInt::from(1)),
        };
        let optimum = Outcome::Optimal {
            value: claimed.clone(),
            model_values: vec![claimed],
            cert: None,
        };
        let crossing_heuristic = Outcome::Bound {
            dual_bound: match sense {
                Sense::Minimize => BigRational::from_integer(BigInt::from(2)),
                Sense::Maximize => BigRational::from_integer(BigInt::from(-1)),
            },
            rigorous: false,
        };
        assert!(outcomes_are_compatible(
            &optimum,
            &crossing_heuristic,
            &model
        ));
        assert!(outcomes_are_compatible(
            &crossing_heuristic,
            &optimum,
            &model
        ));
        let better_point = Outcome::Feasible {
            model_values: vec![better],
            incumbent_only: true,
            dual_bound: None,
        };
        assert!(!outcomes_are_compatible(&optimum, &better_point, &model));
        assert!(!outcomes_are_compatible(&better_point, &optimum, &model));
    }
}

fn singleton_substitution_model() -> Model {
    let mut model = Model::new();
    let x = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let z = model.add_binary_col();
    model.add_row(1.0, 1.0, &[(x, 1.0), (z, 1.0)]);
    model.set_objective(&[(x, 1.0), (z, 1.0)], Sense::Minimize);
    model
}

#[test]
fn pb_portfolio_optimum_defers_to_the_anchor_certificate_in_every_posture() {
    for require_certificates in [false, true] {
        let opts = SolveOpts::new()
            .with_time_limit(Duration::from_secs(5))
            .with_require_certificates(require_certificates);
        let mut session =
            BabSession::new(singleton_substitution_model(), &opts).expect("valid singleton model");
        let outcome = session.check().expect("singleton solve");
        let Outcome::Optimal { cert, .. } = outcome else {
            panic!("expected certified optimum")
        };
        assert!(cert.is_some(), "the native succinct certificate must win");
        assert_eq!(
            session.deferred_lane(),
            Some(("pb-portfolio", "no-better-than"))
        );
        assert!(session
            .replay_claims()
            .iter()
            .any(|claim| claim.claim == "pb-portfolio-projection-optimal"));
    }
}

fn specialized_pb_optimization_model() -> Model {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    model.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    model.set_objective(&[(x, 1.0), (y, 1.0)], Sense::Minimize);
    model
}

#[test]
fn specialized_pb_optimum_defers_to_a_verified_anchor_certificate_in_every_posture() {
    for require_certificates in [false, true] {
        let opts = SolveOpts::new()
            .with_time_limit(Duration::from_secs(5))
            .with_require_certificates(require_certificates);
        let mut session = BabSession::new(specialized_pb_optimization_model(), &opts)
            .expect("valid specialized-PB model");
        let outcome = session.check().expect("specialized-PB solve");
        let Outcome::Optimal { value, cert, .. } = outcome else {
            panic!("expected certified optimum")
        };
        assert_eq!(value, BigRational::from_integer(BigInt::from(1)));
        cert.expect("the native succinct certificate must win")
            .verify(&session.model)
            .expect("native certificate must verify against the source model");
        assert_eq!(
            session.deferred_lane(),
            Some(("specialized-pb", "no-better-than"))
        );
        assert!(session
            .replay_claims()
            .iter()
            .any(|claim| claim.claim == "pb-projection-optimal"));
    }
}

fn parity_optimization_model() -> Model {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let slack = model.add_int_col(0.0, f64::INFINITY);
    model.add_row(-1.0, -1.0, &[(x, 1.0), (slack, -2.0)]);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    model
}

#[test]
fn parity_optimum_is_posture_independent_and_keeps_replay_evidence() {
    #[derive(Debug, PartialEq, Eq)]
    struct EvidenceObservation {
        deferred_lane: Option<(&'static str, &'static str)>,
        replay_claims: Vec<crate::cert_io::ReplayClaim>,
    }

    let mut evidence_observations = Vec::new();
    for require_certificates in [false, true] {
        let opts = SolveOpts::new()
            .with_time_limit(Duration::from_secs(5))
            .with_require_certificates(require_certificates);
        let mut session =
            BabSession::new(parity_optimization_model(), &opts).expect("valid parity model");
        let outcome = session.check().expect("parity solve");
        let shape = outcome.evidence_shape(&session.model);
        match (require_certificates, outcome) {
            (
                false,
                Outcome::Optimal {
                    value, cert: None, ..
                },
            ) => {
                assert_eq!(value, BigRational::from_integer(BigInt::from(1)));
                assert!(matches!(shape, EvidenceShape::MissingFields { .. }));
            }
            (
                true,
                Outcome::Unknown {
                    reason: UnknownReason::CertificateUnavailable,
                },
            ) => {
                assert!(matches!(shape, EvidenceShape::MissingFields { .. }));
            }
            (_, other) => panic!("unexpected parity policy outcome: {other:?}"),
        }
        evidence_observations.push(EvidenceObservation {
            deferred_lane: session.deferred_lane(),
            replay_claims: session.replay_claims().to_vec(),
        });
    }

    assert_eq!(evidence_observations[0], evidence_observations[1]);
    let observation = &evidence_observations[0];
    // This fixture has an integrality gap, so native search has no stronger
    // typed dual artifact. Full policy therefore declines the bare optimum,
    // but both postures perform the same parity work, engage the same floor,
    // and preserve the same honest replay evidence.
    assert_eq!(
        observation.deferred_lane,
        Some(("parity-optimum", "no-better-than"))
    );
    assert!(observation
        .replay_claims
        .iter()
        .any(|claim| claim.claim == "parity-enumeration-optimal"));
}

#[test]
fn typed_single_row_refutation_closes_without_deferral_under_full_policy() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let z = model.add_binary_col();
    model.add_row(17.0, 18.0, &[(x, 6.0), (y, 10.0), (z, 14.0)]);
    let opts = SolveOpts::new()
        .with_time_limit(Duration::from_secs(5))
        .with_require_certificates(true);
    let mut session = BabSession::new(model, &opts).expect("valid weighted-binary model");
    assert!(matches!(session.check(), Ok(Outcome::Infeasible { .. })));
    assert!(session.single_row_dp_infeasibility_certificate().is_some());
    assert_eq!(session.deferred_lane(), None);
}
