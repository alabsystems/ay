// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Solver-free public replay controls exercised on deciding ground evidence.

#![cfg(test)]

use super::*;
use crate::engine_result::ValidationEvidence;
use crate::ground_derivation::{
    validate_ground_derivation, GroundDerivation, GroundDerivationStep,
};
use crate::{
    ChcEngineResult, ChcReplayPayloadFormat as Format, ClauseBody, Counterexample, HornClause,
    VerifiedCounterexample,
};
use std::cell::Cell;

mod ambient_controls;
mod bound_cancellation_tests;
mod cancellation_tests;
mod deadline_tests;
mod retained_settlement;

const BUDGET: Duration = Duration::from_secs(600);

fn truth_parts() -> (ChcProblem, GroundDerivation) {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    let derivation = GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: 0,
            env: Default::default(),
            premises: vec![],
        }],
        query_step: 0,
    };
    validate_ground_derivation(&problem, &derivation).unwrap();
    (problem, derivation)
}

fn truth_run() -> ChcPdrProofRun {
    let (problem, derivation) = truth_parts();
    let counterexample = Counterexample::new(vec![]).with_ground_derivation(derivation);
    ChcPdrProofRun::new(
        problem,
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(counterexample)),
        "ground-progress-test",
    )
}

fn binding(run: &ChcPdrProofRun, format: Format) -> CheckedReplayBinding {
    let engine = run.metadata.engine.clone();
    let mut options = ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default());
    options.proof_mode = format!("checked-replay:{engine}");
    let solver = ChcProofSolverIdentity::new(engine);
    let obligation_id = format!(
        "ay-chc:checked-replay:{}",
        run.metadata.normalized_input_sha256
    );
    let bytes = match format {
        Format::GroundDerivationV1 => run.unsafe_ground_derivation_artifact_bytes(),
        Format::GroundDerivationV2 => run.unsafe_ground_derivation_artifact_v2_bytes(),
        Format::CompactGroundDerivationV1 => run.unsafe_compact_ground_derivation_artifact_bytes(),
        Format::SmtlibV1 => panic!("fixture is a ground derivation"),
    }
    .unwrap()
    .unwrap();
    let query =
        ChcProofArtifactDigest::from_bytes(super::super::replay_payload_role(format), &bytes);
    let evidence = ChcReplayEvidence::new(
        run.metadata.normalized_input_sha256.clone(),
        options.identity_sha256(),
        solver.identity_sha256(),
        obligation_id.clone(),
        run.metadata.result.clone(),
        run.metadata.proof_status.clone(),
    )
    .with_replay_obligation(
        ChcReplayObligationArtifact::new(ChcReplayObligationKind::TraceValidity, query)
            .with_payload_format(format),
    );
    CheckedReplayBinding {
        options,
        solver,
        obligation_id,
        base_evidence: Some(evidence),
    }
}

#[derive(Clone, Copy, Debug)]
enum Mode {
    Default,
    Bound(Format),
}

impl Mode {
    fn run(
        self,
        run: &ChcPdrProofRun,
        callback: &mut dyn FnMut() -> bool,
    ) -> ChcResult<ChcCheckedReplayRun> {
        match self {
            Self::Default => run.run_checked_replay_with_progress(BUDGET, callback),
            Self::Bound(format) => {
                let binding = binding(run, format);
                run.run_checked_replay_with_binding_and_progress(
                    binding.options,
                    binding.solver,
                    binding.obligation_id,
                    binding.base_evidence,
                    BUDGET,
                    callback,
                )
            }
        }
    }

    fn legacy(self, run: &ChcPdrProofRun) -> ChcResult<ChcCheckedReplayRun> {
        match self {
            Self::Default => run.run_checked_replay(BUDGET),
            Self::Bound(format) => {
                let binding = binding(run, format);
                run.run_checked_replay_with_binding(
                    binding.options,
                    binding.solver,
                    binding.obligation_id,
                    binding.base_evidence,
                    BUDGET,
                )
            }
        }
    }
}

fn assert_same(actual: &ChcCheckedReplayRun, expected: &ChcCheckedReplayRun) {
    assert_eq!(actual.summary(), expected.summary());
    assert_eq!(
        actual.manifest().to_json_value(),
        expected.manifest().to_json_value()
    );
    assert_eq!(
        actual.proof_run().metadata().to_json_value(),
        expected.proof_run().metadata().to_json_value()
    );
    assert_eq!(actual.problem_bytes(), expected.problem_bytes());
    assert_eq!(actual.certificate_bytes(), expected.certificate_bytes());
    assert_eq!(actual.run_log_bytes(), expected.run_log_bytes());
    assert_eq!(actual.replay_log_bytes(), expected.replay_log_bytes());
    assert_eq!(
        actual.checked_report_bytes(),
        expected.checked_report_bytes()
    );
    let actual: Vec<_> = actual
        .obligation_payloads()
        .map(|row| row.payload_bytes())
        .collect();
    let expected: Vec<_> = expected
        .obligation_payloads()
        .map(|row| row.payload_bytes())
        .collect();
    assert_eq!(actual, expected);
}

fn assert_interrupted<T>(result: ChcResult<T>) {
    let Err(error) = result else {
        panic!("refusal must not publish checked evidence")
    };
    assert!(error.to_string().contains("interrupted"), "{error}");
}

#[test]
fn public_progress_preserves_default_and_explicit_ground_binding_bytes() {
    let run = truth_run();
    for mode in [
        Mode::Default,
        Mode::Bound(Format::GroundDerivationV1),
        Mode::Bound(Format::GroundDerivationV2),
    ] {
        let expected = mode.legacy(&run).unwrap();
        let actual = mode.run(&run, &mut || true).unwrap();
        assert_same(&actual, &expected);
        assert!(actual.manifest().trust_full_verifier_admissible());
        let expected_format = match mode {
            Mode::Default => Format::GroundDerivationV1,
            Mode::Bound(format) => format,
        };
        assert_eq!(
            actual.summary().obligations[0].payload_format,
            expected_format
        );
    }
}

#[test]
fn default_identity_matches_the_equivalent_explicit_binding() {
    let run = truth_run();
    let default = Mode::Default.run(&run, &mut || true).unwrap();
    let explicit = Mode::Bound(Format::GroundDerivationV1)
        .run(&run, &mut || true)
        .unwrap();
    assert_same(&default, &explicit);
}

#[test]
fn every_public_callback_including_final_publication_is_terminal() {
    let run = truth_run();
    let original = run.metadata().to_json_value();
    for mode in [
        Mode::Default,
        Mode::Bound(Format::GroundDerivationV1),
        Mode::Bound(Format::GroundDerivationV2),
    ] {
        let mut total = 0;
        let expected = mode
            .run(&run, &mut || {
                total += 1;
                true
            })
            .unwrap();
        assert!(
            total > 10,
            "exercise export, fresh replay and final metadata phases"
        );
        for refused in 1..=total {
            let mut calls = 0;
            assert_interrupted(mode.run(&run, &mut || {
                calls += 1;
                calls != refused
            }));
            assert_eq!(calls, refused, "{mode:?}: no retry after refusal {refused}");
        }
        assert_same(&mode.run(&run, &mut || true).unwrap(), &expected);
        assert_eq!(run.metadata().to_json_value(), original);
    }
}

struct ObservedId<'a> {
    conversions: &'a Cell<usize>,
}

impl From<ObservedId<'_>> for String {
    fn from(value: ObservedId<'_>) -> Self {
        value.conversions.set(value.conversions.get() + 1);
        "observed-id".to_string()
    }
}

#[test]
fn pre_refusal_prevents_opaque_binding_conversion() {
    let run = truth_run();
    let conversions = Cell::new(0);
    let mut calls = 0;
    assert_interrupted(run.run_checked_replay_with_binding_and_progress(
        ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default()),
        ChcProofSolverIdentity::new("test"),
        ObservedId {
            conversions: &conversions,
        },
        None,
        BUDGET,
        &mut || {
            calls += 1;
            calls != 1
        },
    ));
    assert_eq!(calls, 1);
    assert_eq!(conversions.get(), 0);
}

#[test]
fn post_conversion_refusal_cannot_restart_progress_in_worker() {
    let run = truth_run();
    let conversions = Cell::new(0);
    let mut calls = 0;
    let mut refused_at = None;
    // Refuse the FIRST poll after the supplied-ID conversion. The retained
    // entry owner polls before and after each admission debit, so that is not
    // a fixed callback index.
    assert_interrupted(run.run_checked_replay_with_binding_and_progress(
        ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default()),
        ChcProofSolverIdentity::new("test"),
        ObservedId {
            conversions: &conversions,
        },
        None,
        BUDGET,
        &mut || {
            calls += 1;
            if refused_at.is_none() && conversions.get() == 1 {
                refused_at = Some(calls);
            }
            refused_at.is_none()
        },
    ));
    let refused_at = refused_at.expect("the worker polls after the conversion");
    assert!(refused_at > 1, "entry admission polls before conversion");
    assert_eq!(calls, refused_at, "a refused attempt is never polled again");
    assert_eq!(conversions.get(), 1);
}

#[test]
fn pre_refusal_precedes_unknown_missing_and_malformed_candidates() {
    let (problem, mut derivation) = truth_parts();
    derivation.query_step = usize::MAX;
    // The malformed/absent synthetic markers exercise entry refusal only;
    // neither is used to acquire positive checked authority.
    for result in [
        VerifiedChcResult::from_validated(
            ChcEngineResult::Unknown,
            ValidationEvidence::FullVerification,
        ),
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(Counterexample::new(
            vec![],
        ))),
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(
            Counterexample::new(vec![]).with_ground_derivation(derivation),
        )),
    ] {
        let run = ChcPdrProofRun::new(problem.clone(), result, "entry-test");
        let original = run.metadata().to_json_value();
        let mut calls = 0;
        assert_interrupted(run.run_checked_replay_with_progress(BUDGET, &mut || {
            calls += 1;
            calls != 1
        }));
        assert_eq!(calls, 1);
        let mut calls = 0;
        assert_interrupted(run.run_checked_replay_with_binding_and_progress(
            ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default()),
            ChcProofSolverIdentity::new("entry-test"),
            "entry-test",
            None,
            BUDGET,
            &mut || {
                calls += 1;
                calls != 1
            },
        ));
        assert_eq!(calls, 1);
        assert_eq!(run.metadata().to_json_value(), original);
    }
}

#[test]
fn zero_budget_preserves_legacy_error_without_entry_work() {
    let run = truth_run();
    let expected = run
        .run_checked_replay(Duration::ZERO)
        .unwrap_err()
        .to_string();
    assert_eq!(
        expected,
        "verification error: checked replay budget is zero; staying metadata-only"
    );
    let error = run
        .run_checked_replay_with_progress(Duration::ZERO, &mut || {
            panic!("zero budget is immediate")
        })
        .unwrap_err();
    assert_eq!(error.to_string(), expected);
    let conversions = Cell::new(0);
    let error = run
        .run_checked_replay_with_binding_and_progress(
            ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default()),
            ChcProofSolverIdentity::new("test"),
            ObservedId {
                conversions: &conversions,
            },
            None,
            Duration::ZERO,
            &mut || panic!("zero budget is immediate"),
        )
        .unwrap_err();
    assert_eq!(error.to_string(), expected);
    assert_eq!(conversions.get(), 0);
}

#[test]
fn caller_binding_mismatch_is_still_rejected_when_progress_continues() {
    let run = truth_run();
    for format in [Format::GroundDerivationV1, Format::GroundDerivationV2] {
        let mut binding = binding(&run, format);
        binding.base_evidence.as_mut().unwrap().replay_obligations[0]
            .query
            .sha256 = "0".repeat(64);
        let error = run
            .run_checked_replay_with_binding_and_progress(
                binding.options,
                binding.solver,
                binding.obligation_id,
                binding.base_evidence,
                BUDGET,
                &mut || true,
            )
            .unwrap_err();
        assert!(error
            .to_string()
            .contains("do not match the supplied replay evidence"));
    }
}

#[test]
fn worker_retains_original_absolute_start_instead_of_granting_a_new_budget() {
    let run = truth_run();
    let binding = binding(&run, Format::GroundDerivationV1);
    let start = Instant::now().checked_sub(Duration::from_secs(5)).unwrap();
    let budget = Duration::from_secs(1);
    let mut callback = || ground_export::within_budget(&start, budget);
    let mut progress = ground_export::ReplayProgress::new(&mut callback);
    assert_interrupted(run.run_checked_replay_with_control(
        binding,
        ReplayLimit::Until(replay_deadline(start, budget).unwrap()),
        &mut progress,
    ));
}
