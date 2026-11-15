// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::super::tests::{fixture, uf_fixture};
use super::*;
use crate::engine_result::ValidationEvidence;
use crate::{ChcEngineResult, VerifiedCounterexample};

mod fixtures;
mod oracle;

#[derive(Clone, Copy, Debug)]
enum Format {
    V1,
    V2,
}

impl Format {
    fn export(
        self,
        cex: &Counterexample,
        problem: &ChcProblem,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
        match self {
            Self::V1 => cex.ground_derivation_artifact_with_progress(problem, progress),
            Self::V2 => cex.ground_derivation_artifact_v2_with_progress(problem, progress),
        }
    }

    fn run_export(
        self,
        run: &ChcPdrProofRun,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<Option<Vec<u8>>, ChcGroundDerivationArtifactError> {
        match self {
            Self::V1 => run.unsafe_ground_derivation_artifact_bytes_with_progress(progress),
            Self::V2 => run.unsafe_ground_derivation_artifact_v2_bytes_with_progress(progress),
        }
    }

    fn legacy(
        self,
        problem: &ChcProblem,
        derivation: &GroundDerivation,
    ) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
        match self {
            Self::V1 => oracle::encode_v1(problem, derivation),
            Self::V2 => oracle::encode_v2(problem, derivation),
        }
    }
}

fn cex(derivation: GroundDerivation) -> Counterexample {
    Counterexample::new(Vec::new()).with_ground_derivation(derivation)
}

fn assert_same_error(
    actual: ChcGroundDerivationArtifactError,
    expected: ChcGroundDerivationArtifactError,
) {
    assert_eq!(actual.reason, expected.reason);
    assert_eq!(actual.reason_code, expected.reason_code);
    assert_eq!(actual.detail, expected.detail);
}

fn every_refusal(format: Format, problem: &ChcProblem, derivation: GroundDerivation) {
    let counterexample = cex(derivation);
    let mut total = 0;
    let expected = format
        .export(&counterexample, problem, &mut || {
            total += 1;
            true
        })
        .unwrap();
    assert!(total > 10, "exercise several producer and consumer phases");
    for stop in 1..=total {
        let mut calls = 0;
        let result = format.export(&counterexample, problem, &mut || {
            calls += 1;
            calls != stop
        });
        assert_eq!(
            result.unwrap_err().reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted,
            "{format:?} refusal {stop}/{total}"
        );
        assert_eq!(calls, stop, "no callback retry after refusal");
    }
    assert_eq!(
        format
            .export(&counterexample, problem, &mut || true)
            .unwrap(),
        expected
    );
}

#[test]
fn always_continue_producers_match_legacy_bytes_digests_and_metadata() {
    let (problem, derivation) = fixture();
    let counterexample = cex(derivation.clone());
    for format in [Format::V1, Format::V2] {
        let expected = format.legacy(&problem, &derivation).unwrap();
        assert_eq!(
            format
                .export(&counterexample, &problem, &mut || true)
                .unwrap(),
            expected
        );
        let default = match format {
            Format::V1 => counterexample.ground_derivation_artifact(&problem),
            Format::V2 => counterexample.ground_derivation_artifact_v2(&problem),
        }
        .unwrap();
        assert_eq!(default, expected);
    }
    let (problem, derivation) = uf_fixture();
    let expected = oracle::encode_v2(&problem, &derivation).unwrap();
    assert_eq!(
        cex(derivation)
            .ground_derivation_artifact_v2_with_progress(&problem, &mut || true)
            .unwrap(),
        expected
    );
}

#[test]
fn wide_recursive_values_retain_exact_legacy_bytes() {
    let (problem, derivation) = fixtures::wide_recursive();
    let counterexample = cex(derivation.clone());
    for format in [Format::V1, Format::V2] {
        assert_eq!(
            format
                .export(&counterexample, &problem, &mut || true)
                .unwrap(),
            format.legacy(&problem, &derivation).unwrap()
        );
    }
}

#[test]
fn v1_producer_refuses_every_callback_including_final_seal() {
    let (problem, derivation) = fixtures::truth();
    every_refusal(Format::V1, &problem, derivation);
}

#[test]
fn v2_producer_refuses_every_callback_including_uf_replay() {
    let (problem, derivation) = uf_fixture();
    every_refusal(Format::V2, &problem, derivation);
}

#[test]
fn malformed_candidates_keep_legacy_error_priority_and_detail() {
    let (problem, derivation) = fixture();
    let mut cases = Vec::new();
    let mut invalid = derivation.clone();
    invalid.steps.clear();
    cases.push(invalid);
    let mut invalid = derivation.clone();
    invalid.query_step = usize::MAX;
    cases.push(invalid);
    let mut invalid = derivation.clone();
    invalid.steps[0].clause_index = usize::MAX;
    cases.push(invalid);
    let mut invalid = derivation.clone();
    invalid.steps[1].premises = vec![1];
    cases.push(invalid);
    let mut invalid = derivation.clone();
    invalid.steps[0].env.clear();
    cases.push(invalid);
    for value in [
        SmtValue::Opaque("not-ground".to_string()),
        SmtValue::Bool(true),
    ] {
        let mut invalid = derivation.clone();
        invalid.steps[0].env.insert("x".to_string(), value);
        cases.push(invalid);
    }
    let mut invalid = derivation;
    invalid.steps[0]
        .env
        .insert("extra".to_string(), SmtValue::Int(0));
    cases.push(invalid);
    for invalid in cases {
        let counterexample = cex(invalid.clone());
        for format in [Format::V1, Format::V2] {
            assert_same_error(
                format
                    .export(&counterexample, &problem, &mut || true)
                    .unwrap_err(),
                format.legacy(&problem, &invalid).unwrap_err(),
            );
        }
    }
}

#[test]
fn v1_wire_errors_precede_native_errors_but_v2_checks_native_first() {
    let (problem, mut derivation) = fixture();
    derivation.steps[0]
        .env
        .insert("x".to_string(), SmtValue::Opaque("opaque".to_string()));
    derivation.steps[1].premises = vec![1];
    let counterexample = cex(derivation);
    assert_eq!(
        Format::V1
            .export(&counterexample, &problem, &mut || true)
            .unwrap_err()
            .reason,
        ChcGroundDerivationArtifactErrorReason::OpaqueValue
    );
    assert_eq!(
        Format::V2
            .export(&counterexample, &problem, &mut || true)
            .unwrap_err()
            .reason,
        ChcGroundDerivationArtifactErrorReason::DerivationRejected
    );
}

#[test]
fn pre_cancel_precedes_missing_evidence_and_malformed_source() {
    let missing = Counterexample::new(Vec::new());
    let (problem, derivation) = fixtures::truth();
    let present = cex(derivation);
    for format in [Format::V1, Format::V2] {
        for candidate in [&missing, &present] {
            let mut calls = 0;
            let error = format
                .export(candidate, &ChcProblem::new(), &mut || {
                    calls += 1;
                    false
                })
                .unwrap_err();
            assert_eq!(
                error.reason,
                ChcGroundDerivationArtifactErrorReason::Interrupted
            );
            assert_eq!(calls, 1);
        }
        assert_eq!(
            format
                .export(&missing, &problem, &mut || true)
                .unwrap_err()
                .reason,
            ChcGroundDerivationArtifactErrorReason::MissingGroundDerivation
        );
    }
}

#[test]
fn shared_control_cannot_resume_a_second_export_after_refusal() {
    let (problem, derivation) = fixtures::truth();
    let mut calls = 0;
    let mut progress = || {
        calls += 1;
        calls != 2
    };
    let mut control = GroundValidationControl::new(&mut progress);
    assert_eq!(
        encode_v1_with_control(&problem, &derivation, &mut control)
            .unwrap_err()
            .reason,
        ChcGroundDerivationArtifactErrorReason::Interrupted
    );
    assert_eq!(
        encode_v2_with_control(&problem, &derivation, &mut control)
            .unwrap_err()
            .reason,
        ChcGroundDerivationArtifactErrorReason::Interrupted
    );
    assert_eq!(calls, 2);
}

#[test]
fn run_exports_preserve_valid_bytes_and_are_cancellable_at_completion() {
    let (problem, derivation) = fixtures::truth();
    validate_ground_derivation(&problem, &derivation).unwrap();
    let run = ChcPdrProofRun::new(
        problem,
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(cex(derivation))),
        "producer-test",
    );
    for format in [Format::V1, Format::V2] {
        let mut calls = 0;
        let bytes = format
            .run_export(&run, &mut || {
                calls += 1;
                true
            })
            .unwrap()
            .unwrap();
        let default = match format {
            Format::V1 => run.unsafe_ground_derivation_artifact_bytes(),
            Format::V2 => run.unsafe_ground_derivation_artifact_v2_bytes(),
        }
        .unwrap()
        .unwrap();
        assert_eq!(bytes, default);
        let mut seen = 0;
        assert_eq!(
            format
                .run_export(&run, &mut || {
                    seen += 1;
                    seen != calls
                })
                .unwrap_err()
                .reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted
        );
        assert_eq!(seen, calls);
        assert_eq!(format.run_export(&run, &mut || true).unwrap(), Some(bytes));
    }
}

#[test]
fn absence_and_nonunsafe_run_paths_poll_entry_and_completion() {
    let (problem, _) = fixtures::truth();
    let unknown = ChcPdrProofRun::new(
        problem.clone(),
        VerifiedChcResult::from_validated(
            ChcEngineResult::Unknown,
            ValidationEvidence::FullVerification,
        ),
        "producer-test",
    );
    // This synthetic legacy Unsafe marker tests only the documented absence
    // path; it carries no ground artifact and cannot mint a checked capability.
    let absent = ChcPdrProofRun::new(
        problem,
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(Counterexample::new(
            Vec::new(),
        ))),
        "producer-test",
    );
    for run in [&unknown, &absent] {
        for format in [Format::V1, Format::V2] {
            let mut total = 0;
            assert!(format
                .run_export(run, &mut || {
                    total += 1;
                    true
                })
                .unwrap()
                .is_none());
            assert!(total >= 2);
            for stop in 1..=total {
                let mut calls = 0;
                assert_eq!(
                    format
                        .run_export(run, &mut || {
                            calls += 1;
                            calls != stop
                        })
                        .unwrap_err()
                        .reason,
                    ChcGroundDerivationArtifactErrorReason::Interrupted
                );
                assert_eq!(calls, stop);
            }
            let legacy = match format {
                Format::V1 => run.unsafe_ground_derivation_artifact_bytes(),
                Format::V2 => run.unsafe_ground_derivation_artifact_v2_bytes(),
            };
            assert!(legacy.unwrap().is_none());
        }
    }
}
