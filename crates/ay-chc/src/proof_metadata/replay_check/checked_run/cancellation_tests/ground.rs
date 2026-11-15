// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn ground_case(
    checked: &ChcCheckedReplayRun,
    format: ChcReplayPayloadFormat,
) -> (ChcCheckedReplayObligation, Vec<u8>) {
    let item = checked.obligation_payloads().next().unwrap();
    let mut obligation = item.obligation().clone();
    let bytes = match format {
        ChcReplayPayloadFormat::GroundDerivationV1 => item.payload_bytes().to_vec(),
        ChcReplayPayloadFormat::GroundDerivationV2 => checked
            .proof_run()
            .unsafe_ground_derivation_artifact_v2_bytes()
            .unwrap()
            .unwrap(),
        _ => panic!("only actual versioned ground artifacts are fixtures"),
    };
    obligation.payload_format = format;
    (obligation, bytes)
}

#[test]
fn both_ground_readers_poll_each_inner_boundary_and_refuse_without_retry() {
    let checked = checked_ground_fixture();
    for format in [
        ChcReplayPayloadFormat::GroundDerivationV1,
        ChcReplayPayloadFormat::GroundDerivationV2,
    ] {
        let (obligation, bytes) = ground_case(&checked, format);
        let token = CancellationToken::new();
        let cancellation = ReplayCancellation::new(&token);
        let control = live_control(&cancellation);
        let start = Instant::now();
        let mut samples = 0;
        let validated = recheck_ground_with_control(
            checked.proof_run().problem(),
            &obligation,
            &bytes,
            control,
            &mut || {
                samples += 1;
                start
            },
        )
        .unwrap();
        assert_eq!(validated.query_step(), 0);
        drop(validated);
        assert!(
            samples > 10,
            "must reach the real source, decode and native reader phases"
        );
        for stop_at in 1..=samples {
            let parent = CancellationToken::new();
            let token = parent.child().child();
            let cancellation = ReplayCancellation::new(&token);
            let mut ordinal = 0;
            assert_interrupted(recheck_ground_with_control(
                checked.proof_run().problem(),
                &obligation,
                &bytes,
                live_control(&cancellation),
                &mut || {
                    ordinal += 1;
                    if ordinal == stop_at {
                        parent.cancel();
                    }
                    start
                },
            ));
            assert_eq!(
                ordinal, stop_at,
                "the chosen format must not retry a refused poll"
            );
            parent.reset();
            assert!(cancellation.is_cancelled());
        }
    }
}

#[test]
fn ground_source_binding_and_bytes_are_not_relaxed_by_a_live_token() {
    let checked = checked_ground_fixture();
    for format in [
        ChcReplayPayloadFormat::GroundDerivationV1,
        ChcReplayPayloadFormat::GroundDerivationV2,
    ] {
        let (obligation, bytes) = ground_case(&checked, format);
        let token = CancellationToken::new();
        let cancellation = ReplayCancellation::new(&token);
        for problem in [checked.proof_run().problem(), &crate::ChcProblem::new()] {
            let legacy = recheck_ground_with_progress(problem, &obligation, &bytes, &mut || true);
            let controlled = recheck_ground_with_control(
                problem,
                &obligation,
                &bytes,
                live_control(&cancellation),
                &mut Instant::now,
            );
            match (legacy, controlled) {
                (Ok(expected), Ok(actual)) => {
                    assert_eq!(actual.artifact_sha256(), expected.artifact_sha256())
                }
                (Err(expected), Err(actual)) => {
                    assert_eq!(actual.to_string(), expected.to_string())
                }
                _ => panic!("live cancellation must not change source admission"),
            }
        }
        assert!(recheck_ground_with_control(
            &crate::ChcProblem::new(),
            &obligation,
            &bytes,
            live_control(&cancellation),
            &mut Instant::now
        )
        .is_err());
        let mut tampered = bytes.clone();
        tampered[0] = b'[';
        assert!(recheck_ground_with_control(
            checked.proof_run().problem(),
            &obligation,
            &tampered,
            live_control(&cancellation),
            &mut Instant::now
        )
        .is_err());
    }
}

#[test]
fn ground_precancel_and_spent_original_wall_precede_malformed_input() {
    for format in [
        ChcReplayPayloadFormat::GroundDerivationV1,
        ChcReplayPayloadFormat::GroundDerivationV2,
    ] {
        let checked = checked_ground_fixture();
        let (obligation, _) = ground_case(&checked, format);
        let token = CancellationToken::new();
        token.cancel();
        let cancellation = ReplayCancellation::new(&token);
        assert_interrupted(recheck_ground_with_control(
            checked.proof_run().problem(),
            &obligation,
            b"{",
            live_control(&cancellation),
            &mut || panic!("pre-cancellation precedes the clock"),
        ));
        token.reset();
        let fresh = ReplayCancellation::new(&token);
        let start = Instant::now().checked_sub(Duration::from_secs(5)).unwrap();
        let control = FreshRecheckControl {
            deadline: fresh_recheck_deadline(start, Duration::from_secs(1)).unwrap(),
            cancellation: Some(&fresh),
        };
        let mut samples = 0;
        assert_interrupted(recheck_ground_with_control(
            checked.proof_run().problem(),
            &obligation,
            b"{",
            control,
            &mut || {
                samples += 1;
                Instant::now()
            },
        ));
        assert_eq!(samples, 1);
        assert!(!token.is_cancelled());
    }
}
