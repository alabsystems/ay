// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

#[test]
fn backward_failure_mapping_never_confuses_deadline_or_memory_with_cancellation() {
    assert_eq!(
        map_backward_proof_failure(BackwardProofFailure::Cancelled),
        ResolutionProofError::Cancelled
    );
    assert_eq!(
        map_backward_proof_failure(BackwardProofFailure::Deadline),
        ResolutionProofError::DeadlineExceeded {
            phase: ResolutionProofPhase::Solve
        }
    );
    assert_eq!(
        map_backward_proof_failure(BackwardProofFailure::Limit {
            resource: BackwardProofResource::Bytes,
            limit: 10,
            actual: 11,
        }),
        ResolutionProofError::LimitExceeded {
            resource: ResolutionProofResource::BackwardReconstructionBytes,
            limit: 10,
            actual: 11,
        }
    );
}

#[test]
fn only_the_typed_writer_marker_maps_to_cancellation() {
    let output = ProofOutput::lrat_binary(Vec::new(), 0);
    let error = output
        .into_inner_with_cancellation(&|| false)
        .expect_err("caller refusal");
    let text = error.to_string();
    assert_ne!(error.kind(), io::ErrorKind::Interrupted);
    assert_eq!(
        map_proof_writer_error(error),
        ResolutionProofError::Cancelled
    );
    for kind in [
        io::ErrorKind::Other,
        io::ErrorKind::Interrupted,
        io::ErrorKind::TimedOut,
        io::ErrorKind::BrokenPipe,
    ] {
        assert_eq!(
            map_proof_writer_error(io::Error::new(kind, text.clone())),
            ResolutionProofError::ProofWriterUnavailable
        );
    }
}

#[test]
fn input_time_terminal_proofs_keep_zero_backward_memory_and_every_poll_is_terminal() {
    for clauses in [
        vec![vec![], vec![positive(0)]],
        vec![vec![positive(0)], vec![negative(0)]],
    ] {
        let make_limits = || ResolutionProofLimits {
            max_backward_reconstruction_bytes: 0,
            ..limits()
        };
        let mut total = 0;
        let expected = prove_unsat_resolution_dag_with_limits_and_cancellation(
            1,
            &clauses,
            &make_limits(),
            &mut || {
                total += 1;
                true
            },
        )
        .unwrap();
        assert_eq!(expected.validate(), Ok(()));
        assert!(
            total > 10 && total < 2_000,
            "small terminal fixture: {total}"
        );
        for stop in 1..=total {
            let mut calls = 0;
            let result = prove_unsat_resolution_dag_with_limits_and_cancellation(
                1,
                &clauses,
                &make_limits(),
                &mut || {
                    calls += 1;
                    calls != stop
                },
            );
            assert_eq!(
                result,
                Err(ResolutionProofError::Cancelled),
                "poll {stop}/{total}"
            );
            assert_eq!(calls, stop);
        }
        assert_eq!(
            prove_unsat_resolution_dag_with_limits_and_cancellation(
                1,
                &clauses,
                &make_limits(),
                &mut || true,
            ),
            Ok(expected)
        );
    }
}
