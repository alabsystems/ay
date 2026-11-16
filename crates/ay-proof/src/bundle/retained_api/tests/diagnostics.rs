// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

type ReadResult = Result<(RetainedProofBundle, BundleReCheck), ProofCheckError>;
type ReadTrace = (ReadResult, Vec<(usize, usize)>, RetainedReadDiagnostics);

#[derive(Clone, Copy)]
enum Lane {
    Legacy,
    Observed,
}

#[derive(Clone, Copy)]
enum Admission {
    Healthy,
    RefuseAt(usize),
}

fn bool_bytes() -> Vec<u8> {
    let (bundle, _) = capture_strict_retained_bundle_with_resource_control(
        repeated_bool_snapshot(),
        end(),
        &mut |_, _| true,
    )
    .unwrap()
    .finish_exact_with_resource_control(&mut |_, _| true)
    .unwrap();
    bundle
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap()
}

fn read(
    lane: Lane,
    bytes: &[u8],
    limits: RetainedProofTransportLimits,
    deadline: Instant,
    admission: Admission,
) -> ReadTrace {
    let mut trace = Vec::new();
    let mut diagnostic = RetainedReadDiagnostics::default();
    let mut progress = |work, bytes| {
        trace.push((work, bytes));
        match admission {
            Admission::Healthy => true,
            Admission::RefuseAt(stop) => trace.len() != stop,
        }
    };
    let result = match lane {
        Lane::Legacy => {
            read_retained_proof_bundle_with_resource_control(bytes, limits, deadline, &mut progress)
        }
        Lane::Observed => read_retained_proof_bundle_with_resource_control_and_diagnostics(
            bytes,
            limits,
            deadline,
            &mut progress,
            &mut diagnostic,
        ),
    };
    (result, trace, diagnostic)
}

fn paired(
    bytes: &[u8],
    limits: RetainedProofTransportLimits,
    deadline: Instant,
    admission: Admission,
) -> ReadTrace {
    // Independent test invocations compare exact outcome and callback/debit traces.
    // Production receives diagnostics in ONE read, not a newly granted second run.
    let legacy = read(Lane::Legacy, bytes, limits, deadline, admission);
    let observed = read(Lane::Observed, bytes, limits, deadline, admission);
    assert_eq!(format!("{:?}", legacy.0), format!("{:?}", observed.0));
    assert_eq!(legacy.1, observed.1);
    observed
}

#[test]
fn healthy_reader_keeps_exact_old_result_and_callback_trace() {
    let bytes = bool_bytes();
    let before = producer_test_counter::count();
    let (result, trace, diagnostic) = paired(&bytes, transport_limits(), end(), Admission::Healthy);
    assert!(result.unwrap().1.quality.is_complete());
    assert_ne!(trace, []);
    assert_eq!(diagnostic.first_failure(), None);
    assert_eq!(diagnostic.terminal(), Some(RetainedReadTerminal::Healthy));
    assert_eq!(diagnostic.reported_error(), None);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn outer_json_limit_preserves_actual_numbers_before_public_flattening() {
    let bytes = bool_bytes();
    let mut limits = transport_limits();
    limits.max_json_bytes = bytes.len() - 1;
    let (result, _, diagnostic) = paired(&bytes, limits, end(), Admission::Healthy);
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(
        diagnostic.first_failure(),
        Some(RetainedReadFailure {
            stage: RetainedReadStage::Decode,
            refusal: RetainedReadRefusal::TransportLimit {
                resource: "outer JSON bytes",
                actual: bytes.len(),
                limit: bytes.len() - 1,
            },
        })
    );
    assert_eq!(diagnostic.terminal(), Some(RetainedReadTerminal::Healthy));
    assert_eq!(
        diagnostic.reported_error(),
        Some(RetainedReadErrorClass::ResourceLimit)
    );
}

#[test]
fn work_and_storage_limits_keep_the_existing_decoder_numbers_and_trace() {
    let bytes = bool_bytes();
    for resource in ["transport work", "new transport bytes"] {
        let mut limits = transport_limits();
        if resource == "transport work" {
            limits.max_work = 0;
        } else {
            limits.max_storage_bytes = 0;
        }
        let (result, _, diagnostic) = paired(&bytes, limits, end(), Admission::Healthy);
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        let RetainedReadFailure { stage, refusal } = diagnostic.first_failure().unwrap();
        assert_eq!(stage, RetainedReadStage::Decode);
        let RetainedReadRefusal::TransportLimit {
            resource: actual_resource,
            actual,
            limit,
        } = refusal
        else {
            panic!("the actual decoder limit must remain available");
        };
        assert_eq!(actual_resource, resource);
        assert!(actual > 0);
        assert_eq!(limit, 0);
        assert_eq!(diagnostic.terminal(), Some(RetainedReadTerminal::Healthy));
    }
}

#[test]
fn entry_callback_and_original_deadline_refusal_do_not_invent_a_decoder_cause() {
    let bytes = bool_bytes();
    let (result, trace, diagnostic) =
        paired(&bytes, transport_limits(), end(), Admission::RefuseAt(1));
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(trace, [(0, 0)]);
    assert_eq!(
        diagnostic.first_failure(),
        Some(RetainedReadFailure {
            stage: RetainedReadStage::Entry,
            refusal: RetainedReadRefusal::ProofResourceLimit,
        })
    );
    assert_eq!(diagnostic.terminal(), None);
    let (result, trace, diagnostic) = paired(
        &bytes,
        transport_limits(),
        Instant::now(),
        Admission::Healthy,
    );
    assert!(matches!(result, Err(ProofCheckError::Cancelled)));
    assert_eq!(trace, []);
    assert_eq!(
        diagnostic.first_failure(),
        Some(RetainedReadFailure {
            stage: RetainedReadStage::Entry,
            refusal: RetainedReadRefusal::ProofCancelled,
        })
    );
    assert_eq!(diagnostic.terminal(), None);
}

#[test]
fn strict_replay_refusal_is_distinct_from_decode_and_new_late_control() {
    let bytes = finished()
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap();
    let healthy = read(
        Lane::Observed,
        &bytes,
        transport_limits(),
        end(),
        Admission::Healthy,
    );
    assert!(healthy.0.is_ok());
    // Refuse an actual positive strict-replay debit, not the historical
    // producer's worst-case fee. Final public control polls have zero work.
    let stop = healthy.1.iter().rposition(|&(work, _)| work > 0).unwrap() + 1;
    let before = producer_test_counter::count();
    let (result, trace, diagnostic) =
        paired(&bytes, transport_limits(), end(), Admission::RefuseAt(stop));
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(trace.len(), stop);
    assert!(trace.last().unwrap().0 > 0);
    assert_eq!(
        diagnostic.first_failure(),
        Some(RetainedReadFailure {
            stage: RetainedReadStage::StrictReplay,
            refusal: RetainedReadRefusal::ProofResourceLimit,
        })
    );
    assert_eq!(
        diagnostic.terminal(),
        Some(RetainedReadTerminal::AlreadyRefused(
            RetainedReadErrorClass::ResourceLimit,
        ))
    );
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn actual_final_control_refusal_publishes_neither_bundle_nor_healthy_terminal() {
    let bytes = bool_bytes();
    let deadline = end();
    let healthy = read(
        Lane::Legacy,
        &bytes,
        transport_limits(),
        deadline,
        Admission::Healthy,
    );
    assert!(healthy.0.is_ok());
    let final_poll = healthy.1.len();
    let (result, trace, diagnostic) = paired(
        &bytes,
        transport_limits(),
        deadline,
        Admission::RefuseAt(final_poll),
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(trace.len(), final_poll);
    assert_eq!(
        diagnostic.first_failure(),
        Some(RetainedReadFailure {
            stage: RetainedReadStage::FinalControl,
            refusal: RetainedReadRefusal::ProofResourceLimit,
        })
    );
    assert_eq!(
        diagnostic.terminal(),
        Some(RetainedReadTerminal::NewlyRefused(
            RetainedReadErrorClass::ResourceLimit,
        ))
    );
}

#[test]
fn decoder_first_limit_survives_its_existing_later_refusal_precedence() {
    let bytes = bool_bytes();
    let deadline = end();
    let mut limits = transport_limits();
    limits.max_json_bytes = bytes.len() - 1;
    let healthy = read(Lane::Legacy, &bytes, limits, deadline, Admission::Healthy);
    assert!(matches!(healthy.0, Err(ProofCheckError::ResourceLimit)));
    // The last two existing callback observations are decoder cleanup then
    // outer original-control final admission. Refuse the decoder's cleanup.
    assert!(healthy.1.len() >= 2);
    let stop = healthy.1.len() - 1;
    assert_eq!(healthy.1[stop - 1], (0, 0));
    let (result, trace, diagnostic) = paired(&bytes, limits, deadline, Admission::RefuseAt(stop));
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(trace.len(), stop);
    assert_eq!(
        diagnostic.first_failure(),
        Some(RetainedReadFailure {
            stage: RetainedReadStage::Decode,
            refusal: RetainedReadRefusal::TransportLimit {
                resource: "outer JSON bytes",
                actual: bytes.len(),
                limit: bytes.len() - 1,
            },
        })
    );
    assert_eq!(
        diagnostic.terminal(),
        Some(RetainedReadTerminal::AlreadyRefused(
            RetainedReadErrorClass::ResourceLimit,
        ))
    );
}

#[test]
fn malformed_first_cause_survives_a_new_terminal_refusal_with_exact_old_error() {
    let deadline = end();
    let healthy = read(
        Lane::Legacy,
        b"{}",
        transport_limits(),
        deadline,
        Admission::Healthy,
    );
    assert!(healthy.0.is_err());
    let final_poll = healthy.1.len();
    let (result, trace, diagnostic) = paired(
        b"{}",
        transport_limits(),
        deadline,
        Admission::RefuseAt(final_poll),
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(trace.len(), final_poll);
    assert_eq!(
        diagnostic.first_failure(),
        Some(RetainedReadFailure {
            stage: RetainedReadStage::Decode,
            refusal: RetainedReadRefusal::TransportInvalid,
        })
    );
    assert_eq!(
        diagnostic.terminal(),
        Some(RetainedReadTerminal::NewlyRefused(
            RetainedReadErrorClass::ResourceLimit,
        ))
    );
    assert_eq!(
        diagnostic.reported_error(),
        Some(RetainedReadErrorClass::ResourceLimit)
    );
}

#[test]
fn selected_inner_refusals_keep_sticky_trace_and_reset_only_observation_header() {
    let bytes = bool_bytes();
    let deadline = end();
    let healthy = read(
        Lane::Legacy,
        &bytes,
        transport_limits(),
        deadline,
        Admission::Healthy,
    );
    assert!(healthy.0.is_ok());
    let calls = healthy.1.len();
    for stop in [2, calls / 2, calls] {
        let (result, trace, diagnostic) = paired(
            &bytes,
            transport_limits(),
            deadline,
            Admission::RefuseAt(stop),
        );
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(trace.len(), stop); // No callback after the original local latch.
        assert_eq!(
            diagnostic.reported_error(),
            Some(RetainedReadErrorClass::ResourceLimit)
        );
    }
    // Reusing observational data cannot reuse or renew an original control.
    let mut diagnostic = RetainedReadDiagnostics {
        first: None,
        terminal: Some(RetainedReadTerminal::Healthy),
        reported: None,
    };
    let result = read_retained_proof_bundle_with_resource_control_and_diagnostics(
        &bytes,
        transport_limits(),
        Instant::now(),
        &mut |_, _| true,
        &mut diagnostic,
    );
    assert!(matches!(result, Err(ProofCheckError::Cancelled)));
    assert_eq!(diagnostic.terminal(), None);
    assert_eq!(
        diagnostic.reported_error(),
        Some(RetainedReadErrorClass::Cancelled)
    );
}
