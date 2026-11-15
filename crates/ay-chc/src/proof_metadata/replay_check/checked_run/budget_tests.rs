// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Row-budget admission must precede retained payload validation.

#![cfg(test)]

use super::*;
use crate::ChcReplayCheckResult;

pub(super) mod deadline_tests;

// Keep the legacy clock probes exercising the production control helpers
// without changing their sample order or deadline-only error precedence.
fn deadline_control(deadline: Instant) -> FreshRecheckControl<'static> {
    FreshRecheckControl {
        deadline,
        cancellation: None,
    }
}

fn validate_payload_with_deadline(
    payload: &SealedReplayObligationPayload,
    obligation: &ChcCheckedReplayObligation,
    deadline: Instant,
    now: &mut dyn FnMut() -> Instant,
) -> ChcResult<()> {
    validate_payload_with_control(payload, obligation, deadline_control(deadline), now)
}

fn recheck_smt_payload(
    query_bytes: &[u8],
    obligation: &ChcCheckedReplayObligation,
    deadline: Instant,
) -> ChcResult<()> {
    recheck_smt_payload_with_control(query_bytes, obligation, deadline_control(deadline))
}

fn invalid_payload(
    format: ChcReplayPayloadFormat,
) -> (ChcCheckedReplayObligation, SealedReplayObligationPayload) {
    let bytes = b"retained payload".to_vec();
    let mut obligation = ChcCheckedReplayObligation::new(
        "budget-ordering",
        ChcReplayObligationKind::TraceValidity,
        ChcProofArtifactDigest::from_bytes("replay-obligation", &bytes),
        "test-only",
        ChcReplayCheckResult::pass(),
    );
    obligation.payload_format = format;
    // Deliberately bypass the sealing constructors: this mismatched identity
    // must be rejected when admitted, but not inspected after budget expiry.
    let payload = match format {
        ChcReplayPayloadFormat::SmtlibV1 => SealedReplayObligationPayload::Smt {
            obligation_identity_sha256: String::new(),
            query_bytes: bytes,
            strict_bundle_bytes: None,
            alethe_bytes: None,
            source_authority: SmtSourceAuthority::Legacy,
        },
        ChcReplayPayloadFormat::GroundDerivationV1
        | ChcReplayPayloadFormat::GroundDerivationV2
        | ChcReplayPayloadFormat::CompactGroundDerivationV1 => {
            SealedReplayObligationPayload::GroundDerivation {
                obligation_identity_sha256: String::new(),
                artifact_bytes: bytes,
            }
        }
    };
    (obligation, payload)
}

#[test]
fn expired_row_budget_precedes_invalid_payload_rejection() {
    let start = Instant::now()
        .checked_sub(Duration::from_secs(5))
        .expect("test clock must represent a past start");
    for format in [
        ChcReplayPayloadFormat::SmtlibV1,
        ChcReplayPayloadFormat::GroundDerivationV1,
        ChcReplayPayloadFormat::GroundDerivationV2,
    ] {
        let (obligation, payload) = invalid_payload(format);
        let error = validate_payload_with_deadline(
            &payload,
            &obligation,
            fresh_recheck_deadline(start, Duration::from_secs(1)).unwrap(),
            &mut Instant::now,
        )
        .expect_err("expired work must be refused before payload validation");
        assert!(
            error
                .to_string()
                .contains("budget exhausted before obligation budget-ordering"),
            "unexpected {format:?} rejection: {error}"
        );
    }
}

#[test]
fn live_row_budget_retains_invalid_payload_rejection() {
    for format in [
        ChcReplayPayloadFormat::SmtlibV1,
        ChcReplayPayloadFormat::GroundDerivationV1,
        ChcReplayPayloadFormat::GroundDerivationV2,
    ] {
        let (obligation, payload) = invalid_payload(format);
        let error = validate_payload_with_deadline(
            &payload,
            &obligation,
            fresh_recheck_deadline(Instant::now(), Duration::from_mins(1)).unwrap(),
            &mut Instant::now,
        )
        .expect_err("a live budget must not bypass payload validation");
        assert!(
            error
                .to_string()
                .contains("retained payload is not aligned with obligation budget-ordering"),
            "unexpected {format:?} rejection: {error}"
        );
    }
}

#[test]
fn ground_format_dispatch_preserves_interruption_without_fallback() {
    let problem = crate::ChcProblem::new();
    for format in [
        ChcReplayPayloadFormat::GroundDerivationV1,
        ChcReplayPayloadFormat::GroundDerivationV2,
    ] {
        let (obligation, _) = invalid_payload(format);
        let mut calls = 0;
        let error = recheck_ground_with_progress(&problem, &obligation, b"{", &mut || {
            calls += 1;
            calls != 1
        })
        .expect_err("pre-refusal must dominate malformed artifact bytes");
        assert!(
            error.to_string().contains("interrupted"),
            "{format:?}: {error}"
        );
        assert!(error.to_string().contains("obligation budget-ordering"));
        assert_eq!(calls, 1, "neither another format nor a retry may run");
    }
}

#[test]
fn ground_recheck_uses_the_original_start_instead_of_resetting_a_row_duration() {
    let start = Instant::now()
        .checked_sub(Duration::from_secs(5))
        .expect("test clock must represent a past start");
    let problem = crate::ChcProblem::new();
    for format in [
        ChcReplayPayloadFormat::GroundDerivationV1,
        ChcReplayPayloadFormat::GroundDerivationV2,
    ] {
        let (obligation, _) = invalid_payload(format);
        let error =
            recheck_ground_with_budget(&problem, &obligation, b"{", Duration::from_secs(1), &start)
                .expect_err("spent time before this row must remain spent");
        assert!(
            error.to_string().contains("interrupted"),
            "{format:?}: {error}"
        );
    }
}

#[test]
fn live_ground_recheck_preserves_the_original_malformed_reason() {
    let problem = crate::ChcProblem::new();
    for format in [
        ChcReplayPayloadFormat::GroundDerivationV1,
        ChcReplayPayloadFormat::GroundDerivationV2,
    ] {
        let (obligation, _) = invalid_payload(format);
        let original = match format {
            ChcReplayPayloadFormat::GroundDerivationV1 => {
                crate::validate_chc_ground_derivation_artifact(&problem, b"{")
            }
            ChcReplayPayloadFormat::GroundDerivationV2 => {
                crate::validate_chc_ground_derivation_artifact_v2(&problem, b"{")
            }
            _ => unreachable!("test only selects ground formats"),
        }
        .expect_err("incomplete JSON must stay malformed");
        assert_eq!(
            original.reason,
            crate::ChcGroundDerivationArtifactErrorReason::MalformedEnvelope
        );
        let error = recheck_ground_with_budget(
            &problem,
            &obligation,
            b"{",
            Duration::from_mins(1),
            &Instant::now(),
        )
        .expect_err("a live budget cannot accept malformed evidence");
        assert_eq!(
            error.to_string(),
            verification_error(format!(
                "checked replay obligation {} ground derivation recheck: {original}",
                obligation.name,
            ))
            .to_string(),
        );
    }
}

#[test]
fn ground_dispatch_rejects_smt_format_without_calling_a_validator() {
    let (obligation, _) = invalid_payload(ChcReplayPayloadFormat::SmtlibV1);
    let mut calls = 0;
    let error =
        recheck_ground_with_progress(&crate::ChcProblem::new(), &obligation, b"{", &mut || {
            calls += 1;
            true
        })
        .expect_err("ground evidence cannot be relabeled as SMT-LIB");
    assert!(error
        .to_string()
        .contains("labels a ground derivation as SMT-LIB"));
    assert_eq!(calls, 0, "unsupported dispatch must not try another format");
}
