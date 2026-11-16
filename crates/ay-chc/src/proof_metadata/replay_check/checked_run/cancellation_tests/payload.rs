// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn sat_parts() -> (ChcCheckedReplayObligation, Vec<u8>) {
    let query = b"(assert true)\n(check-sat)\n".to_vec();
    let obligation = ChcCheckedReplayObligation::new(
        "retained-sealing",
        ChcReplayObligationKind::TraceValidity,
        ChcProofArtifactDigest::from_bytes("replay-obligation", &query),
        "test-only",
        crate::ChcReplayCheckResult::pass(),
    );
    (obligation, query)
}

fn actual_strict_payload() -> (ChcCheckedReplayObligation, SealedReplayObligationPayload) {
    let query = "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(check-sat)\n(exit)\n";
    let cert = crate::smt::executor_adapter::smtlib_strict_unsat_cert_via_executor_until(
        query,
        fresh_recheck_deadline(Instant::now(), BUDGET).unwrap(),
    )
    .expect("fixture must acquire a real exact-query certificate and strict recheck");
    let bundle = serde_json::to_vec(&cert.bundle).unwrap();
    let record = crate::ChcObligationStrictCert::new_bundle(
        cert.bundle.schema.clone(),
        None,
        crate::proof_metadata::sha256_hex(&bundle),
        "verified",
    );
    let obligation = ChcCheckedReplayObligation::new(
        "retained-offline",
        ChcReplayObligationKind::Safety,
        ChcProofArtifactDigest::from_bytes("replay-obligation", query.as_bytes()),
        "test-only",
        crate::ChcReplayCheckResult::pass(),
    )
    .with_strict_cert(record);
    let payload = SealedReplayObligationPayload::try_new_smt(
        &obligation,
        query.as_bytes().to_vec(),
        Some(bundle),
        None,
    )
    .unwrap();
    (obligation, payload)
}

#[test]
fn controlled_sealing_is_byte_exact_and_refuses_every_callback() {
    let (obligation, bytes) = sat_parts();
    let legacy =
        SealedReplayObligationPayload::try_new_smt(&obligation, bytes.clone(), None, None).unwrap();
    let mut samples = 0;
    let controlled = SealedReplayObligationPayload::try_new_smt_with_progress(
        &obligation,
        bytes.clone(),
        None,
        None,
        &mut || {
            samples += 1;
            true
        },
    )
    .unwrap();
    let (
        SealedReplayObligationPayload::Smt {
            obligation_identity_sha256: expected,
            query_bytes: expected_bytes,
            ..
        },
        SealedReplayObligationPayload::Smt {
            obligation_identity_sha256: actual,
            query_bytes: actual_bytes,
            ..
        },
    ) = (legacy, controlled)
    else {
        panic!("sealing may not change the representation");
    };
    assert_eq!(actual, expected);
    assert_eq!(actual_bytes, expected_bytes);
    assert!(samples > 4);
    for stop_at in 1..=samples {
        let mut ordinal = 0;
        assert_interrupted(SealedReplayObligationPayload::try_new_smt_with_progress(
            &obligation,
            bytes.clone(),
            None,
            None,
            &mut || {
                ordinal += 1;
                ordinal != stop_at
            },
        ));
        assert_eq!(
            ordinal, stop_at,
            "no callback retry or partially sealed value"
        );
    }
}

#[test]
fn actual_retained_offline_reader_shares_each_sticky_parent_callback() {
    let (obligation, payload) = actual_strict_payload();
    let mut samples = 0;
    payload
        .validate_with_progress(&obligation, &mut || {
            samples += 1;
            true
        })
        .unwrap();
    assert!(
        samples > 20,
        "must enter the real offline reader, not just phase wrappers"
    );
    for stop_at in 1..=samples {
        let parent = CancellationToken::new();
        let token = parent.child();
        let cancellation = ReplayCancellation::new(&token);
        let control = live_control(&cancellation);
        let mut ordinal = 0;
        assert_interrupted(payload.validate_with_progress(&obligation, &mut || {
            ordinal += 1;
            if ordinal == stop_at {
                parent.cancel();
            }
            control.allows(&mut Instant::now)
        }));
        assert_eq!(ordinal, stop_at);
        parent.reset();
        assert!(cancellation.is_cancelled());
    }
    payload.validate(&obligation).unwrap();
}

#[test]
fn retained_bundle_and_descriptor_mutations_keep_the_exact_live_rejection() {
    let (obligation, payload) = actual_strict_payload();
    let mut bad_bytes = payload.clone();
    let SealedReplayObligationPayload::Smt {
        strict_bundle_bytes: Some(bytes),
        ..
    } = &mut bad_bytes
    else {
        panic!("fixture must retain its independently checked proof bundle");
    };
    bytes[0] ^= 1;
    let mut wrong_identity = obligation.clone();
    wrong_identity.name.push_str("-changed");
    for (row, evidence) in [(&obligation, &bad_bytes), (&wrong_identity, &payload)] {
        let expected = evidence.validate(row).unwrap_err().to_string();
        let actual = evidence
            .validate_with_progress(row, &mut || true)
            .unwrap_err()
            .to_string();
        assert_eq!(actual, expected);
        assert!(!actual.contains("interrupted"));
        let mut calls = 0;
        assert_interrupted(evidence.validate_with_progress(row, &mut || {
            calls += 1;
            false
        }));
        assert_eq!(calls, 1, "refusal precedes malformed evidence processing");
    }
}

#[test]
fn opaque_payload_phase_destruction_precedes_the_last_poll() {
    struct CancelOnDrop<'a>(&'a CancellationToken);
    impl Drop for CancelOnDrop<'_> {
        fn drop(&mut self) {
            self.0.cancel();
        }
    }
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let mut calls = 0;
    assert_interrupted(payload_phase(
        &mut || {
            calls += 1;
            !cancellation.is_cancelled()
        },
        |_| {
            let _owned_checker_state = CancelOnDrop(&token);
            Ok(())
        },
    ));
    assert_eq!(calls, 2);
    token.reset();
    assert!(cancellation.is_cancelled());
}
