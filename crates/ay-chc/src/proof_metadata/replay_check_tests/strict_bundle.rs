// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked-replay assertions for bundle authority and optional Alethe output.

use super::*;

pub(super) fn assert_strict_bundle_rows(checked: &ChcCheckedReplayRun) {
    assert!(
        !checked.summary().obligations.is_empty(),
        "safe PDR proof should have replay obligations"
    );
    for obligation in &checked.summary().obligations {
        assert_ne!(obligation.kind, ChcReplayObligationKind::TraceValidity);
        let cert = obligation.strict_cert.as_ref().unwrap_or_else(|| {
            panic!(
                "unsat obligation {} must carry a native strict bundle cert",
                obligation.name
            )
        });
        assert_eq!(cert.verdict, "verified");
        assert_eq!(
            cert.proof_bundle_schema,
            ay_dpll::api::RETAINED_PROOF_BUNDLE_SCHEMA
        );
        assert!(cert.is_retained_bundle_commitment());
        if let Some(alethe_sha256) = &cert.alethe_sha256 {
            assert_eq!(alethe_sha256.len(), 64);
        }
        assert_eq!(cert.bundle_sha256.len(), 64);
    }

    let payloads: Vec<_> = checked.obligation_payloads().collect();
    assert_eq!(payloads.len(), checked.summary().obligations.len());
    for payload in payloads {
        let obligation = payload.obligation();
        let query_bytes = payload
            .smt_query_bytes()
            .expect("UNSAT row must retain an SMT-LIB query");
        assert_eq!(obligation.query.sha256, sha256_hex(query_bytes));
        assert_eq!(obligation.query.bytes, query_bytes.len() as u64);
        let bundle_bytes = payload
            .strict_bundle_bytes()
            .expect("UNSAT row must retain serialized strict bundle bytes");
        let cert = obligation
            .strict_cert
            .as_ref()
            .expect("UNSAT row must retain its strict commitment");
        assert_eq!(cert.bundle_sha256, sha256_hex(bundle_bytes));
        let deadline = ay_core::time::Instant::now() + Duration::from_secs(60);
        let limits = ay_dpll::api::RetainedProofTransportLimits {
            max_json_bytes: bundle_bytes.len(),
            max_storage_bytes: ay_dpll::api::MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA,
            max_work: ay_dpll::api::MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA,
        };
        let rechecked = ay_dpll::api::re_check_retained_bundle_strict_with_resource_control(
            bundle_bytes,
            limits,
            deadline,
            &mut |_, _| true,
        )
        .expect("actual-v4 strict bundle must independently replay");
        assert!(rechecked.quality.is_complete());
        match (cert.alethe_sha256.as_deref(), payload.alethe_bytes()) {
            (Some(expected), Some(bytes)) => assert_eq!(expected, sha256_hex(bytes)),
            (None, None) => {}
            mismatch => panic!("Alethe payload/commitment mismatch: {mismatch:?}"),
        }
    }

    let replay_log: serde_json::Value = serde_json::from_slice(checked.replay_log_bytes())
        .expect("checked replay log should be JSON");
    for record in replay_log["obligations"]
        .as_array()
        .expect("replay obligations array")
    {
        assert_eq!(record["strict_bundle"], true);
        let alethe_present = record["strict_cert"].get("alethe_sha256").is_some();
        assert_eq!(record["strict_alethe"], alethe_present);
    }
}
