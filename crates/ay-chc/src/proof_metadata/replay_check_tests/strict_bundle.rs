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
        assert_eq!(cert.proof_bundle_schema, ay_dpll::api::PROOF_BUNDLE_SCHEMA);
        if let Some(alethe_sha256) = &cert.alethe_sha256 {
            assert_eq!(alethe_sha256.len(), 64);
        }
        assert_eq!(cert.bundle_sha256.len(), 64);
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
