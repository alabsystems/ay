// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

const SAT: &[u8] = b"(set-logic QF_LIA)\n(assert true)\n(check-sat)\n";
const UNSAT: &[u8] = b"(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(check-sat)\n(exit)\n";

fn row(query: &[u8], kind: ChcReplayObligationKind) -> ChcCheckedReplayObligation {
    ChcCheckedReplayObligation::new(
        "retained-cancellation",
        kind,
        ChcProofArtifactDigest::from_bytes("replay-obligation", query),
        "test-only",
        crate::ChcReplayCheckResult::pass(),
    )
}

#[test]
fn live_typed_control_preserves_actual_sat_and_exact_strict_unsat() {
    for (query, kind) in [
        (SAT, ChcReplayObligationKind::TraceValidity),
        (UNSAT, ChcReplayObligationKind::Safety),
    ] {
        let parent = CancellationToken::new();
        let token = parent.child();
        let cancellation = ReplayCancellation::new(&token);
        recheck_smt_payload_with_control(query, &row(query, kind), live_control(&cancellation))
            .unwrap();
        assert!(!parent.is_cancelled());
        assert!(!token.is_cancelled());
    }
}

#[test]
fn both_smt_kinds_decline_precancel_and_malformed_queries_without_starting() {
    let parent = CancellationToken::new();
    let token = parent.child();
    parent.cancel();
    let cancellation = ReplayCancellation::new(&token);
    parent.reset();
    for kind in [
        ChcReplayObligationKind::TraceValidity,
        ChcReplayObligationKind::Safety,
    ] {
        assert_interrupted(recheck_smt_payload_with_control(
            b"(malformed",
            &row(b"(malformed", kind),
            live_control(&cancellation),
        ));
    }
}

#[test]
fn a_live_token_never_changes_the_required_verdict_or_script_authority() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    for (query, kind) in [
        (SAT, ChcReplayObligationKind::Safety),
        (UNSAT, ChcReplayObligationKind::TraceValidity),
    ] {
        let error =
            recheck_smt_payload_with_control(query, &row(query, kind), live_control(&cancellation))
                .unwrap_err();
        assert!(error.to_string().contains("fresh AY recheck expected"));
    }
    let override_query = b"(set-option :timeout 99999999)\n(assert false)\n(check-sat)\n";
    assert!(recheck_smt_payload_with_control(
        override_query,
        &row(override_query, ChcReplayObligationKind::Safety),
        live_control(&cancellation),
    )
    .is_err());
}
