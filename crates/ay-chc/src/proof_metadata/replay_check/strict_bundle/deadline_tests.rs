// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::pdr::ChcReplayObligationKind;
use crate::smt::executor_adapter::{smtlib_strict_unsat_cert_via_executor_until, StrictUnsatCert};
use ay_core::time::Instant;
use std::time::Duration;

fn obligation() -> ChcReplayObligation {
    ChcReplayObligation {
        name: "strict-bundle-deadline".into(),
        kind: ChcReplayObligationKind::Safety,
        clause_index: 0,
        smtlib: "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(check-sat)\n".into(),
    }
}

fn live_deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn certificate(obligation: &ChcReplayObligation) -> StrictUnsatCert {
    smtlib_strict_unsat_cert_via_executor_until(&obligation.smtlib, live_deadline())
        .expect("exact contradiction must produce independently checked evidence")
}

#[test]
fn expired_discharge_declines_before_parsing_or_failure_diagnostics() {
    let mut obligation = obligation();
    obligation.smtlib = "(malformed".into();
    let error = discharge(&obligation, ReplayLimit::Until(Instant::now()), "unsat")
        .err()
        .unwrap();
    assert_eq!(error.to_string(), exhausted().to_string());
}

#[test]
fn cancelled_parent_discharge_declines_before_parsing_or_failure_diagnostics() {
    let mut obligation = obligation();
    obligation.smtlib = "(malformed".into();
    let parent = crate::CancellationToken::new();
    let token = parent.child();
    let cancellation = crate::smt::executor_adapter::ReplayCancellation::new(&token);
    parent.cancel();
    let limit = ReplayLimit::Cancellable {
        deadline: live_deadline(),
        cancellation: &cancellation,
    };
    let error = discharge(&obligation, limit, "unsat").err().unwrap();
    assert_eq!(error.to_string(), exhausted().to_string());
    parent.reset();
    assert!(discharge(&obligation, limit, "unsat").is_err());
    assert!(!token.is_cancelled());
}

#[test]
fn serialization_keeps_exact_native_bytes_and_optional_alethe_digest() {
    let obligation = obligation();
    let native = certificate(&obligation);
    let expected_bundle = serde_json::to_vec(&native.bundle).unwrap();
    let expected_alethe = native.alethe.as_ref().map(|text| text.as_bytes().to_vec());
    let expected = ChcObligationStrictCert::new_bundle(
        native.bundle.schema.clone(),
        expected_alethe
            .as_deref()
            .map(super::super::super::sha256_hex),
        super::super::super::sha256_hex(&expected_bundle),
        "verified",
    );
    let limit = ReplayLimit::Until(live_deadline());
    let (record, bundle, alethe) = limit
        .phase(|| Some(cert_from_checked_bundle(&obligation, native, limit)))
        .unwrap()
        .unwrap();
    assert_eq!(record.to_json_value(), expected.to_json_value());
    assert_eq!(bundle, expected_bundle);
    assert_eq!(alethe, expected_alethe);
}

#[test]
fn live_serialization_still_rejects_incomplete_verdict() {
    let obligation = obligation();
    let mut native = certificate(&obligation);
    native.strict_verdict = ay_dpll::api::StrictProofVerdict::Rejected("mutation".into());
    let error = cert_from_checked_bundle(&obligation, native, ReplayLimit::Until(live_deadline()))
        .err()
        .unwrap();
    assert!(error
        .to_string()
        .contains("native strict bundle verdict is not complete"));
}

#[test]
fn expired_serialization_refuses_before_verdict_inspection() {
    let obligation = obligation();
    let mut native = certificate(&obligation);
    native.strict_verdict = ay_dpll::api::StrictProofVerdict::Rejected("mutation".into());
    let error = cert_from_checked_bundle(&obligation, native, ReplayLimit::Until(Instant::now()))
        .err()
        .unwrap();
    assert_eq!(error.to_string(), exhausted().to_string());
}

#[test]
fn live_discharge_retains_replayable_exact_bundle() {
    let obligation = obligation();
    let result = discharge(&obligation, ReplayLimit::Until(live_deadline()), "unsat").unwrap();
    let bundle: ay_dpll::api::SerializableProofBundle =
        serde_json::from_slice(&result.bundle_bytes).unwrap();
    let checked = ay_dpll::api::re_check_bundle_strict(&bundle).unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(bundle.obligation_assertions.len(), 2);
    assert_eq!(
        result.checker_command,
        format!(
            "{} --strict-proof-bundle --expect unsat {}",
            super::super::CHC_IN_PROCESS_REPLAY_CHECKER_NAME,
            obligation.name,
        )
    );
}
