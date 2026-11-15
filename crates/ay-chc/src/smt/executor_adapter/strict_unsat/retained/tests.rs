// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::executor_adapter::ReplayCancellation;
use std::time::Duration;

const UNSAT: &str = "; original bytes must survive\n(set-logic QF_LIA)\n\
    (declare-const x Int) (assert (> x 5)) (assert (< x 3)) (check-sat)\n";

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

#[test]
fn live_plain_query_mints_verified_actual_v4_and_preserves_original_bytes() {
    let mut callback = || true;
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let bound = check_plain_unsat_retained_native_with_progress(UNSAT, &mut progress).unwrap();
    let bytes = bound.encode(&mut progress).unwrap();
    assert_eq!(bytes.query_bytes(), UNSAT.as_bytes());
    assert!(
        matches!(bytes.strict_verdict(), ay_dpll::api::StrictProofVerdict::Verified(quality)
        if quality.is_complete())
    );
    let document: serde_json::Value = serde_json::from_slice(bytes.bundle_bytes()).unwrap();
    assert_eq!(document["schema"], "ay.proofbundle/v6");
    assert!(document.get("retained").is_some());
    bytes.admit(&mut progress).unwrap();
    let (query, bundle) = bytes.into_parts();
    assert_eq!(query, UNSAT.as_bytes());
    let (owner, checked) = ay_dpll::api::read_retained_proof_bundle_with_resource_control(
        &bundle,
        progress.transport_limits(),
        progress.deadline(),
        &mut |work, bytes| progress.charge(work, bytes),
    )
    .unwrap();
    let used = progress.ordered_unique(&checked.assume_terms).unwrap();
    assert!(checked.quality.is_complete());
    assert!(!used.is_empty());
    assert!(progress.equal_ids(&used, owner.obligation_assertions()));
    drop((owner, checked, used, query, bundle));
    progress.check().unwrap();
}

#[test]
fn live_datatype_and_folded_premises_keep_exact_retained_authority() {
    for script in [
        "(declare-datatype D ((a) (b))) (declare-const x D) (assert (= x a)) (assert (= x b)) (check-sat)",
        "(declare-const x Int) (assert (and (>= x 0) (not (> x 10)) (> x 10))) (check-sat)",
    ] {
        let mut callback = || true;
        let mut progress = RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        let bytes = check_plain_unsat_retained_native_with_progress(script, &mut progress).unwrap()
            .encode(&mut progress).unwrap();
        assert_eq!(bytes.query_bytes(), script.as_bytes());
        assert!(matches!(bytes.strict_verdict(), ay_dpll::api::StrictProofVerdict::Verified(quality)
            if quality.is_complete()));
        bytes.admit(&mut progress).unwrap();
    }
}

#[test]
fn non_plain_sat_and_explicit_wire_refusals_never_mint_a_bound_artifact() {
    for script in [
        "(assert true) (check-sat)",
        "(assert false) (check-sat-assuming ())",
        "(assert false) (check-sat) (check-sat)",
        "(assert false) (push 1) (check-sat)",
        "(assert false) (set-logic QF_LIA) (check-sat)",
        "(set-option :timeout 0) (assert false) (check-sat)",
        "(set-option :check-proofs-strict true) (declare-datatype D ((a) (b))) (declare-const x D) (assert (= x a)) (assert (= x b)) (check-sat)",
        "(invalid unmatched",
    ] {
        let mut callback = || true;
        let mut progress = RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        assert!(check_plain_unsat_retained_native_with_progress(script, &mut progress).is_err(), "{script}");
        assert!(progress.check().is_err(), "refusal must remain sticky: {script}");
    }
}

#[test]
fn encoding_cannot_renew_a_live_bound_capability_with_a_new_ledger() {
    let mut first_callback = || true;
    let mut first =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut first_callback).unwrap();
    let bound = check_plain_unsat_retained_native_with_progress(UNSAT, &mut first).unwrap();
    let mut fresh_callback = || true;
    let mut fresh =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut fresh_callback).unwrap();
    assert!(bound.encode(&mut fresh).is_err());
    assert!(fresh.check().is_err());
    first.check().unwrap();
}

#[test]
fn encoded_capability_cannot_admit_under_another_request_owner() {
    let mut first_callback = || true;
    let mut first =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut first_callback).unwrap();
    let bytes = check_plain_unsat_retained_native_with_progress(UNSAT, &mut first)
        .unwrap()
        .encode(&mut first)
        .unwrap();
    let mut fresh_callback = || true;
    let mut fresh =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut fresh_callback).unwrap();
    assert!(bytes.admit(&mut fresh).is_err());
    assert!(fresh.check().is_err());
    bytes.admit(&mut first).unwrap();
}

#[test]
fn cancellation_between_export_and_encoding_is_sticky_after_parent_reset() {
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let mut callback = || true;
    let mut progress = RetainedReplayProgress::new(
        ReplayLimit::Cancellable {
            deadline: deadline(),
            cancellation: &cancellation,
        },
        &mut callback,
    )
    .unwrap();
    let bound = check_plain_unsat_retained_native_with_progress(UNSAT, &mut progress).unwrap();
    parent.cancel();
    assert!(bound.encode(&mut progress).is_err());
    parent.reset();
    assert!(progress.check().is_err());
}

#[test]
fn original_interphase_deadline_cannot_be_reopened_for_encoding() {
    let original = Instant::now() + Duration::from_secs(2);
    let mut callback = || true;
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(original), &mut callback).unwrap();
    let bound = check_plain_unsat_retained_native_with_progress(UNSAT, &mut progress).unwrap();
    assert_eq!(progress.deadline(), original);
    std::thread::sleep(
        original.saturating_duration_since(Instant::now()) + Duration::from_millis(5),
    );
    assert!(bound.encode(&mut progress).is_err());
    assert_eq!(progress.deadline(), original);
    assert!(progress.check().is_err());
}
