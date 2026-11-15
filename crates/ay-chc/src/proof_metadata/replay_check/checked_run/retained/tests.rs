// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Live-query sealing controls. Fixture allocations and deliberate private
//! mutations are test-owned, not a public capability construction API.

use super::*;
use crate::smt::executor_adapter::{
    check_plain_unsat_retained_native_with_progress, ReplayCancellation, ReplayLimit,
};
use crate::{
    engines, CancellationToken, ChcObligationStrictCert, ChcParser, ChcProofArtifactDigest,
    ChcReplayCheckResult, ChcReplayObligationKind, PdrConfig,
};
use ay_core::time::Instant;
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Duration;

mod causal;
mod control;
mod diagnostic_bridge;
mod settlement;

const BUDGET: Duration = Duration::from_secs(60);
const UNSAT: &str = "; keep original source bytes\n(set-logic QF_UF)\n\
    (declare-const p Bool) (assert p) (assert (not p)) (check-sat)\n";
const OTHER_UNSAT: &str = "(set-logic QF_UF)\n\
    (declare-const other Bool) (assert other) (assert (not other)) (check-sat)\n";

fn deadline() -> Instant {
    Instant::now() + BUDGET
}

fn encoded(progress: &mut RetainedReplayProgress<'_>) -> BoundRetainedProofBytes {
    check_plain_unsat_retained_native_with_progress(UNSAT, progress)
        .expect("Boolean contradiction must acquire live exact-query authority")
        .encode(progress)
        .expect("same original owner must encode actual-v4 evidence")
}

fn row(query: &[u8], bundle: &[u8]) -> ChcCheckedReplayObligation {
    ChcCheckedReplayObligation::new(
        "retained-live-query",
        ChcReplayObligationKind::Safety,
        ChcProofArtifactDigest::from_bytes("replay-obligation", query),
        "test-only-retained-reader",
        ChcReplayCheckResult::pass(),
    )
    .with_strict_cert(ChcObligationStrictCert::new_retained(
        None,
        crate::proof_metadata::sha256_hex(bundle),
        "verified",
    ))
}

fn sealed(
    progress: &mut RetainedReplayProgress<'_>,
) -> (ChcCheckedReplayObligation, SealedReplayObligationPayload) {
    let bound = encoded(progress);
    let row = row(bound.query_bytes(), bound.bundle_bytes());
    let payload = SealedReplayObligationPayload::try_new_retained(&row, bound, progress)
        .expect("aligned live-query capability must seal its original row");
    (row, payload)
}

fn assert_reader(bytes: &[u8], progress: &mut RetainedReplayProgress<'_>) {
    let document: serde_json::Value = serde_json::from_slice(bytes).unwrap();
    assert_eq!(
        document["schema"],
        ay_dpll::api::RETAINED_PROOF_BUNDLE_SCHEMA
    );
    assert!(document.get("retained").is_some());
    assert!(serde_json::from_slice::<ay_dpll::api::SerializableProofBundle>(bytes).is_err());
    let limits = progress.transport_limits();
    let original_deadline = progress.deadline();
    let (bundle, checked) = ay_dpll::api::read_retained_proof_bundle_with_resource_control(
        bytes,
        limits,
        original_deadline,
        &mut |work, bytes| progress.charge(work, bytes),
    )
    .expect("actual-v4 reader must independently replay the sealed proof");
    let unique = progress.ordered_unique(&checked.assume_terms).unwrap();
    assert!(checked.quality.is_complete());
    assert!(!unique.is_empty());
    assert!(progress.equal_ids(&unique, bundle.obligation_assertions()));
    drop((unique, checked, bundle));
    progress.check().unwrap();
}

#[test]
fn live_boolean_capability_seals_actual_v4_and_controlled_reader_replays_it() {
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let original_deadline = deadline();
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(original_deadline), &mut callback).unwrap();
    let (row, payload) = sealed(&mut progress);
    let SealedReplayObligationPayload::Smt {
        obligation_identity_sha256,
        query_bytes,
        strict_bundle_bytes,
        alethe_bytes,
        source_authority,
    } = &payload
    else {
        panic!("retained capability must seal an SMT payload");
    };
    assert_eq!(*source_authority, SmtSourceAuthority::RetainedLiveQuery);
    assert_eq!(query_bytes, UNSAT.as_bytes());
    assert_eq!(obligation_identity_sha256, &row.identity_sha256());
    assert!(alethe_bytes.is_none());
    let cert = row.strict_cert.as_ref().unwrap();
    assert!(cert.is_retained_bundle_commitment());
    assert_eq!(
        cert.proof_bundle_schema,
        ay_dpll::api::RETAINED_PROOF_BUNDLE_SCHEMA
    );
    let bytes = strict_bundle_bytes.as_deref().unwrap();
    assert_eq!(cert.bundle_sha256, crate::proof_metadata::sha256_hex(bytes));
    let before = calls.get();
    assert_reader(bytes, &mut progress);
    assert!(calls.get() > before);
    payload
        .validate_retained_with_resources(&row, &mut progress)
        .unwrap();
    assert_eq!(progress.deadline(), original_deadline);
}

#[test]
fn raw_legacy_constructor_cannot_mint_v4_even_with_valid_rechecked_bytes() {
    let mut callback = || true;
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let bound = encoded(&mut progress);
    let row = row(bound.query_bytes(), bound.bundle_bytes());
    assert_reader(bound.bundle_bytes(), &mut progress);
    let error = SealedReplayObligationPayload::try_new_smt(
        &row,
        bound.query_bytes().to_vec(),
        Some(bound.bundle_bytes().to_vec()),
        None,
    )
    .unwrap_err();
    assert!(error.to_string().contains("live exact-query capability"));
    SealedReplayObligationPayload::try_new_retained(&row, bound, &mut progress).unwrap();
}

#[test]
fn swapped_source_row_with_recomputed_query_digest_cannot_use_another_capability() {
    let mut callback = || true;
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let bound = encoded(&mut progress);
    let original = row(bound.query_bytes(), bound.bundle_bytes());
    let swapped = row(OTHER_UNSAT.as_bytes(), bound.bundle_bytes());
    assert_ne!(original.query.sha256, swapped.query.sha256);
    assert_eq!(
        swapped.query.sha256,
        crate::proof_metadata::sha256_hex(OTHER_UNSAT.as_bytes())
    );
    let error = SealedReplayObligationPayload::try_new_retained(&swapped, bound, &mut progress)
        .unwrap_err();
    assert!(error.to_string().contains("query descriptor mismatch"));
}

#[test]
fn terminal_proof_tampering_is_rejected_after_bundle_digest_and_row_identity_are_recooked() {
    let mut callback = || true;
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let (mut row, mut payload) = sealed(&mut progress);
    let SealedReplayObligationPayload::Smt {
        strict_bundle_bytes,
        ..
    } = &mut payload
    else {
        panic!("fixture must carry a retained SMT proof");
    };
    let bytes = strict_bundle_bytes.as_mut().unwrap();
    let mut document: serde_json::Value = serde_json::from_slice(bytes).unwrap();
    let steps = document["steps"].as_array_mut().unwrap();
    assert!(steps.len() >= 3);
    steps.pop().unwrap(); // Valid typed JSON, but no final empty-clause proof.
    *bytes = serde_json::to_vec(&document).unwrap();
    row.strict_cert.as_mut().unwrap().bundle_sha256 = crate::proof_metadata::sha256_hex(bytes);
    let recooked = identity(&row, &mut progress).unwrap();
    let SealedReplayObligationPayload::Smt {
        obligation_identity_sha256,
        ..
    } = &mut payload
    else {
        unreachable!();
    };
    *obligation_identity_sha256 = recooked;
    let error = payload
        .validate_retained_with_resources(&row, &mut progress)
        .unwrap_err();
    assert!(error.to_string().contains("v4 replay"));
    assert!(!error.to_string().contains("digest mismatch"));
}

#[test]
fn sealing_cannot_adopt_a_capability_from_a_different_request_owner() {
    let mut first_callback = || true;
    let mut first =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut first_callback).unwrap();
    let bound = encoded(&mut first);
    let row = row(bound.query_bytes(), bound.bundle_bytes());
    let mut fresh_callback = || true;
    let mut fresh =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut fresh_callback).unwrap();
    assert!(SealedReplayObligationPayload::try_new_retained(&row, bound, &mut fresh).is_err());
    assert!(fresh.check().is_err());
    first.check().unwrap();
}

#[test]
fn inherited_cancellation_between_encoding_and_sealing_stays_stopped_after_reset() {
    let parent = CancellationToken::new();
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
    let bound = encoded(&mut progress);
    let row = row(bound.query_bytes(), bound.bundle_bytes());
    parent.cancel();
    assert!(SealedReplayObligationPayload::try_new_retained(&row, bound, &mut progress).is_err());
    parent.reset();
    assert!(progress.check().is_err());
}

#[test]
fn sealing_callback_refusal_cannot_be_reset_or_obtain_more_callback_credit() {
    let allow = Cell::new(true);
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        allow.get()
    };
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let bound = encoded(&mut progress);
    let row = row(bound.query_bytes(), bound.bundle_bytes());
    allow.set(false);
    assert!(SealedReplayObligationPayload::try_new_retained(&row, bound, &mut progress).is_err());
    let stopped_calls = calls.get();
    allow.set(true);
    assert!(progress.check().is_err());
    assert_eq!(calls.get(), stopped_calls);
}

#[test]
fn caught_callback_panic_during_sealing_permanently_poisons_the_original_owner() {
    let panic_next = Cell::new(false);
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        assert!(!panic_next.replace(false), "test-only callback panic");
        true
    };
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let bound = encoded(&mut progress);
    let row = row(bound.query_bytes(), bound.bundle_bytes());
    panic_next.set(true);
    assert!(catch_unwind(AssertUnwindSafe(|| {
        SealedReplayObligationPayload::try_new_retained(&row, bound, &mut progress)
    }))
    .is_err());
    assert!(!panic_next.get());
    let stopped_calls = calls.get();
    assert!(progress.check().is_err());
    assert_eq!(calls.get(), stopped_calls);
}

#[test]
fn safe_pdr_emits_nonempty_multirow_v4_and_preserves_fresh_original_query_redischarge() {
    let problem = ChcParser::parse(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#,
    )
    .unwrap();
    let run = engines::solve_pdr_proof(problem, PdrConfig::default()).unwrap();
    assert!(run.accepted_as_proof());
    assert_eq!(run.metadata().result, "safe");
    let checked = run.run_checked_replay(BUDGET).unwrap();
    assert!(checked.summary().obligations.len() >= 3);
    let mut callback = || true;
    let mut consumer =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let mut rows = 0;
    for view in checked.obligation_payloads() {
        rows += 1;
        let row = view.obligation();
        assert_ne!(row.kind, ChcReplayObligationKind::TraceValidity);
        let cert = row.strict_cert.as_ref().unwrap();
        assert!(cert.is_retained_bundle_commitment());
        assert_eq!(
            cert.proof_bundle_schema,
            ay_dpll::api::RETAINED_PROOF_BUNDLE_SCHEMA
        );
        assert_eq!(cert.verdict, "verified");
        assert!(cert.alethe_sha256.is_none());
        assert!(view.alethe_bytes().is_none());
        assert_eq!(
            row.query.sha256,
            crate::proof_metadata::sha256_hex(view.smt_query_bytes().unwrap())
        );
        assert_reader(view.strict_bundle_bytes().unwrap(), &mut consumer);
    }
    assert_eq!(rows, checked.summary().obligations.len());
    drop(consumer);
    // Offline inventory validity is not external-query authority. This public
    // consumer must ALSO freshly discharge every sealed ORIGINAL query.
    checked.recheck_with_fresh_ay(BUDGET).unwrap();
}
