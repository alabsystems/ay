// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ground_derivation::compact::{
    self, Arena, CompactDerivation, CompactEvidence, CompactStep, Owner,
};
use crate::{ClauseBody, Counterexample, HornClause, VerifiedCounterexample};
use std::cell::Cell;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

mod caller_controls;

fn run() -> ChcPdrProofRun {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    let derivation = CompactDerivation {
        arena: Arena::new(),
        steps: vec![CompactStep {
            clause_index: 0,
            env: Default::default(),
            premises: vec![],
        }],
        query_step: 0,
    };
    let mut owner = Owner::capture().expect("original owner");
    compact::validate(&problem, &derivation, &mut owner).expect("original query replay");
    let candidate = Counterexample::new(vec![])
        .with_compact_ground_derivation(CompactEvidence::new(derivation, owner));
    ChcPdrProofRun::new(
        problem,
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(candidate)),
        "compact-replay-test",
    )
}

fn checked() -> ChcCheckedReplayRun {
    run()
        .run_checked_replay(Duration::from_secs(60))
        .expect("default compact checked replay")
}

#[test]
fn compact_summary_is_distinct_and_requires_a_fresh_opaque_capability() {
    let checked = checked();
    let summary = checked.summary();
    assert_eq!(
        summary.schema,
        crate::proof_metadata::CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V4
    );
    assert_eq!(summary.obligations.len(), 1);
    assert_eq!(
        summary.obligations[0].payload_format,
        Format::CompactGroundDerivationV1
    );
    let parsed =
        ChcCheckedReplaySummary::from_json_value(&summary.to_json_value()).expect("v4 roundtrip");
    assert_eq!(parsed.identity_sha256(), summary.identity_sha256());
    assert!(checked
        .manifest()
        .clone()
        .try_with_checked_replay_summary(parsed.clone())
        .is_err());
    let item = checked.obligation_payloads().next().expect("one payload");
    assert!(item.smt_query_bytes().is_none());
    assert!(item.ground_derivation_artifact_bytes().is_none());
    let bytes = item
        .compact_ground_derivation_artifact_bytes()
        .expect("explicit compact bytes");
    let snapshot = crate::validate_chc_compact_ground_derivation_artifact(
        checked.proof_run().problem(),
        bytes,
    )
    .expect("fresh original-source reader");
    assert!(checked
        .manifest()
        .clone()
        .try_with_validated_compact_ground_replay_summary(parsed, &snapshot)
        .is_ok());
    checked
        .recheck_with_fresh_ay(Duration::from_secs(60))
        .expect("fresh complete compact recheck");
}

#[test]
fn compact_payload_cannot_be_relabelled_as_legacy_or_safe() {
    let checked = checked();
    let bytes = checked
        .obligation_payloads()
        .next()
        .expect("row")
        .payload_bytes();
    let snapshot = crate::validate_chc_compact_ground_derivation_artifact(
        checked.proof_run().problem(),
        bytes,
    )
    .expect("snapshot");
    for (schema, version) in [
        (crate::proof_metadata::CHC_CHECKED_REPLAY_SUMMARY_SCHEMA, 1),
        (
            crate::proof_metadata::CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V2,
            2,
        ),
        (
            crate::proof_metadata::CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V3,
            3,
        ),
    ] {
        let mut altered = checked.summary().to_json_value();
        altered["schema"] = schema.into();
        altered["schema_version"] = version.into();
        assert!(ChcCheckedReplaySummary::from_json_value(&altered).is_err());
    }
    let mut summary = checked.summary().clone();
    summary.verdict = "safe".into();
    assert!(checked
        .manifest()
        .clone()
        .try_with_validated_compact_ground_replay_summary(summary, &snapshot)
        .is_err());
    let mut summary = checked.summary().clone();
    summary.obligations[0].kind = ChcReplayObligationKind::Safety;
    assert!(checked
        .manifest()
        .clone()
        .try_with_validated_compact_ground_replay_summary(summary, &snapshot)
        .is_err());
    for format in [
        Format::SmtlibV1,
        Format::GroundDerivationV1,
        Format::GroundDerivationV2,
    ] {
        let mut row = checked.summary().obligations[0].clone();
        row.payload_format = format;
        assert!(
            SealedReplayObligationPayload::try_new_compact_ground_derivation(
                &row,
                &snapshot,
                bytes.to_vec(),
                &mut || true
            )
            .is_err()
        );
    }
}

#[test]
fn changed_compact_bytes_or_descriptor_never_reseal_by_digest_alone() {
    let checked = checked();
    let bytes = checked
        .obligation_payloads()
        .next()
        .expect("row")
        .payload_bytes();
    let snapshot = crate::validate_chc_compact_ground_derivation_artifact(
        checked.proof_run().problem(),
        bytes,
    )
    .expect("snapshot");
    let row = &checked.summary().obligations[0];
    let mut altered = bytes.to_vec();
    altered[0] = b'[';
    assert!(
        SealedReplayObligationPayload::try_new_compact_ground_derivation(
            row,
            &snapshot,
            altered,
            &mut || true
        )
        .is_err()
    );
    let mut altered = row.clone();
    altered.query.sha256 = "0".repeat(64);
    assert!(
        SealedReplayObligationPayload::try_new_compact_ground_derivation(
            &altered,
            &snapshot,
            bytes.to_vec(),
            &mut || true
        )
        .is_err()
    );
}

#[test]
fn original_one_shot_refusal_prevents_replay_and_retry() {
    let armed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&armed);
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.swap(false, Ordering::SeqCst)
    }));
    let run = run();
    armed.store(true, Ordering::SeqCst);
    assert!(run.run_checked_replay(Duration::from_secs(60)).is_err());
    assert!(!armed.load(Ordering::SeqCst));
    assert!(
        run.run_checked_replay(Duration::from_secs(60)).is_err(),
        "original owner cannot be renewed"
    );
}

#[test]
fn later_ambient_one_shot_refusal_survives_scope_removal_and_retry() {
    let run = run();
    let armed = Arc::new(AtomicBool::new(true));
    let observed = Arc::clone(&armed);
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.swap(false, Ordering::SeqCst)
    }));
    assert!(run.run_checked_replay(Duration::from_secs(60)).is_err());
    assert!(!armed.load(Ordering::SeqCst), "later caller must be polled");
    drop(scope);
    assert!(
        run.run_checked_replay(Duration::from_secs(60)).is_err(),
        "dropping the later caller must not revive the retained witness"
    );
}

#[test]
fn healthy_later_ambient_callback_remains_part_of_complete_replay() {
    let run = run();
    let calls = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst);
        false
    }));
    let checked = run
        .run_checked_replay(Duration::from_secs(60))
        .expect("healthy later caller permits complete checked replay");
    assert!(calls.load(Ordering::SeqCst) > 1);
    assert_eq!(
        checked.summary().obligations[0].payload_format,
        Format::CompactGroundDerivationV1
    );
    drop(checked);
    drop(scope);
    run.run_checked_replay(Duration::from_secs(60))
        .expect("a healthy later caller does not poison the witness");
}

#[test]
fn later_ambient_callback_panic_latches_retained_witness() {
    let run = run();
    let scope =
        ay_core::resource::enter_check_stop(Arc::new(|| panic!("later replay caller panic")));
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run.run_checked_replay(Duration::from_secs(60))
    }));
    drop(scope);
    assert!(run.run_checked_replay(Duration::from_secs(60)).is_err());
}

#[test]
fn caller_refusal_covers_export_replay_and_final_publication() {
    let count = Cell::new(0usize);
    run()
        .run_checked_replay_with_progress(Duration::from_secs(60), &mut || {
            count.set(count.get() + 1);
            true
        })
        .expect("healthy complete run");
    let total = count.get();
    for stop_at in [1, total / 2, total.saturating_sub(1)] {
        let count = Cell::new(0usize);
        assert!(
            run()
                .run_checked_replay_with_progress(Duration::from_secs(60), &mut || {
                    count.set(count.get() + 1);
                    count.get() != stop_at
                })
                .is_err(),
            "refusal at {stop_at} must not publish"
        );
    }
}

#[test]
fn compact_format_cannot_enter_legacy_export_or_smt_fallback() {
    let mut callback = || true;
    let mut progress = ReplayProgress::new_retained_for_rows(
        ReplayLimit::Until(Instant::now() + Duration::from_secs(60)),
        &mut callback,
        1,
    )
    .unwrap();
    let result = super::super::ground_export::select_plan(
        Some(Format::CompactGroundDerivationV1),
        |_, _| panic!("compact format must not enter recursive exporter"),
        || panic!("compact refusal must not launch SMT"),
        &mut progress,
    );
    assert!(result.is_err());
}

#[test]
fn initial_borrowed_refusal_or_panic_latches_original_before_replay_admission() {
    let run = run();
    assert!(run
        .run_checked_replay_with_progress(Duration::from_secs(60), &mut || false)
        .is_err());
    assert!(run.run_checked_replay(Duration::from_secs(60)).is_err());

    let another = self::run();
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        another.run_checked_replay_with_progress(Duration::from_secs(60), &mut || {
            panic!("borrowed refusal")
        })
    }));
    assert!(another.run_checked_replay(Duration::from_secs(60)).is_err());
}

#[test]
fn compact_source_schema_and_hash_are_one_authenticated_pair() {
    let checked = checked();
    let bytes = checked
        .obligation_payloads()
        .next()
        .expect("row")
        .payload_bytes();
    let snapshot = crate::validate_chc_compact_ground_derivation_artifact(
        checked.proof_run().problem(),
        bytes,
    )
    .expect("snapshot");
    let mut altered = checked.manifest().clone();
    altered.problem_schema = crate::proof_metadata::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA;
    altered.transcript_metadata.normalized_input_schema = altered.problem_schema;
    let error = altered
        .try_with_validated_compact_ground_replay_summary(checked.summary().clone(), &snapshot)
        .expect_err("authentic hashes cannot authorize a spliced source schema");
    assert!(error
        .reasons()
        .iter()
        .any(|reason| reason.contains("normalized schema mismatch")));
}
