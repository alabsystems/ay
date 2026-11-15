// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn constructor_invocations_keep_distinct_identity_and_real_typed_context() {
    let bundle = fixture();
    let original = original();
    let original_owner = owner(&original);
    let mut identities = Vec::new();
    for (case, seq) in [(R34Witness::Static0001, 1), (R34Witness::Static0003, 3)] {
        let record = bundle.inspect_witness(case, &original_owner).unwrap();
        assert_eq!(record.sequence, seq);
        assert_eq!(record.clause_index, 14);
        assert_eq!(record.datatype_definitions, 7);
        assert_eq!(
            record.current_query_schema.as_deref(),
            Some("ay.chc.normalized-input/v2")
        );
        let smt = record.qualified_expression.as_ref().unwrap();
        assert!(smt.contains("(as Coroutine_390_mk Coroutine_390)"));
        assert!(smt.contains("Coroutine_390::DirectFields_mk"));
        assert!(!smt.contains("Coroutine_390_mk:Datatype"));
        assert!(record
            .blockers
            .contains(&R34WitnessBlocker::MissingOriginalRemainingBudget));
        assert!(record
            .blockers
            .iter()
            .any(|b| matches!(b, R34WitnessBlocker::IdentityMigration { .. })));
        assert!(!record.solver_invoked);
        assert!(!record.promotable_for_ask_closure);
        identities.push(record.current_query_sha256.unwrap());
    }
    assert_eq!(identities[0], identities[1]);
}

#[test]
fn original_constructor_captures_have_identical_bytes_but_not_sequence_numbers() {
    let bundle = fixture();
    let base = &bundle.capture.sources["static"].base;
    for (seq, original) in [
        (1, include_str!("../fixtures/static-0001.normalized")),
        (3, include_str!("../fixtures/static-0003.normalized")),
    ] {
        assert_eq!(
            bundle
                .text(&format!("{base}/witness/{seq:04}.normalized"))
                .unwrap(),
            original
        );
        assert_eq!(
            capture::digest(original.as_bytes()),
            "16d3e5c37525ac46567bc21669867ab63e21bdad12e105a65f6de7c766126ce1"
        );
    }
    assert_ne!(
        bundle.capture.witnesses[0].record["seq"],
        bundle.capture.witnesses[1].record["seq"]
    );
}

#[test]
fn bitmask_preserves_original_full_array_query_without_inventing_predecessor_recipe() {
    let bundle = fixture();
    let record = bundle
        .inspect_witness(R34Witness::Bitmask0026, &owner(&original()))
        .unwrap();
    assert_eq!(record.sequence, 26);
    assert_eq!(record.clause_index, 26);
    assert_eq!(record.original_result, "unknown");
    assert_eq!(
        record.captured_smtlib_sha256.as_deref(),
        Some("1600f7ec7236b52fe54da2b3f31895007fc3caad505921620987763159f317a3")
    );
    let smt = include_str!("../fixtures/bitmask-0026.smt2");
    assert_eq!(
        capture::digest(smt.as_bytes()),
        record.captured_smtlib_sha256.unwrap()
    );
    assert!(smt.contains("(Array (_ BitVec 64) (_ BitVec 32))"));
    assert!(smt.contains("store"));
    assert!(record
        .blockers
        .contains(&R34WitnessBlocker::MissingOriginalRemainingBudget));
    assert!(record
        .blockers
        .contains(&R34WitnessBlocker::MissingAggregatePreparation));
    assert!(!record.solver_invoked);
    assert!(!record.promotable_for_ask_closure);
}

#[test]
fn a_boolean_claim_that_missing_budget_exists_cannot_unlock_solver_execution() {
    let mut bundle = fixture();
    bundle.capture.witnesses[0].remaining_budget_recorded = true;
    assert!(bundle
        .inspect_witness(R34Witness::Static0001, &owner(&original()))
        .is_err());
}

#[test]
fn expired_witness_owner_is_reused_and_no_new_duration_is_granted() {
    let bundle = fixture();
    let mut guard = original();
    guard.set_deadline(Some(Instant::now()));
    let owner = owner(&guard);
    let deadline = owner.deadline();
    for case in R34Witness::ALL {
        let record = bundle.inspect_witness(case, &owner).unwrap();
        assert!(record.blockers.iter().any(|b| matches!(b,
            R34WitnessBlocker::OwnerRefused { observed } if observed == "Timeout")));
        assert!(record.current_query_sha256.is_none());
        assert!(!record.solver_invoked);
        assert_eq!(owner.deadline(), deadline);
    }
}

#[test]
fn witness_work_boundaries_preserve_the_original_sticky_worklimit() {
    let bundle = fixture();
    let healthy = original();
    let complete = bundle
        .inspect_witness(R34Witness::Static0001, &owner(&healthy))
        .unwrap();
    assert!(complete.current_query_sha256.is_some());
    let work = healthy.ticks();
    assert!(work > 1);
    for cut in work_cut_boundaries(work) {
        let mut limited = original();
        limited.set_rlimit(Some(cut));
        let owner = owner(&limited);
        let record = bundle
            .inspect_witness(R34Witness::Static0001, &owner)
            .unwrap();
        assert!(
            record.blockers.iter().any(|b| matches!(b,
            R34WitnessBlocker::OwnerRefused { observed } if observed == "WorkLimit")),
            "cut={cut}"
        );
        assert!(!record.solver_invoked);
        let spent = limited.ticks();
        assert_eq!(format!("{:?}", owner.clone().check()), "Some(WorkLimit)");
        assert_eq!(limited.ticks(), spent);
    }
}

#[test]
fn panicking_original_observer_refuses_binding_and_keeps_the_first_cause() {
    let bundle = fixture();
    let scope =
        ay_core::resource::enter_check_stop(std::sync::Arc::new(|| panic!("R34 observer control")));
    let original_owner = owner(&original());
    let record = bundle
        .inspect_witness(R34Witness::Static0001, &original_owner)
        .unwrap();
    assert!(record.blockers.iter().any(|b| matches!(b,
        R34WitnessBlocker::OwnerRefused { observed } if observed == "Inconclusive")));
    assert!(record.current_query_sha256.is_none());
    assert!(!record.solver_invoked);
    drop(scope);
    assert_eq!(
        format!("{:?}", original_owner.check()),
        "Some(Inconclusive)"
    );
    assert_eq!(owner(&original()).check(), None);
}
