// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

#[test]
fn original_thousand_decision_stop_cadence_is_preserved_and_sticky() {
    let mut s = Solver::new(1001);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    s.initialize_watches();
    let owner = generous();
    attach(&mut s, &owner);
    let calls = AtomicUsize::new(0);
    let result = s.cdcl_loop_main_no_tla(
        || {
            calls.fetch_add(1, Ordering::SeqCst);
            true
        },
        None,
    );
    assert_eq!(result, SatResult::Unknown);
    assert_eq!(s.num_decisions, 1000);
    assert_eq!(s.cold.search_decisions, 1000);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(
        s.cold.last_unknown_reason,
        Some(SatUnknownReason::Interrupted)
    );
    refused(&s, &owner);
    let before = owner.usage().unwrap();
    assert_eq!(drive(&mut s), SatResult::Unknown);
    assert_eq!(owner.usage().unwrap(), before);
}

#[test]
fn every_short_work_and_storage_grant_stops_without_authority() {
    let mut baseline = unsat();
    let owner = generous();
    attach(&mut baseline, &owner);
    assert!(matches!(drive(&mut baseline), SatResult::Unsat(_)));
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > 0 && used.storage_admitted > 0);
    for work in 0..used.work_admitted {
        let mut s = unsat();
        let owner = test_owner(work, used.storage_admitted);
        attach(&mut s, &owner);
        assert_eq!(drive(&mut s), SatResult::Unknown, "work cut {work}");
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
        refused(&s, &owner);
        let before = owner.usage().unwrap();
        assert_eq!(drive(&mut s), SatResult::Unknown);
        assert_eq!(owner.usage().unwrap(), before);
    }
    for storage in 0..used.storage_admitted {
        let mut s = unsat();
        let owner = test_owner(used.work_admitted, storage);
        attach(&mut s, &owner);
        assert_eq!(drive(&mut s), SatResult::Unknown, "storage cut {storage}");
        assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
        refused(&s, &owner);
    }
}

#[test]
fn every_original_observer_cut_wins_including_terminal_publication() {
    let mut baseline = unsat();
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing(usize::MAX, &calls));
    assert!(matches!(drive(&mut baseline), SatResult::Unsat(_)));
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 10);
    for cut in 0..total {
        let mut s = unsat();
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing(cut, &calls);
        attach(&mut s, &owner);
        assert_eq!(drive(&mut s), SatResult::Unknown, "observer cut {cut}");
        assert_eq!(
            s.cold.last_unknown_reason,
            Some(SatUnknownReason::Interrupted)
        );
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        refused(&s, &owner);
        let before = owner.usage().unwrap();
        assert_eq!(drive(&mut s), SatResult::Unknown);
        assert_eq!(owner.usage().unwrap(), before);
    }
}

#[test]
fn selected_maintenance_refuses_before_mutation_without_switching_defaults() {
    for selected in 0..4 {
        let mut s = sat();
        match selected {
            0 => {
                s.cold.arena_compaction_pending = true;
            }
            1 => {
                s.cold.next_rephase = 0;
                s.cold.rephase_enabled = true;
            }
            2 => {
                s.num_conflicts = 1;
                s.cold.next_inprobe_conflict = 0;
            }
            _ => {
                s.num_conflicts = s.cold.restart_min_conflicts;
                s.conflicts_since_restart = 1;
            }
        }
        let why = match selected {
            0 => "selected arena compaction is not admitted",
            1 => {
                assert!(s.should_rephase());
                "selected rephase is not admitted"
            }
            2 => {
                assert!(s.inprocessing_gates_pass());
                "selected inprocessing round is not admitted"
            }
            _ => "selected restart schedule continuation is not admitted",
        };
        let before = (
            s.num_decisions,
            s.num_conflicts,
            s.cold.next_rephase,
            s.cold.next_inprobe_conflict,
            s.cold.arena_compaction_pending,
            s.cold.rephase_enabled,
        );
        let original = rows(&s);
        let owner = generous();
        attach(&mut s, &owner);
        assert_eq!(drive(&mut s), SatResult::Unknown);
        assert_eq!(
            owner.check(),
            Err(CountedAdmissionError::Original(
                ay_core::original_query::QueryError::Invalid(why).into()
            ))
        );
        assert_eq!(
            (
                s.num_decisions,
                s.num_conflicts,
                s.cold.next_rephase,
                s.cold.next_inprobe_conflict,
                s.cold.arena_compaction_pending,
                s.cold.rephase_enabled
            ),
            before
        );
        assert_eq!(rows(&s), original);
        assert!(s.trail.is_empty());
        refused(&s, &owner);
    }
}

#[test]
fn caller_resource_limit_is_sticky_after_real_conflict_not_a_new_budget() {
    let mut s = unsat();
    s.set_conflict_budget(Some(1));
    let owner = generous();
    attach(&mut s, &owner);
    assert_eq!(drive(&mut s), SatResult::Unknown);
    assert_eq!(s.num_conflicts, 1);
    assert!(s.num_decisions > 0);
    assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
    s.set_conflict_budget(None);
    let before = owner.usage().unwrap();
    assert_eq!(drive(&mut s), SatResult::Unknown);
    assert_eq!(owner.usage().unwrap(), before);
}

#[test]
fn already_expired_original_deadline_stops_before_decision_or_proof() {
    let mut s = unsat();
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        Some(ay_core::time::Instant::now()),
        Arc::new(|| false),
    )
    .unwrap();
    let original = rows(&s);
    attach(&mut s, &owner);
    assert_eq!(drive(&mut s), SatResult::Unknown);
    assert_eq!(
        s.cold.last_unknown_reason,
        Some(SatUnknownReason::DeadlineExceeded)
    );
    assert_eq!(s.num_decisions, 0);
    assert_eq!(rows(&s), original);
    refused(&s, &owner);
}
