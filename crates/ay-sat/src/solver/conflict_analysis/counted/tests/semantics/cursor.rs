// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod unwind;

fn stale_fixture() -> (Solver, ClauseRef) {
    let (mut s, reference, _) = fixture(1, Reasons::Binary);
    s.var_data[2].trail_pos = u32::MAX;
    (s, reference)
}

fn nonchrono_fixture(stale: bool) -> (Solver, ClauseRef) {
    let (mut s, source) = fork_formula(3, Reasons::Binary);
    s.chrono_enabled = false; // Selected before actual BCP, never inside analysis.
    for clause in source {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    for var in [0, 1] {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
    }
    s.decide(pos(2));
    let reference = s.search_propagate().unwrap();
    assert_eq!(s.stats.jumped_reasons, 4);
    if stale {
        s.var_data[2].trail_pos = u32::MAX;
    }
    (s, reference)
}

#[test]
fn nonchronological_real_bcp_keeps_fast_path_and_repaired_uip_parity() {
    let (mut baseline, reference) = nonchrono_fixture(false);
    let expected = ordinary(&mut baseline, reference).unwrap();
    assert_eq!(expected.clause, [neg(2), neg(1), neg(0)]);
    for stale in [false, true] {
        let (mut uncounted, reference) = nonchrono_fixture(stale);
        assert_eq!(ordinary(&mut uncounted, reference), Some(expected.clone()));
        let (mut s, reference) = nonchrono_fixture(stale);
        attach(&mut s, &test_owner(100_000_000, 100_000_000));
        assert_eq!(run(&mut s, reference), Ok(Some(expected.clone())));
        assert_eq!(s.search_ticks, baseline.search_ticks);
        assert_eq!(s.stats.trail_exhaustion_bailouts, 0);
        assert!(!s.chrono_enabled);
        clean(&s);
    }
}

#[test]
fn stale_position_fallback_debits_each_actual_trail_observation() {
    let (mut ordinary_metadata, reference, _) = fixture(1, Reasons::Binary);
    let normal_owner = test_owner(100_000_000, 100_000_000);
    attach(&mut ordinary_metadata, &normal_owner);
    let expected = run(&mut ordinary_metadata, reference).unwrap();
    let normal = normal_owner.usage().unwrap();
    let (mut repaired, reference) = stale_fixture();
    let trail_len = repaired.trail.len();
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut repaired, &owner);
    assert_eq!(run(&mut repaired, reference), Ok(expected));
    let used = owner.usage().unwrap();
    assert_eq!(used.work_admitted, normal.work_admitted + trail_len as u64);
    assert_eq!(used.storage_admitted, normal.storage_admitted);
    assert_eq!(repaired.search_ticks, ordinary_metadata.search_ticks);
    clean(&repaired);
}

#[test]
fn stale_fallback_exact_and_short_original_work_storage_preserve_custody() {
    let (mut baseline, reference) = stale_fixture();
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut baseline, &owner);
    let expected = run(&mut baseline, reference).unwrap();
    let used = owner.usage().unwrap();
    assert!(expected.is_some() && used.storage_admitted > 0 && used.work_admitted > 100);
    for (work, storage, refusal) in [
        (used.work_admitted, used.storage_admitted, None),
        (
            used.work_admitted - 1,
            used.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            used.work_admitted,
            used.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let (mut s, reference) = stale_fixture();
        let owner = test_owner(work, storage);
        attach(&mut s, &owner);
        let actual = run(&mut s, reference);
        if let Some(error) = refusal {
            assert_eq!(actual, Err(SatUnknownReason::ResourceBudget));
            assert_eq!(owner.check(), Err(error));
            let frozen = owner.usage().unwrap();
            assert_eq!(run(&mut s, reference), actual);
            assert_eq!(owner.usage().unwrap(), frozen);
        } else {
            assert_eq!(actual, Ok(expected.clone()));
            assert_eq!(owner.usage().unwrap().work_remaining, 0);
            assert_eq!(owner.usage().unwrap().storage_remaining, 0);
        }
        clean(&s);
    }
}

#[test]
fn every_stale_cursor_work_cut_retires_without_a_learned_consequence() {
    let (mut baseline, reference) = stale_fixture();
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut baseline, &owner);
    assert!(run(&mut baseline, reference).unwrap().is_some());
    let total = owner.usage().unwrap().work_admitted;
    assert!(total > 100);
    for work in 0..total {
        let (mut s, reference) = stale_fixture();
        let original = clauses(&s);
        let owner = test_owner(work, 100_000_000);
        attach(&mut s, &owner);
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget),
            "cut {work}"
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
        let frozen = owner.usage().unwrap();
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.usage().unwrap(), frozen);
        assert_eq!(clauses(&s), original);
        clean(&s);
    }
}

#[test]
fn every_stale_cursor_observer_cut_is_sticky_including_actual_reverse_scan() {
    let (mut baseline, reference) = stale_fixture();
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    assert!(run(&mut baseline, reference).unwrap().is_some());
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 20);
    for cut in 0..total {
        let (mut s, reference) = stale_fixture();
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing_owner(cut, &calls);
        attach(&mut s, &owner);
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::Interrupted),
            "poll {cut}"
        );
        let frozen = owner.usage().unwrap();
        assert_eq!(run(&mut s, reference), Err(SatUnknownReason::Interrupted));
        assert_eq!(owner.usage().unwrap(), frozen);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        clean(&s);
    }
}

#[derive(Clone, Copy)]
enum InvalidTrail {
    Missing,
    WrongSign,
    Duplicate,
    ForwardReason,
}

fn invalid_fixture(kind: InvalidTrail) -> (Solver, ClauseRef) {
    let (mut s, reference, _) = fixture(3, Reasons::Binary);
    let actual = s.var_data[2].trail_pos as usize;
    assert_eq!(s.trail[actual], pos(2));
    match kind {
        InvalidTrail::Missing => s.trail[actual] = pos(0),
        InvalidTrail::WrongSign => s.trail[actual] = neg(2),
        InvalidTrail::Duplicate => {
            let duplicate = s.var_data[3].trail_pos as usize;
            assert_ne!(duplicate, actual);
            s.trail[duplicate] = pos(2);
        }
        InvalidTrail::ForwardReason => {
            let last = s.trail.len() - 1;
            let other = s.trail[last].variable().index();
            assert_ne!(other, 2);
            s.trail.swap(actual, last);
            s.var_data[other].trail_pos = actual as u32;
            s.var_data[2].trail_pos = last as u32;
            // Both metadata entries are exact; the discovered support is
            // genuinely later than the endpoint that will be resolved first.
            assert_eq!(s.trail[s.var_data[2].trail_pos as usize], pos(2));
            return (s, reference);
        }
    }
    s.var_data[2].trail_pos = u32::MAX;
    (s, reference)
}

#[test]
fn exact_live_forward_reason_cannot_reopen_the_resolved_trail_suffix() {
    let (mut expected, reference) = invalid_fixture(InvalidTrail::ForwardReason);
    assert!(ordinary(&mut expected, reference).is_none());
    let (mut s, reference) = invalid_fixture(InvalidTrail::ForwardReason);
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    assert_eq!(run(&mut s, reference), Ok(None));
    assert_eq!(owner.check(), Ok(()));
    assert_eq!(s.stats.trail_exhaustion_bailouts, 1);
    assert_eq!(s.search_ticks, expected.search_ticks);
    clean(&s);
}

#[test]
fn missing_wrong_signed_or_duplicate_fallback_assignment_never_learns() {
    for kind in [
        InvalidTrail::Missing,
        InvalidTrail::WrongSign,
        InvalidTrail::Duplicate,
    ] {
        let (mut expected, reference) = invalid_fixture(kind);
        assert!(ordinary(&mut expected, reference).is_none());
        let (mut s, reference) = invalid_fixture(kind);
        let original = clauses(&s);
        let owner = test_owner(100_000_000, 100_000_000);
        attach(&mut s, &owner);
        assert_eq!(run(&mut s, reference), Ok(None));
        assert_eq!(owner.check(), Ok(()));
        assert_eq!(s.stats.trail_exhaustion_bailouts, 1);
        assert_eq!(s.search_ticks, expected.search_ticks);
        assert_eq!(clauses(&s), original);
        clean(&s);
    }
}

fn negative_fixture() -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    let (mut s, mut source) = fork_formula(2, Reasons::Binary);
    for clause in &mut source {
        for lit in clause.iter_mut() {
            if lit.variable().index() == 2 {
                *lit = lit.negated();
            }
        }
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    for lit in [pos(0), pos(1)] {
        s.decide(lit);
        assert!(s.search_propagate().is_none());
    }
    s.decide(neg(2));
    let conflict = s.search_propagate().unwrap();
    assert_eq!(s.trail[s.var_data[2].trail_pos as usize], neg(2));
    (s, conflict, source)
}

#[test]
fn negative_assigned_uip_is_recovered_from_its_actual_signed_trail_entry() {
    let (mut expected, reference, _) = negative_fixture();
    let expected = ordinary(&mut expected, reference).unwrap();
    assert_eq!(expected.clause[0], pos(2));
    let (mut s, reference, source) = negative_fixture();
    s.var_data[2].trail_pos = u32::MAX;
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    let actual = run(&mut s, reference).unwrap().unwrap();
    assert_eq!(actual, expected);
    let mut models = 0;
    for bits in 0..1usize << s.num_vars {
        if source.iter().all(|clause| satisfies(clause, bits)) {
            models += 1;
            assert!(satisfies(&actual.clause, bits));
        }
    }
    assert!(models > 0);
    clean(&s);
}

#[cfg(all(feature = "jit", target_arch = "aarch64"))]
#[test]
fn native_and_scalar_stale_positions_share_signed_repair_and_correct_uip() {
    let (mut expected, reference, _) = fixture(3, Reasons::Binary);
    let expected = ordinary(&mut expected, reference).unwrap();
    for counted in [false, true] {
        let (mut s, reference, _) = fixture(3, Reasons::Binary);
        s.var_data[2].trail_pos = u32::MAX; // scalar binary-reason bookkeeping
        s.var_data[5].trail_pos = s.var_data[8].trail_pos; // native new-seen bookkeeping
        s.compile_conflict_processor();
        assert!(s.standard_native_available());
        let actual = if counted {
            attach(&mut s, &test_owner(100_000_000, 100_000_000));
            run(&mut s, reference).unwrap()
        } else {
            ordinary(&mut s, reference)
        };
        assert_eq!(actual, Some(expected.clone()));
        assert_eq!(s.stats.sat_conflict_analysis_native_applications, 3);
        assert_eq!(s.stats.trail_exhaustion_bailouts, 0);
        if counted {
            clean(&s);
        }
    }
}
