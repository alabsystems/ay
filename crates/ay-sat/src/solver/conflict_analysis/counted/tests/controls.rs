// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn exact_and_one_short_work_storage_cover_actual_finalization_and_retirement() {
    let (mut baseline, reference, _) = fixture(1, Reasons::Long);
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut baseline, &owner);
    let expected = run(&mut baseline, reference).unwrap();
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > 100 && used.storage_admitted > 0);
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
        let (mut s, reference, _) = fixture(1, Reasons::Long);
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
fn every_short_work_cut_retires_actual_standard_scratch_without_publishing() {
    let (mut baseline, reference, _) = fixture(1, Reasons::Binary);
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut baseline, &owner);
    assert!(run(&mut baseline, reference).unwrap().is_some());
    let total = owner.usage().unwrap().work_admitted;
    assert!(total > 100);
    for work in 0..total {
        let (mut s, reference, _) = fixture(1, Reasons::Binary);
        let before = clauses(&s);
        let trace = format!("{:?}", s.clause_trace());
        let owner = test_owner(work, 100_000_000);
        attach(&mut s, &owner);
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget),
            "cut {work}"
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
        assert_eq!(clauses(&s), before);
        assert_eq!(format!("{:?}", s.clause_trace()), trace);
        clean(&s);
    }
}

#[test]
fn every_short_storage_cut_retires_the_actual_traced_chain_and_learned_result() {
    let (mut baseline, reference, _) = fixture(1, Reasons::Long);
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut baseline, &owner);
    assert!(run(&mut baseline, reference).unwrap().is_some());
    let total = owner.usage().unwrap().storage_admitted;
    assert!(
        total > 32,
        "must allocate real chain, scratch and result storage"
    );
    for storage in 0..total {
        let (mut s, reference, _) = fixture(1, Reasons::Long);
        let trace = format!("{:?}", s.clause_trace());
        let owner = test_owner(100_000_000, storage);
        attach(&mut s, &owner);
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget),
            "storage {storage}"
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
        assert_eq!(format!("{:?}", s.clause_trace()), trace);
        clean(&s);
    }
}

#[test]
fn every_observer_cut_including_finish_is_sticky_and_retires_actual_scratch() {
    let (mut baseline, reference, _) = fixture(1, Reasons::Long);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    assert!(run(&mut baseline, reference).unwrap().is_some());
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 20);
    for cut in 0..total {
        let (mut s, reference, _) = fixture(1, Reasons::Long);
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

#[test]
fn completed_result_stays_private_when_original_cancellation_arrives_at_finish() {
    let (mut s, reference, _) = fixture(2, Reasons::Long);
    let cancel = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&cancel);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 100_000_000),
        None,
        Arc::new(move || observed.load(Ordering::SeqCst)),
    )
    .unwrap();
    attach(&mut s, &owner);
    let scope = s
        .begin_counted_standard_analysis(reference)
        .unwrap()
        .unwrap();
    assert_ne!(scope.learned_clause().len(), 0);
    cancel.store(true, Ordering::SeqCst);
    assert_eq!(scope.finish(), Err(SatUnknownReason::Interrupted));
    cancel.store(false, Ordering::SeqCst);
    assert_eq!(run(&mut s, reference), Err(SatUnknownReason::Interrupted));
    clean(&s);
}

#[test]
fn preexisting_ordinary_scratch_is_refused_not_silently_discarded() {
    let (mut s, reference, _) = fixture(1, Reasons::Long);
    assert!(ordinary(&mut s, reference).is_some());
    let before = format!("{:?}", s.conflict);
    let vars = s.var_data.clone();
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    assert_eq!(
        run(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(format!("{:?}", s.conflict), before);
    assert_eq!(s.var_data, vars);
}

#[test]
fn original_owner_is_never_renewed_by_a_second_completed_scope() {
    let (mut s, reference, _) = fixture(2, Reasons::Binary);
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    let expected = run(&mut s, reference).unwrap();
    let first = owner.usage().unwrap();
    assert_eq!(run(&mut s, reference).unwrap(), expected);
    let second = owner.usage().unwrap();
    assert!(second.work_admitted > first.work_admitted);
    assert!(second.work_remaining < first.work_remaining);
    clean(&s);
}

#[test]
fn sampled_relevance_prepays_each_decision_in_both_modes() {
    for stable in [false, true] {
        let mut observed = Vec::new();
        for num_conflicts in [1023, 1024] {
            let (mut s, reference, _) = fixture(1, Reasons::Binary);
            s.stable_mode = stable;
            s.num_conflicts = num_conflicts;
            s.target_phase[0] = 1;
            s.target_phase[1] = -1;
            let level = s.decision_level;
            let trail_len = s.trail.len() as u64;
            let owner = test_owner(100_000_000, 100_000_000);
            attach(&mut s, &owner);
            let result = run(&mut s, reference).unwrap();
            let usage = owner.usage().unwrap();
            let totals = s.sampled_decision_relevance();
            let sources = s.sampled_decision_sources();
            let composition = s.sampled_trail_composition();
            clean(&s);
            observed.push((
                result,
                usage,
                level,
                totals,
                sources,
                trail_len,
                composition,
            ));
        }
        assert_eq!(observed[0].0, observed[1].0);
        assert!(observed[0].0.is_some());
        assert_eq!(observed[0].2, observed[1].2);
        assert_eq!(observed[0].3, ((0, 0, 0), (0, 0, 0)));
        assert_eq!(observed[0].4, ((0, 0, 0, 0), (0, 0, 0, 0)));
        assert_eq!(observed[0].5, observed[1].5);
        assert_eq!(observed[0].6, ((0, 0, 0), (0, 0, 0)));
        let (_, usage, level, totals, sources, trail_len, composition) = &observed[1];
        let (active, inactive, split, other_split) = if stable {
            (totals.1, totals.0, sources.1, sources.0)
        } else {
            (totals.0, totals.1, sources.0, sources.1)
        };
        assert_eq!(active.0, 1);
        assert_eq!(active.1, u64::from(*level));
        assert!(active.2 > 0 && active.2 <= active.1);
        assert_eq!(inactive, (0, 0, 0));
        assert_eq!(other_split, (0, 0, 0, 0));
        assert_eq!(split.0 + split.2, active.1);
        assert_eq!(split.1 + split.3, active.2);
        assert!(split.1 <= split.0 && split.3 <= split.2);
        let (trail, other_trail) = if stable {
            (composition.1, composition.0)
        } else {
            (composition.0, composition.1)
        };
        assert_eq!(trail, (*trail_len, 2, 1));
        assert_eq!(other_trail, (0, 0, 0));
        // This fixed cost catches an uncharged scan even when dynamic
        // exact-budget tests would simply discover a smaller wrong budget.
        assert_eq!(
            usage.work_admitted - observed[0].1.work_admitted,
            u64::from(*level) + *trail_len + 11,
        );
        assert_eq!(usage.storage_admitted, observed[0].1.storage_admitted);
        for short in [false, true] {
            let (mut s, reference, _) = fixture(1, Reasons::Binary);
            s.stable_mode = stable;
            s.num_conflicts = 1024;
            s.target_phase[0] = 1;
            s.target_phase[1] = -1;
            let owner = test_owner(
                usage.work_admitted - u64::from(short),
                usage.storage_admitted,
            );
            attach(&mut s, &owner);
            let result = run(&mut s, reference);
            if short {
                assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
                assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
                let frozen = owner.usage().unwrap();
                assert_eq!(run(&mut s, reference), result);
                assert_eq!(owner.usage().unwrap(), frozen);
            } else {
                assert_eq!(result, Ok(observed[1].0.clone()));
                assert_eq!(owner.usage().unwrap().work_remaining, 0);
                assert_eq!(owner.usage().unwrap().storage_remaining, 0);
            }
            clean(&s);
        }
    }
}

#[test]
fn sampled_analyzed_refusal_preserves_a_complete_measurement_batch() {
    for stable in [false, true] {
        let (mut baseline, reference, _) = fixture(1, Reasons::Binary);
        baseline.stable_mode = stable;
        baseline.num_conflicts = 1024;
        baseline.target_phase[0] = 1;
        baseline.target_phase[1] = -1;
        let trail_len = baseline.trail.len() as u64;
        let owner = test_owner(100_000_000, 100_000_000);
        attach(&mut baseline, &owner);
        assert!(run(&mut baseline, reference).unwrap().is_some());
        let expected = (
            baseline.sampled_decision_relevance(),
            baseline.sampled_decision_sources(),
            baseline.sampled_analyzed(),
            baseline.sampled_trail_composition(),
        );
        let (active, analyzed, trail, other_trail) = if stable {
            (expected.0 .1, expected.2 .1, expected.3 .1, expected.3 .0)
        } else {
            (expected.0 .0, expected.2 .0, expected.3 .0, expected.3 .1)
        };
        assert!(active.2 > 0 && analyzed >= active.2);
        assert_eq!(trail, (trail_len, 2, 1));
        assert_eq!(other_trail, (0, 0, 0));
        let empty = (
            ((0, 0, 0), (0, 0, 0)),
            ((0, 0, 0, 0), (0, 0, 0, 0)),
            (0, 0),
            ((0, 0, 0), (0, 0, 0)),
        );
        clean(&baseline);
        for work in 0..owner.usage().unwrap().work_admitted {
            let (mut s, reference, _) = fixture(1, Reasons::Binary);
            s.stable_mode = stable;
            s.num_conflicts = 1024;
            s.target_phase[0] = 1;
            s.target_phase[1] = -1;
            let owner = test_owner(work, 100_000_000);
            attach(&mut s, &owner);
            assert_eq!(
                run(&mut s, reference),
                Err(SatUnknownReason::ResourceBudget)
            );
            assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
            let actual = (
                s.sampled_decision_relevance(),
                s.sampled_decision_sources(),
                s.sampled_analyzed(),
                s.sampled_trail_composition(),
            );
            assert!(
                actual == empty || actual == expected,
                "work cut {work}, stable {stable}: partial measurement {actual:?}"
            );
            clean(&s);
        }
    }
}
