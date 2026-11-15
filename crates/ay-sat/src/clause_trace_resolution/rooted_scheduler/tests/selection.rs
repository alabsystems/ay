// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn rooted_selection_bound_includes_escalation_census_equality_and_overflow() {
    assert!(size_of::<CandidateSchedule>() <= size_of::<Scheduler>() + size_of::<Vec<usize>>());
    let choose = super::super::selection::legacy_is_cheaper;
    // C=3, M=2, L=5, S=C+M+1: (M+2)*(C+M+L)+2M+1+S = 51.
    assert!(choose(3, 2, 5, 8, 6)); // Three dense head passes also cost 51.
    assert!(!choose(3, 2, 5, 8, 7));
    assert!(!choose(3, 2, 5, 7, 6));
    assert!(crate::clause_trace_resolution::ordinary_compaction::legacy_is_cheaper(3, 2, 5, 7, 6));
    for (c, m, l, v, s) in [
        (u128::MAX, 2, 5, 8, 6),
        (3, u128::MAX, 5, 8, 6),
        (3, 2, u128::MAX, 8, 6),
        (3, 2, 5, u128::MAX, 6),
        (3, 2, 5, 8, u128::MAX),
    ] {
        assert!(!choose(c, m, l, v, s));
    }
}

#[test]
fn rooted_selection_identifies_legacy_exhausted_and_indexed_states() {
    let clauses = originals();
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = root_for(&clauses, 1027);
    seed_rooted_target(&mut root, &[pos(0)], &mut meter).unwrap();
    // Exact post-first-pass state for candidates [3,2,1]: id1 propagated b.
    root.assign[1] = Some(true);
    root.cand_reason[1] = 1;
    root.row_trail.push(1);
    root.cand_order.push(1);
    let mut retired = rooted_retirement::RetiredCandidates::new(3, 3, &mut meter).unwrap();
    retired.mark(2, &mut meter).unwrap();
    let before = meter.consumed_work();
    assert!(matches!(
        CandidateSchedule::select(&root, &clauses, &[], &[3, 2, 1], &retired, 0, &mut meter)
            .unwrap(),
        Some(CandidateSchedule::Legacy)
    ));
    assert_eq!(meter.consumed_work() - before, 6);
    let mut retired = rooted_retirement::RetiredCandidates::new(1, 1, &mut meter).unwrap();
    retired.mark(0, &mut meter).unwrap();
    let before = meter.consumed_work();
    assert!(matches!(
        CandidateSchedule::select(&root, &clauses, &[], &[1], &retired, 0, &mut meter).unwrap(),
        Some(CandidateSchedule::Exhausted)
    ));
    assert_eq!(meter.consumed_work() - before, 2);
    let candidates = vec![3; 128];
    let retired = rooted_retirement::RetiredCandidates::new(128, 128, &mut meter).unwrap();
    assert!(matches!(
        CandidateSchedule::select(
            &root,
            &clauses,
            &[],
            &candidates,
            &retired,
            admission(1027, &clauses, &[], &candidates),
            &mut meter
        )
        .unwrap(),
        Some(CandidateSchedule::Indexed(_))
    ));
}

#[test]
fn exhausted_candidates_still_escalate_originals_after_root_filtering() {
    let clauses = vec![
        (1, vec![pos(4)]),
        (2, vec![pos(0), pos(4)]), // Root-satisfied; absent from the filtered CSR.
        (3, vec![pos(0), pos(1)]),
        (4, vec![neg(4), neg(1), pos(2)]),
        (5, vec![neg(2), pos(3)]),
        (6, vec![neg(2), neg(3)]),
        (7, vec![neg(0), pos(1)]),
    ];
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = root_for(&clauses, 5);
    assert!(!root.index_items.contains(&1));
    let mut derived = Vec::new();
    // Each first pass retires every candidate (one satisfied, one unit), but
    // neither candidate supplies the eventual original-clause conflict.
    for (target, candidates, expected) in [
        (pos(0), [2, 3], vec![1, 3, 4, 5, 6]),
        (neg(0), [2, 7], vec![1, 7, 4, 5, 6]),
        (pos(0), [2, 3], vec![1, 3, 4, 5, 6]),
    ] {
        let chain = compact_rup_hint_candidates_rooted(
            &mut root,
            &clauses,
            &[],
            &[target],
            &candidates,
            6,
            2,
            0,
            &mut meter,
        )
        .unwrap()
        .unwrap();
        assert_eq!(chain, expected);
        assert_eq!(root.assign, vec![None, None, None, None, Some(true)]);
        assert!(root.row_trail.is_empty());
        assert!(root.cand_order.is_empty());
        derived.push(RupStep {
            id: 8 + derived.len() as u64,
            clause: vec![target],
            rup_hints: chain,
        });
    }
    derived.push(RupStep {
        id: 11,
        clause: vec![],
        rup_hints: vec![8, 9],
    });
    let dag = ResolutionDag {
        num_vars: 5,
        original_clauses: clauses,
        derived,
        empty_clause_id: 11,
    };
    assert_eq!(dag.validate_with_limits(&limits), Ok(()));
    let mut corrupted = dag.clone();
    corrupted.derived[0].rup_hints.pop();
    assert!(corrupted.validate_with_limits(&limits).is_err());
}

#[test]
fn direct_scheduler_retains_explicit_dense_setup_cost() {
    let clauses = originals();
    let candidates = [3, 2, 1];
    let run = |num_vars| {
        let root = root_for(&clauses, num_vars);
        let limits = ResolutionValidationLimits::unbounded();
        let mut stop = || false;
        let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
        let retired = rooted_retirement::RetiredCandidates::new(3, 3, &mut meter).unwrap();
        let before = meter.consumed_work();
        assert!(Scheduler::new(
            &root,
            &clauses,
            &[],
            &candidates,
            &retired,
            admission(num_vars, &clauses, &[], &candidates),
            &mut meter
        )
        .unwrap()
        .is_some());
        meter.consumed_work() - before
    };
    assert_eq!(run(4096) - run(16), 6 * (4096 - 16));
}

#[test]
fn cheap_selected_rows_stop_at_every_poll_and_exact_work_limit() {
    let clauses = originals();
    for (candidates, expected) in [(vec![3, 2, 1], vec![1, 3, 2]), (vec![1], vec![1, 2, 3])] {
        let run = |stop_at: usize, work: u64| {
            let mut root = root_for(&clauses, 1027);
            let calls = Cell::new(0usize);
            let mut stop = || {
                calls.set(calls.get() + 1);
                calls.get() == stop_at
            };
            let mut limits = ResolutionValidationLimits::unbounded();
            limits.max_work = work;
            let result = (|| {
                let mut meter = ConversionMeter::new(&limits, &mut stop)?;
                let hints = compact_rup_hint_candidates_rooted(
                    &mut root,
                    &clauses,
                    &[],
                    &[pos(0)],
                    &candidates,
                    6,
                    candidates.len(),
                    0,
                    &mut meter,
                )?;
                assert_eq!(hints, Some(expected.clone()));
                Ok::<_, ResolutionValidationError>(meter.consumed_work())
            })();
            assert_clean(&root);
            (result, calls.get())
        };
        let (complete, polls) = run(usize::MAX, u64::MAX);
        let work = complete.unwrap();
        assert!(polls > 3);
        for stop_at in 1..=polls {
            let (result, calls) = run(stop_at, u64::MAX);
            assert_eq!(result, Err(ResolutionValidationError::Cancelled));
            assert_eq!(
                calls, stop_at,
                "observed stops cannot restart selection or a fallback"
            );
        }
        assert_eq!(run(usize::MAX, work).0, Ok(work));
        assert!(matches!(
            run(usize::MAX, work - 1).0,
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                ..
            })
        ));
    }
}
