// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn isolated_peak_accounts_pending_actual_capacities_and_overflow() {
    let capacities = [11, 16, 6, 6, 6, 11];
    let admitted = Scheduler::bytes(capacities).unwrap();
    assert_eq!(
        admitted,
        size_of::<Scheduler>()
            + size_of::<Vec<usize>>()
            + (11 + 16 + 6 + 6 + 11) * size_of::<usize>()
            + 6
    );
    for index in 0..6 {
        let mut grown = capacities;
        grown[index] += 1;
        assert!(Scheduler::check_capacities(grown, admitted).is_err());
    }
    assert!(Scheduler::planned_bytes(usize::MAX, 1, 1).is_err());
    assert!(Scheduler::planned_bytes(1, 1, usize::MAX).is_err());
    assert_eq!(Scheduler::planned_bytes(usize::MAX, 0, 0).unwrap(), 0);
    let clauses = originals();
    let root = root_for(&clauses, 5);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let retired = rooted_retirement::RetiredCandidates::new(6, 6, &mut meter).unwrap();
    let exact = admission(5, &clauses, &[], &[3, 2, 1, 6, 5, 4]);
    assert!(matches!(
        Scheduler::new(
            &root,
            &clauses,
            &[],
            &[3, 2, 1, 6, 5, 4],
            &retired,
            exact - 1,
            &mut meter
        ),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
    assert!(Scheduler::new(
        &root,
        &clauses,
        &[],
        &[3, 2, 1, 6, 5, 4],
        &retired,
        exact,
        &mut meter
    )
    .unwrap()
    .is_some());
}

#[test]
fn exact_census_counts_duplicate_positions_and_refinement_reselects_recorded_plan() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(40, vec![pos(0)], true);
    trace.add_clause(7, vec![neg(0)], true);
    trace.add_clause_with_hints(90, vec![], false, vec![40, 7, 40]);
    let entries = trace.entries();
    let mut limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let shape = preflight_trace_shape(&trace, entries, 5, 0, false, &mut meter).unwrap();
    let states = collect_entry_states(entries, &mut meter).unwrap();
    let structure =
        validate_entry_structure(&trace, entries, &[], &states, shape, &mut meter).unwrap();
    assert_eq!(structure.max_candidate_count, 3);
    assert_eq!(
        structure.max_candidate_literals, 3,
        "repeat original 40 counts twice"
    );

    let scheduler = Scheduler::planned_bytes(5, 3, 3).unwrap();
    let mut narrow = shape;
    narrow.hints = narrow.recorded_hints;
    narrow.max_row_hints = narrow.recorded_max_row_hints;
    narrow.row_hint_budget = 0;
    // A separate hypothetical widened width exercises the same chooser used
    // by real large traces; both candidate plans retain the exact row census.
    narrow.widened_hints = Some(9);
    let old = choose_trace_plan(narrow, Some(9), 3, 5, 3, 0, &limits).unwrap();
    assert_eq!(old.shape.hints, 9);
    let recorded = choose_trace_plan(narrow, None, 3, 5, 3, 0, &limits).unwrap();
    limits.max_bytes = recorded.conversion.max(recorded.replay) + scheduler;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let refined = admit_candidate_scheduler(old.shape, 3, 3, 3, 5, 0, &mut meter).unwrap();
    assert_eq!(refined.hints, 3);
    assert_eq!(refined.row_hint_budget, 0);
    assert_eq!(refined.widening_hint_slack, limits.max_hints - 3);
    assert_eq!(refined.widening_byte_slack, 0);
    let added = choose_trace_plan(refined, None, 3, 5, 3, 0, &limits).unwrap();
    assert_eq!(
        added.replay, recorded.replay,
        "scheduler never enters replay allowance"
    );
    assert_eq!(added.conversion, recorded.conversion + scheduler);
    limits.max_bytes -= 1;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    assert!(matches!(
        admit_candidate_scheduler(old.shape, 3, 3, 3, 5, 0, &mut meter),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
}

#[test]
fn bounded_heap_debits_and_no_growth_are_explicit() {
    let mut heap = Vec::new();
    heap.try_reserve_exact(4).unwrap();
    let capacity = heap.capacity();
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    for value in [3, 1, 2] {
        queue::push(&mut heap, value, 4, &mut meter).unwrap();
    }
    assert_eq!(meter.consumed_work(), 7);
    for value in [1, 2, 3] {
        assert_eq!(queue::pop(&mut heap, &mut meter).unwrap(), Some(value));
    }
    assert_eq!(queue::pop(&mut heap, &mut meter).unwrap(), None);
    assert_eq!(meter.consumed_work(), 19);
    assert_eq!(heap.capacity(), capacity);
    for value in 0..4 {
        queue::push(&mut heap, value, 4, &mut meter).unwrap();
    }
    assert!(queue::push(&mut heap, 4, 4, &mut meter).is_err());
    assert_eq!(heap.len(), 4);
    assert_eq!(heap.capacity(), capacity);
}

#[test]
fn every_transient_stop_and_tight_work_byte_deadline_refusal_clean_the_row() {
    let clauses = originals();
    // Distinct live positions, even when they repeat ids, make the conservative
    // legacy bound exceed dense setup. A tiny row now correctly bypasses it.
    let mut candidates = vec![3; 128];
    candidates.extend(vec![2; 128]);
    candidates.extend([1, 6, 5, 4]);
    // Enough variables to exercise chunk polls inside each dense allocation.
    let num_vars = CONTROL_POLL_INTERVAL + 3;
    let bytes = admission(num_vars, &clauses, &[], &candidates);
    let run = |stop_at: usize, max_work: u64, admitted: usize, expired: bool| {
        let mut root = root_for(&clauses, num_vars);
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = max_work;
        if expired {
            limits.deadline = Some(Instant::now());
        }
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
                admitted,
                &mut meter,
            )?;
            assert_eq!(hints, Some(vec![1, 3, 2]));
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        assert_clean(&root);
        (result, calls.get())
    };
    let (complete, polls) = run(usize::MAX, u64::MAX, bytes, false);
    let work = complete.unwrap();
    assert!(polls > 5);
    assert!(
        matches!(
            run(usize::MAX, u64::MAX, 0, false).0,
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                ..
            })
        ),
        "the resource fixture must actually enter indexed construction"
    );
    for stop in 1..=polls {
        let (result, calls) = run(stop, u64::MAX, bytes, false);
        assert!(matches!(result, Err(ResolutionValidationError::Cancelled)));
        assert_eq!(calls, stop, "no retry after a transient stop");
    }
    assert_eq!(run(usize::MAX, work, bytes, false).0.unwrap(), work);
    assert!(matches!(
        run(usize::MAX, work - 1, bytes, false).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));
    assert!(matches!(
        run(usize::MAX, u64::MAX, bytes - 1, false).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
    assert!(matches!(
        run(usize::MAX, u64::MAX, bytes, true).0,
        Err(ResolutionValidationError::DeadlineExceeded)
    ));
}
