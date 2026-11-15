// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn small_case(num_vars: usize) -> Case {
    Case {
        originals: vec![
            (1, vec![neg(0), pos(1)]),
            (2, vec![pos(0)]),
            (3, vec![neg(1)]),
        ],
        derived: vec![],
        candidates: vec![1, 2, 3],
        num_vars,
    }
}

fn indexed_case(num_vars: usize) -> (Case, Vec<u64>) {
    let (mut case, expected) = reverse_chains(32, 2);
    assert!(num_vars >= case.num_vars);
    case.num_vars = num_vars;
    let id = case.originals.len() as u64 + 1;
    case.originals.push((id, vec![neg(0)]));
    case.candidates.push(id);
    let mut hints = vec![id];
    hints.extend_from_slice(&expected[0]);
    (case, hints)
}

fn controlled(
    case: &Case,
    stop_at: usize,
    max_work: u64,
    scheduler_bytes: usize,
    deadline: Option<Instant>,
) -> (
    Result<(Option<Vec<u64>>, u64), ResolutionValidationError>,
    usize,
) {
    let owner = fresh_owner(case.num_vars);
    let calls = Cell::new(0);
    let mut stop = || {
        calls.set(calls.get() + 1);
        calls.get() == stop_at
    };
    let mut limits = ResolutionValidationLimits::unbounded();
    limits.max_work = max_work;
    limits.deadline = deadline;
    let result = (|| {
        let mut meter = ConversionMeter::new(&limits, &mut stop)?;
        let (hints, owner) = scheduled_row(case, owner, &[], &[], scheduler_bytes, &mut meter)?;
        assert_clean(&owner);
        Ok((hints, meter.consumed_work()))
    })();
    (result, calls.get())
}

#[test]
fn ordinary_cheap_rows_bypass_dense_setup_independently_of_namespace_size() {
    let small = small_case(16);
    let large = small_case(4096);
    let old_small = measured(&small, &[], Sweep::Legacy, u64::MAX).unwrap();
    let old_large = measured(&large, &[], Sweep::Legacy, u64::MAX).unwrap();
    let new_small = measured(&small, &[], Sweep::Scheduled, u64::MAX).unwrap();
    let new_large = measured(&large, &[], Sweep::Scheduled, u64::MAX).unwrap();
    assert_eq!(
        old_small, old_large,
        "row work excludes initial reusable scratch allocation"
    );
    assert_eq!(new_large.0, old_small.0);
    assert_eq!(new_small.0, old_small.0);
    assert_eq!(
        new_large, new_small,
        "the dense namespace is never initialized"
    );
    assert_eq!(
        new_large.1,
        old_large.1 + 5,
        "three flag visits, one live length, one choice"
    );
    assert_eq!(
        controlled(&large, usize::MAX, u64::MAX, 0, None).0.unwrap(),
        new_large
    );
    assert_eq!(
        admission(&large) - admission(&small),
        4 * (4096 - 16) * size_of::<usize>()
    );
}

#[test]
fn ordinary_every_transient_stop_and_exact_work_deadline_limits_are_terminal() {
    let (case, expected) = indexed_case(CONTROL_POLL_INTERVAL + 3);
    let bytes = admission(&case);
    let (complete, polls) = controlled(&case, usize::MAX, u64::MAX, bytes, None);
    let (hints, work) = complete.unwrap();
    assert_eq!(hints, Some(expected));
    assert!(
        matches!(
            controlled(&case, usize::MAX, u64::MAX, 0, None).0,
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                ..
            })
        ),
        "fixture must actually enter the indexed lane"
    );
    assert!(polls > 5);
    for stop_at in 1..=polls {
        let (result, calls) = controlled(&case, stop_at, u64::MAX, bytes, None);
        assert!(matches!(result, Err(ResolutionValidationError::Cancelled)));
        assert_eq!(
            calls, stop_at,
            "observed transient stop must not restart another lane"
        );
    }
    assert_eq!(
        controlled(&case, usize::MAX, work, bytes, None).0.unwrap(),
        (hints, work)
    );
    assert!(matches!(
        controlled(&case, usize::MAX, work - 1, bytes, None).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));
    let (expired, calls) = controlled(&case, usize::MAX, u64::MAX, bytes, Some(Instant::now()));
    assert!(matches!(
        expired,
        Err(ResolutionValidationError::DeadlineExceeded)
    ));
    assert_eq!(calls, 0, "absolute deadline refuses before caller polling");
}

#[test]
fn ordinary_scheduler_uses_its_exact_byte_slot_without_borrowing_scratch_or_slack() {
    let (case, expected) = indexed_case(64);
    let bytes = admission(&case);
    assert_eq!(
        controlled(&case, usize::MAX, u64::MAX, bytes, None)
            .0
            .unwrap()
            .0,
        Some(expected.clone())
    );
    assert!(matches!(
        controlled(&case, usize::MAX, u64::MAX, bytes - 1, None).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let owner = fresh_owner(case.num_vars);
    let count = case.candidates.len();
    let scratch_bytes = synthesis_scratch_bytes_from_capacities(0, count, count, count, 0).unwrap();
    assert!(matches!(
        compact_rup_hint_candidates(
            &case.originals,
            &[],
            &[],
            &[],
            &case.candidates,
            count,
            owner,
            scratch_bytes - 1,
            bytes,
            &mut meter,
        ),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
    let mut trace = ClauseTrace::new();
    for (id, clause) in &case.originals {
        trace.add_clause(*id, clause.clone(), true);
    }
    trace.add_clause_with_hints(
        case.originals.len() as u64 + 1,
        vec![],
        false,
        case.candidates.clone(),
    );
    let checked = validate_clause_trace_resolution(&trace, case.num_vars, &limits).unwrap();
    assert_eq!(checked.dag().derived[0].rup_hints, expected);
    assert_eq!(checked.dag().validate_with_limits(&limits), Ok(()));
    let mut no_memory = limits;
    no_memory.max_bytes = 0;
    assert!(matches!(
        validate_clause_trace_resolution(&trace, case.num_vars, &no_memory),
        Err(ClauseTraceResolutionError::InvalidResolutionDag(
            ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                ..
            }
        ))
    ));
}

#[test]
fn ordinary_index_rejects_out_of_range_literals_even_in_retired_raw_rows() {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let visible = Case {
        originals: vec![(1, vec![pos(3)])],
        derived: vec![],
        candidates: vec![1],
        num_vars: 3,
    };
    assert!(matches!(
        scheduled_row(&visible, fresh_owner(3), &[], &[], usize::MAX, &mut meter),
        Err(ResolutionValidationError::Invalid(
            ResolutionDagValidateError::VarOutOfRange { .. }
        ))
    ));
    let (mut hidden, _) = indexed_case(64);
    let id = hidden.originals.len() as u64 + 1;
    hidden.originals.push((id, vec![pos(63), pos(64)]));
    hidden.candidates.insert(0, id);
    // The first scan sees +63 and retires this row before its malformed tail.
    // Index construction is permitted to diagnose that tail, never to accept it.
    assert!(matches!(
        scheduled_row(
            &hidden,
            fresh_owner(64),
            &[],
            &[pos(63)],
            usize::MAX,
            &mut meter
        ),
        Err(ResolutionValidationError::Invalid(
            ResolutionDagValidateError::VarOutOfRange { .. }
        ))
    ));
}

#[test]
fn ordinary_scheduler_poll_unwind_drops_owner_and_next_conversion_is_clean() {
    let (case, expected) = indexed_case(CONTROL_POLL_INTERVAL + 3);
    let bytes = admission(&case);
    let (_, polls) = controlled(&case, usize::MAX, u64::MAX, bytes, None);
    // Exercise every boundary, including setup, index construction and cleanup.
    for stop_at in 1..=polls {
        let owner = fresh_owner(case.num_vars);
        let calls = Cell::new(0);
        let limits = ResolutionValidationLimits::unbounded();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut stop = || {
                calls.set(calls.get() + 1);
                assert_ne!(calls.get(), stop_at, "injected conversion stop panic");
                false
            };
            let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
            scheduled_row(&case, owner, &[], &[], bytes, &mut meter)
        }));
        assert!(result.is_err());
        assert_eq!(calls.get(), stop_at);
    }
    assert_eq!(
        controlled(&case, usize::MAX, u64::MAX, bytes, None)
            .0
            .unwrap()
            .0,
        Some(expected)
    );
}

#[test]
fn ordinary_selection_bound_includes_census_equality_and_overflow() {
    use ordinary_compaction::legacy_is_cheaper;
    // B=(1+1)*(3+1+2)+2+1=15; dense setup at V=3 costs at least21.
    assert!(legacy_is_cheaper(3, 1, 2, 3, 5));
    assert!(legacy_is_cheaper(3, 1, 2, 3, 6));
    assert!(!legacy_is_cheaper(3, 1, 2, 3, 7));
    assert!(!legacy_is_cheaper(3, 1, 2, 2, 5));
    for (candidates, remaining, literals, vars, overhead) in [
        (u128::MAX, 1, 2, 3, 5),
        (3, u128::MAX, 2, 3, 5),
        (3, 1, u128::MAX, 3, 5),
        (3, 1, 2, u128::MAX, 5),
        (3, 1, 2, 3, u128::MAX),
    ] {
        assert!(!legacy_is_cheaper(
            candidates, remaining, literals, vars, overhead
        ));
    }
}
