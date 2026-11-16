// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn filtered_build_keeps_conservative_admission_and_terminal_stop_boundaries() {
    let originals = branches(512);
    let admitted = planned_bytes(
        5,
        originals.len(),
        originals.iter().map(|(_, c)| c.len()).sum(),
    )
    .unwrap();
    let run = |stop_at: usize, work: u64, bytes: usize| {
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = work;
        let mut root = empty_root(5);
        root.assign[0] = Some(true);
        root.assign[1] = Some(false);
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            build(&mut root, &originals, 5, bytes, &mut meter)?;
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        (result, calls.get(), root)
    };
    let (success, polls, root) = run(usize::MAX, u64::MAX, admitted);
    let work = success.unwrap();
    assert_eq!(root.index_items.len(), 8);
    assert!(polls > 3);
    assert_eq!(run(usize::MAX, work, admitted).0, Ok(work));
    for stop_at in 1..=polls {
        let (result, calls, root) = run(stop_at, u64::MAX, admitted);
        assert_eq!(result, Err(ResolutionValidationError::Cancelled));
        assert_eq!(calls, stop_at);
        assert!(root.index_heads.is_none());
        assert_eq!(root.index_items.len(), 0);
    }
    for (budget, bytes, resource) in [
        (work - 1, admitted, ResolutionValidationResource::Work),
        (u64::MAX, admitted - 1, ResolutionValidationResource::Bytes),
    ] {
        let (result, _, root) = run(usize::MAX, budget, bytes);
        assert!(
            matches!(result, Err(ResolutionValidationError::LimitExceeded { resource: actual, .. }) if actual == resource)
        );
        assert!(root.index_heads.is_none());
        assert_eq!(root.index_items.len(), 0);
    }
}

#[test]
fn filtered_build_rejects_invalid_indices_even_behind_a_true_root_literal() {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    for (assignment_vars, declared_vars, tail) in [(2, 2, pos(2)), (1, 2, pos(1)), (3, 2, pos(2))] {
        let mut root = empty_root(assignment_vars);
        root.assign[0] = Some(true);
        let result = build(
            &mut root,
            &[(1, vec![pos(0), tail])],
            declared_vars,
            usize::MAX,
            &mut meter,
        );
        assert!(matches!(
            result,
            Err(ResolutionValidationError::Invalid(
                ResolutionDagValidateError::VarOutOfRange { .. }
            ))
        ));
        assert!(root.index_heads.is_none());
        assert_eq!(root.index_items.len(), 0);
    }
}

#[test]
fn filtered_empty_index_and_expired_deadline_never_invent_occurrences() {
    let originals = vec![(1, vec![pos(0)]), (2, vec![pos(1), neg(1), pos(0)])];
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = empty_root(2);
    root.assign[0] = Some(true);
    let admitted = planned_bytes(2, 2, 4).unwrap();
    build(&mut root, &originals, 2, admitted, &mut meter).unwrap();
    assert_eq!(root.index_heads, Some(vec![0; 5]));
    assert_eq!(root.index_items.len(), 0);

    let mut expired = ResolutionValidationLimits::unbounded();
    expired.deadline = Some(Instant::now());
    let mut root = empty_root(2);
    root.assign[0] = Some(true);
    let result = (|| {
        let mut meter = ConversionMeter::new(&expired, &mut stop)?;
        build(&mut root, &originals, 2, admitted, &mut meter)
    })();
    assert_eq!(result, Err(ResolutionValidationError::DeadlineExceeded));
    assert!(root.index_heads.is_none());
    assert_eq!(root.index_items.len(), 0);
}
