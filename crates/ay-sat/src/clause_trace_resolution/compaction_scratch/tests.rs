// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::cell::Cell;

mod retirement;
mod scheduling;

fn pos(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}

fn neg(var: u32) -> Literal {
    Literal::negative(Variable::new(var))
}

fn scratch(num_vars: usize, meter: &mut ConversionMeter<'_>) -> CompactionScratch {
    CompactionScratch::new(
        num_vars,
        CompactionScratch::planned_bytes(num_vars).unwrap(),
        meter,
    )
    .expect("bounded scratch")
}

fn row(
    owner: CompactionScratch,
    originals: &[(u64, Vec<Literal>)],
    target: &[Literal],
    premises: &[Literal],
    candidates: &[u64],
    meter: &mut ConversionMeter<'_>,
) -> Result<(Option<Vec<u64>>, CompactionScratch), ResolutionValidationError> {
    let admitted = planned_synthesis_scratch_bytes(owner.assign.len(), candidates.len())?;
    compact_rup_hint_candidates(
        originals,
        &[],
        target,
        premises,
        candidates,
        candidates.len(),
        owner,
        admitted,
        usize::MAX, // Direct helper tests admit scheduler storage separately.
        meter,
    )
}

#[test]
fn reused_rows_preserve_exact_hint_order_and_clear_every_normal_exit() {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let originals = vec![
        (1, vec![neg(0), pos(1)]),
        (2, vec![pos(0)]),
        (3, vec![neg(1)]),
    ];
    let mut owner = scratch(8, &mut meter);
    // Open prefix is reconsidered, and each subsequent row needs a fresh
    // assignment even after a prior success, miss, tautology or seed conflict.
    let cases = [
        (vec![], vec![], vec![1, 2, 3], Some(vec![2, 3, 1])),
        (vec![], vec![], vec![2], None),
        (vec![], vec![], vec![3], None),
        (vec![pos(0), neg(0)], vec![], vec![], Some(vec![])),
        (vec![], vec![pos(2), neg(2)], vec![], Some(vec![])),
        (vec![pos(2)], vec![pos(2)], vec![], Some(vec![])),
        (vec![], vec![], vec![3], None),
        (
            vec![],
            vec![neg(2), neg(2)],
            vec![1, 2, 3],
            Some(vec![2, 3, 1]),
        ),
    ];
    for (target, premises, candidates, expected) in cases {
        let fresh = scratch(8, &mut meter);
        let (fresh_result, _) = row(
            fresh,
            &originals,
            &target,
            &premises,
            &candidates,
            &mut meter,
        )
        .unwrap();
        let (result, returned) = row(
            owner,
            &originals,
            &target,
            &premises,
            &candidates,
            &mut meter,
        )
        .unwrap();
        assert_eq!(result, expected);
        assert_eq!(result, fresh_result);
        assert!(returned.assign.iter().all(Option::is_none));
        assert_eq!(returned.touched.len(), 0);
        owner = returned;
    }
    // A stale x=true from an ordinary None must not forge conflict at ¬x.
    let units = vec![(1, vec![pos(0)]), (2, vec![neg(0)])];
    let (first, owner) = row(owner, &units, &[], &[], &[1], &mut meter).unwrap();
    let (second, _) = row(owner, &units, &[], &[], &[2], &mut meter).unwrap();
    assert_eq!((first, second), (None, None));
}

#[test]
fn sparse_reuse_saves_only_repeated_namespace_initialization() {
    const VARS: usize = 4096;
    const ROWS: usize = 32;
    let limits = ResolutionValidationLimits::unbounded();
    let originals = vec![(1, vec![pos(0)]), (2, vec![neg(0)])];
    let run = |reuse: bool| {
        let mut stop = || false;
        let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
        let mut retained = None;
        for _ in 0..ROWS {
            let owner = retained.take().unwrap_or_else(|| scratch(VARS, &mut meter));
            let (hints, owner) = row(owner, &originals, &[], &[], &[1, 2], &mut meter).unwrap();
            assert_eq!(hints, Some(vec![1, 2]));
            if reuse {
                retained = Some(owner);
            }
        }
        meter.consumed_work()
    };
    assert_eq!(run(false) - run(true), ((ROWS - 1) * VARS) as u64);
}

#[test]
fn conversion_reuse_still_independently_replays_every_row() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![pos(0)], true);
    trace.add_clause(2, vec![neg(0)], true);
    for id in 3..35 {
        trace.add_clause_with_hints(id, vec![pos(1)], false, vec![1, 2]);
    }
    trace.add_clause_with_hints(35, vec![], false, vec![1, 2]);
    let mut limits = ResolutionValidationLimits::unbounded();
    let valid = validate_clause_trace_resolution(&trace, 4096, &limits).unwrap();
    assert_eq!(valid.dag().derived.len(), 33);
    for step in &valid.dag().derived {
        assert_eq!(step.rup_hints, vec![1, 2]);
    }
    assert_eq!(valid.dag().validate_with_limits(&limits), Ok(()));
    // A tight allowance admits the new conversion plus final replay, not 33
    // repeated 4096-slot initializations. No production limit is enlarged.
    assert!(valid.validation_work() < 32 * 4096);
    limits.max_work = valid.validation_work() - 1;
    assert!(matches!(
        validate_clause_trace_resolution(&trace, 4096, &limits),
        Err(ClauseTraceResolutionError::InvalidResolutionDag(
            ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                ..
            }
        ))
    ));
    // The independently checked DAG cannot accept removal of its conflicting
    // hints even though the conversion scratch has already been destroyed.
    let mut bad = valid.dag().clone();
    bad.derived.last_mut().unwrap().rup_hints = vec![1];
    assert!(bad
        .validate_with_limits(&ResolutionValidationLimits::unbounded())
        .is_err());
}

#[test]
fn malformed_rows_and_restricted_subsetup_work_refusal_do_not_return_an_owner() {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let owner = scratch(2, &mut meter);
    let malformed = vec![(1, vec![pos(2)])];
    assert!(matches!(
        row(owner, &malformed, &[pos(0)], &[], &[1], &mut meter),
        Err(ResolutionValidationError::Invalid(
            ResolutionDagValidateError::VarOutOfRange { .. }
        ))
    ));
    let owner = scratch(2, &mut meter);
    let (missing, owner) = row(owner, &[], &[pos(0)], &[], &[99], &mut meter).unwrap();
    assert_eq!(missing, None);
    assert!(owner.assign.iter().all(Option::is_none));
    let before = meter.consumed_work();
    let (result, _) = row(owner, &[], &[pos(0), neg(0)], &[], &[], &mut meter).unwrap();
    assert_eq!(result, Some(vec![]));
    let row_work = meter.consumed_work() - before;
    let mut tight = limits.clone();
    // The last work unit is sparse cleanup; rejecting it must not yield a
    // reusable owner or turn the resource error into a repair fallback.
    tight.max_work = row_work - 1;
    let mut stop = || false;
    let mut tight_meter = ConversionMeter::new(&tight, &mut stop).unwrap();
    let owner = scratch(2, &mut meter);
    assert!(matches!(
        row(owner, &[], &[pos(0), neg(0)], &[], &[], &mut tight_meter),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));
}

#[test]
fn cancellation_and_unwind_drop_partial_scratch_without_rearming() {
    let limits = ResolutionValidationLimits::unbounded();
    let run = |stop_at: usize| {
        let calls = Cell::new(0usize);
        let mut stop = || {
            let n = calls.get() + 1;
            calls.set(n);
            n == stop_at
        };
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            let owner =
                CompactionScratch::new(2048, CompactionScratch::planned_bytes(2048)?, &mut meter)?;
            row(owner, &[], &[pos(0), neg(0)], &[], &[], &mut meter)
        })();
        (result, calls.get())
    };
    let (success, polls) = run(usize::MAX);
    assert!(success.is_ok());
    for stop_at in 1..=polls {
        let (result, calls) = run(stop_at);
        assert!(matches!(result, Err(ResolutionValidationError::Cancelled)));
        assert_eq!(
            calls, stop_at,
            "a recovered callback must not rearm conversion"
        );
    }
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![pos(0)], true);
    trace.add_clause(2, vec![neg(0)], true);
    trace.add_clause_with_hints(3, vec![], false, vec![1, 2]);
    let mut stop = || false;
    let mut preparation_meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let owner = scratch(2048, &mut preparation_meter);
    let targets: Vec<_> = (0..1024).map(pos).collect();
    let calls = Cell::new(0usize);
    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut stop = || {
            let n = calls.get() + 1;
            calls.set(n);
            // Meter entry, row entry, then the first charged 1024-work
            // boundary while the target is only partially seeded.
            assert_ne!(n, 3, "injected callback panic");
            false
        };
        let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
        row(owner, &[], &targets, &[], &[], &mut meter)
    }));
    assert!(unwind.is_err());
    assert_eq!(calls.get(), 3);
    assert!(validate_clause_trace_resolution(&trace, 2048, &limits).is_ok());
}

#[test]
fn scratch_bytes_are_additive_to_all_conversion_lanes() {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let bytes = CompactionScratch::planned_bytes(4).unwrap();
    assert!(matches!(
        CompactionScratch::new(4, bytes - 1, &mut meter),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
    let grown = CompactionScratch::bytes(5, 4).unwrap();
    assert!(grown > bytes);
    assert!(enforce_resource(ResolutionValidationResource::Bytes, grown, bytes).is_err());
    let shape = TraceShape {
        original_clauses: 2,
        original_literals: 2,
        derived_steps: 1,
        max_row_hints: 2,
        hints: 2,
        ..TraceShape::default()
    };
    let peaks = planned_trace_peaks(shape, 4, 5, 0, 0, 0).unwrap();
    assert_eq!(peaks.shape.compaction_scratch_bytes, bytes);
    let retained = planned_retained_bytes(peaks.shape, 0).unwrap();
    assert_eq!(
        peaks.conversion,
        retained
            + peaks.shape.synthesis_scratch_bytes
            + bytes
            + peaks.shape.root_index_scratch_bytes
    );
    assert_eq!(
        peaks.replay, retained,
        "conversion owner is not retained into replay"
    );
    assert!(enforce_resource(
        ResolutionValidationResource::Bytes,
        peaks.conversion,
        peaks.conversion - 1
    )
    .is_err());
}

#[test]
fn scratch_coexists_with_rooted_full_and_terminal_repair() {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let originals = vec![
        (1, vec![pos(0)]),
        (2, vec![neg(0), pos(1)]),
        (3, vec![neg(1)]),
    ];
    let owner = scratch(3, &mut meter);
    let (miss, owner) = row(owner, &originals, &[pos(1)], &[], &[2], &mut meter).unwrap();
    assert_eq!(miss, None);
    let mut root = compute_root_propagation(
        &originals,
        &[],
        3,
        root_occurrence_index::planned_bytes(3, 3, 4).unwrap(),
        &mut meter,
    )
    .unwrap();
    // Negating y conflicts with a root-implied (not fixed-premise) value;
    // this is the existing explicit full-synthesis fallback boundary.
    assert_eq!(
        compact_rup_hint_candidates_rooted(
            &mut root,
            &originals,
            &[],
            &[pos(1)],
            &[2],
            4,
            4,
            usize::MAX, // Direct helper test: unbounded scheduler allowance.
            &mut meter
        )
        .unwrap(),
        None
    );
    assert_eq!(
        synthesize_rup_hints(
            &originals,
            &[],
            &[pos(1)],
            &[],
            3,
            4,
            1,
            planned_synthesis_scratch_bytes(3, 4).unwrap(),
            &mut meter
        )
        .unwrap(),
        Some(vec![1, 2])
    );
    assert_eq!(owner.assign.len(), 3);
    assert!(owner.assign.iter().all(Option::is_none));

    let mut trace = ClauseTrace::new();
    for (id, clause) in originals {
        trace.add_clause(id, clause, true);
    }
    trace.add_clause_with_hints(4, vec![pos(1)], false, vec![2]);
    trace.mark_empty();
    let checked = validate_clause_trace_resolution_with_unit_premises_interruptible(
        &trace,
        3,
        &[neg(2)],
        &limits,
        || false,
    )
    .unwrap();
    assert_eq!(checked.dag().derived.len(), 2);
    assert_eq!(checked.dag().derived[0].rup_hints, vec![1, 2]);
    assert_eq!(checked.dag().derived.last().unwrap().clause.len(), 0);
}
