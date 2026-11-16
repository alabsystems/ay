// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;
use std::cell::Cell;

mod retirement;
mod root_filter;

fn pos(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}

fn neg(var: u32) -> Literal {
    Literal::negative(Variable::new(var))
}

fn empty_root(num_vars: usize) -> RootPropagation {
    RootPropagation {
        assign: vec![None; num_vars],
        reason: Vec::new(),
        order_pos: Vec::new(),
        conflict: None,
        premises_conflict: false,
        cand_reason: Vec::new(),
        row_trail: Vec::new(),
        cand_order: Vec::new(),
        cone_mark: Vec::new(),
        cone_vars: Vec::new(),
        cone_stack: Vec::new(),
        index_heads: None,
        index_items: Vec::new(),
        index_retired: rooted_retirement::RetiredOriginals::default(),
    }
}

#[test]
fn occurrence_bytes_grow_with_literals_and_are_conversion_only() {
    let sparse = planned_bytes(2, 1, 2).unwrap();
    let dense = planned_bytes(2, 100, 200).unwrap();
    assert_eq!(dense - sparse, 198 * size_of::<u32>());
    assert_eq!(
        dense,
        (5 + 200 + 5) * size_of::<u32>() + 3 * size_of::<Vec<u32>>()
    );
    let shape = TraceShape {
        original_clauses: 100,
        original_literals: 200,
        derived_steps: 1,
        hints: 2,
        max_row_hints: 2,
        ..TraceShape::default()
    };
    let peaks = planned_trace_peaks(shape, 2, 3, 0, 0, 0).unwrap();
    let retained = planned_retained_bytes(peaks.shape, 0).unwrap();
    assert_eq!(peaks.shape.root_index_scratch_bytes, dense);
    assert_eq!(
        peaks.conversion,
        retained
            + peaks.shape.synthesis_scratch_bytes
            + peaks.shape.compaction_scratch_bytes
            + dense
    );
    assert_eq!(
        peaks.replay, retained,
        "neither index nor cursor survives conversion"
    );
}

#[test]
fn preflight_reserves_index_peak_before_widening_slack() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![pos(0)], true);
    trace.add_clause(2, vec![neg(0)], true);
    trace.add_clause_with_hints(3, vec![], false, vec![1, 2]);
    let mut limits = ResolutionValidationLimits::unbounded();
    limits.max_hints = 2; // Disallow the unrelated fully widened three-hint plan.
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let shape = preflight_trace_shape(&trace, trace.entries(), 2, 0, false, &mut meter).unwrap();
    let peaks = choose_trace_plan(shape, None, 3, 2, 3, 0, &limits).unwrap();
    assert!(peaks.shape.root_index_scratch_bytes > 0);
    limits.max_bytes = peaks.conversion.max(peaks.replay);
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let exact = preflight_trace_shape(&trace, trace.entries(), 2, 0, false, &mut meter).unwrap();
    assert_eq!(exact.widening_byte_slack, 0);
    limits.max_bytes -= 1;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    assert!(matches!(
        preflight_trace_shape(&trace, trace.entries(), 2, 0, false, &mut meter),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
}

#[test]
fn pending_allocations_and_actual_capacity_growth_are_checked() {
    let admitted = planned_bytes(2, 1, 2).unwrap();
    // These are independent capacity-census checks, not claims that the
    // allocator used by this test actually over-allocates reserve_exact.
    assert!(check_capacities(5, 2, 5, admitted).is_ok());
    for (heads, items, cursor) in [(6, 2, 5), (5, 3, 5), (5, 2, 6)] {
        assert!(matches!(
            check_capacities(heads, items, cursor, admitted),
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                ..
            })
        ));
    }
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = empty_root(2);
    assert!(matches!(
        build(
            &mut root,
            &[(1, vec![pos(0), neg(1)])],
            2,
            admitted - 1,
            &mut meter
        ),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
    assert!(root.index_heads.is_none());
    assert_eq!(root.index_items.capacity(), 0);
}

#[test]
fn csr_preserves_duplicate_occurrences_and_literal_polarity() {
    let originals = vec![
        (1, vec![pos(0), neg(1), pos(0)]),
        (2, vec![neg(0), pos(1)]),
        (3, vec![pos(2), neg(1)]),
    ];
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = empty_root(3);
    let admitted = planned_bytes(3, 3, 7).unwrap();
    build(&mut root, &originals, 3, admitted, &mut meter).unwrap();
    let heads = root.index_heads.as_ref().unwrap();
    assert_eq!(heads.len(), 7);
    assert_eq!(heads.last(), Some(&7));
    for variable in 0..3 {
        for positive in [false, true] {
            let code = literal_code(variable, positive);
            let expected: Vec<_> = originals
                .iter()
                .enumerate()
                .flat_map(|(row, (_, clause))| {
                    clause
                        .iter()
                        .filter(move |lit| {
                            lit.variable().index() == variable && lit.is_positive() == positive
                        })
                        .map(move |_| row as u32)
                })
                .collect();
            assert_eq!(
                &root.index_items[heads[code] as usize..heads[code + 1] as usize],
                expected
            );
        }
    }
    assert!(bytes(heads.capacity(), root.index_items.capacity(), heads.len()).unwrap() <= admitted);
}

#[test]
fn representation_refusal_is_distinct_from_accounting_overflow() {
    assert_eq!(planned_bytes(usize::MAX, 0, 0), Ok(0));
    if let Some(over_u32) = (u32::MAX as usize).checked_add(1) {
        assert_eq!(planned_bytes(1, over_u32, 0), Ok(0));
        assert_eq!(planned_bytes(1, 0, over_u32), Ok(0));
    }
    assert!(matches!(
        bytes(usize::MAX, 1, 0),
        Err(ResolutionValidationError::AccountingOverflow { .. })
    ));
    assert!(matches!(
        planned_bytes((usize::MAX - 1) / 2, 0, 0),
        Err(ResolutionValidationError::AccountingOverflow { .. })
    ));
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = empty_root(0);
    build(&mut root, &[], usize::MAX, 0, &mut meter).unwrap();
    assert!(root.index_heads.is_none());
    assert_eq!(root.index_items.len(), 0);
}

#[test]
fn stop_and_work_refusal_never_publish_a_partial_index() {
    let originals = vec![(1, vec![pos(0), neg(1)]); 1024];
    let admitted = planned_bytes(2, originals.len(), 2048).unwrap();
    let run = |stop_at: usize, work: u64| {
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = work;
        let mut root = empty_root(2);
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            build(&mut root, &originals, 2, admitted, &mut meter)?;
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        (result, calls.get(), root)
    };
    let (success, polls, root) = run(usize::MAX, u64::MAX);
    let work = success.unwrap();
    assert_eq!(root.index_items.len(), 2048);
    assert!(polls > 3);
    for stop_at in 1..=polls {
        let (result, calls, root) = run(stop_at, u64::MAX);
        assert!(matches!(result, Err(ResolutionValidationError::Cancelled)));
        assert_eq!(
            calls, stop_at,
            "a transient stop must not become a fallback"
        );
        assert!(root.index_heads.is_none());
        assert_eq!(root.index_items.len(), 0);
    }
    let (result, _, root) = run(usize::MAX, work - 1);
    assert!(matches!(
        result,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));
    assert!(root.index_heads.is_none());
    assert_eq!(root.index_items.len(), 0);
}

#[test]
fn retained_index_coexists_with_full_and_terminal_repair() {
    let originals = vec![
        (1, vec![pos(0)]),
        (2, vec![neg(0), pos(1)]),
        (3, vec![pos(2), pos(3)]),
        (4, vec![pos(2), neg(3)]),
        (5, vec![neg(2), pos(3)]),
        (6, vec![neg(2), neg(3)]),
    ];
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let admitted = planned_bytes(5, 6, 11).unwrap();
    let owner = CompactionScratch::new(5, CompactionScratch::planned_bytes(5).unwrap(), &mut meter)
        .unwrap();
    let mut root =
        compute_root_propagation(&originals, &[pos(4)], 5, admitted, &mut meter).unwrap();
    assert!(root.conflict.is_none());
    assert!(root.index_heads.is_some());
    let retained_items = root.index_items.clone();
    assert_eq!(
        compact_rup_hint_candidates_rooted(
            &mut root,
            &originals,
            &[],
            &[pos(1)],
            &[2],
            6,
            6,
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
            &[pos(4)],
            5,
            6,
            1,
            planned_synthesis_scratch_bytes(5, 6).unwrap(),
            &mut meter
        )
        .unwrap(),
        Some(vec![1, 2])
    );
    let derived = vec![RupStep {
        id: 7,
        clause: vec![pos(2)],
        rup_hints: vec![3, 4],
    }];
    assert_ne!(
        synthesize_terminal_empty_hints(
            &originals,
            &derived,
            &[pos(4)],
            5,
            planned_synthesis_scratch_bytes(5, 6).unwrap(),
            &mut meter
        )
        .unwrap()
        .len(),
        0
    );
    assert_eq!(root.index_items, retained_items);
    assert!(root.index_heads.is_some());
    drop(owner);

    let mut trace = ClauseTrace::new();
    for (id, clause) in originals {
        trace.add_clause(id, clause, true);
    }
    trace.add_clause_with_hints(7, vec![pos(1)], false, vec![2]);
    trace.add_clause_with_hints(8, vec![pos(2)], false, vec![3, 4]);
    trace.mark_empty();
    let checked = validate_clause_trace_resolution_with_unit_premises_interruptible(
        &trace,
        5,
        &[pos(4)],
        &limits,
        || false,
    )
    .unwrap();
    assert_eq!(checked.dag().derived.len(), 3);
    assert_eq!(checked.dag().derived[0].rup_hints, vec![1, 2]);
    assert_eq!(checked.dag().derived.last().unwrap().clause.len(), 0);
}
