// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod resources;

fn root_for(originals: &[(u64, Vec<Literal>)], meter: &mut ConversionMeter<'_>) -> RootPropagation {
    compute_root_propagation(
        originals,
        &[neg(1)],
        5,
        planned_bytes(
            5,
            originals.len(),
            originals.iter().map(|(_, c)| c.len()).sum(),
        )
        .unwrap(),
        meter,
    )
    .unwrap()
}

fn branches(noise: usize) -> Vec<(u64, Vec<Literal>)> {
    let mut originals = vec![(1, vec![pos(0)])];
    for _ in 0..noise {
        originals.push((originals.len() as u64 + 1, vec![pos(2), neg(3), pos(0)]));
        originals.push((originals.len() as u64 + 1, vec![neg(2), neg(4), pos(0)]));
    }
    for clause in [
        vec![neg(0), pos(1), pos(2), pos(3)],
        vec![pos(2), neg(3)],
        vec![neg(0), pos(1), neg(2), pos(4)],
        vec![neg(2), neg(4)],
    ] {
        originals.push((originals.len() as u64 + 1, clause));
    }
    originals
}

// Test-only full CSR baseline, retaining the old source-position and literal
// ordering. It does not decide propagation or validate a proof.
fn install_unfiltered_index(root: &mut RootPropagation, originals: &[(u64, Vec<Literal>)]) {
    let mut heads = vec![0u32; 2 * root.assign.len() + 1];
    for (_, clause) in originals {
        for literal in clause {
            heads[literal_code(literal.variable().index(), literal.is_positive())] += 1;
        }
    }
    let mut total = 0;
    for head in &mut heads {
        let count = *head;
        *head = total;
        total += count;
    }
    let mut items = vec![0; total as usize];
    let mut cursor = heads.clone();
    for (position, (_, clause)) in originals.iter().enumerate() {
        for literal in clause {
            let code = literal_code(literal.variable().index(), literal.is_positive());
            items[cursor[code] as usize] = position as u32;
            cursor[code] += 1;
        }
    }
    root.index_heads = Some(heads);
    root.index_items = items;
}

fn repair(
    root: &mut RootPropagation,
    originals: &[(u64, Vec<Literal>)],
    target: Literal,
    meter: &mut ConversionMeter<'_>,
) -> Option<Vec<u64>> {
    compact_rup_hint_candidates_rooted(root, originals, &[], &[target], &[], 6, 0, 0, meter)
        .unwrap()
}

#[test]
fn filtered_buckets_keep_source_positions_polarity_and_live_duplicates() {
    let originals = vec![
        (1, vec![pos(0)]),
        (2, vec![neg(0), pos(2), pos(2), neg(3)]),
        (3, vec![neg(1), pos(3)]),
        (4, vec![pos(1), neg(2), pos(3)]),
        (5, vec![pos(2), neg(2)]),
        // The root-true literal follows two unassigned literals: a scanner
        // that stops at Open would miss this removable clause.
        (6, vec![pos(2), pos(3), pos(0)]),
    ];
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let root = root_for(&originals, &mut meter);
    assert_eq!(root.assign, vec![Some(true), Some(false), None, None, None]);
    let heads = root.index_heads.as_ref().unwrap();
    assert_eq!(heads.last(), Some(&7));
    for (code, expected) in [
        (literal_code(0, false), vec![]),
        (literal_code(0, true), vec![]),
        (literal_code(1, false), vec![]),
        (literal_code(1, true), vec![]),
        (literal_code(2, false), vec![3, 4]),
        (literal_code(2, true), vec![1, 1, 4]),
        (literal_code(3, false), vec![1]),
        (literal_code(3, true), vec![3]),
    ] {
        assert_eq!(
            &root.index_items[heads[code] as usize..heads[code + 1] as usize],
            expected
        );
    }
    assert_eq!(
        root.reason[0], 1,
        "omitting a reason from the index never deletes the reason"
    );
}

#[test]
fn filtered_cascade_matches_unfiltered_hints_and_saves_row_work() {
    let originals = branches(64);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut filtered = root_for(&originals, &mut meter);
    let mut unfiltered = root_for(&originals, &mut meter);
    install_unfiltered_index(&mut unfiltered, &originals);
    let heads = filtered.index_heads.clone();
    let items = filtered.index_items.clone();
    assert!(items.len() < unfiltered.index_items.len());
    let before = meter.consumed_work();
    let expected: Vec<_> = [pos(2), neg(2), pos(2), neg(2)]
        .into_iter()
        .map(|target| repair(&mut unfiltered, &originals, target, &mut meter))
        .collect();
    let unfiltered_work = meter.consumed_work() - before;
    let before = meter.consumed_work();
    let actual: Vec<_> = [pos(2), neg(2), pos(2), neg(2)]
        .into_iter()
        .map(|target| repair(&mut filtered, &originals, target, &mut meter))
        .collect();
    let filtered_work = meter.consumed_work() - before;
    assert_eq!(actual, expected);
    assert_eq!(actual[0], Some(vec![1, 130, 131]));
    assert_eq!(actual[1], Some(vec![1, 132, 133]));
    // This compares cascade work only; it makes no claim about original-query
    // total work or amortization of the one-time index filtering census.
    assert!(filtered_work < unfiltered_work);
    assert_eq!(filtered.assign, unfiltered.assign);
    assert_eq!(
        filtered.assign,
        vec![Some(true), Some(false), None, None, None]
    );
    assert_eq!(filtered.row_trail.len(), 0);
    assert_eq!(filtered.cand_order.len(), 0);
    assert!(filtered.cand_reason.iter().all(|&reason| reason == 0));
    assert_eq!(filtered.cone_vars.len(), 0);
    assert!(filtered.cone_mark.iter().all(|&mark| mark == 0));
    assert_eq!(filtered.index_heads, heads);
    assert_eq!(filtered.index_items, items);
}

#[test]
fn filtered_root_reasons_replay_independently_and_corruption_refuses() {
    let originals = branches(2);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = root_for(&originals, &mut meter);
    let first = originals.len() as u64 + 1;
    let mut derived = Vec::new();
    for target in [pos(2), neg(2)] {
        derived.push(RupStep {
            id: first + derived.len() as u64,
            clause: vec![target],
            rup_hints: repair(&mut root, &originals, target, &mut meter).unwrap(),
        });
    }
    derived.push(RupStep {
        id: first + 2,
        clause: vec![],
        rup_hints: vec![first, first + 1],
    });
    let dag = ResolutionDag {
        num_vars: 5,
        original_clauses: originals,
        derived,
        empty_clause_id: first + 2,
    };
    assert!(dag
        .validate_with_limits_interruptible(&limits, &[neg(1)], 0, 0, &mut stop)
        .is_ok());
    assert!(
        dag.validate_with_limits(&limits).is_err(),
        "the fixed premise remains necessary"
    );
    for row in 0..2 {
        let mut corrupted = dag.clone();
        corrupted.derived[row].rup_hints.pop();
        assert!(corrupted
            .validate_with_limits_interruptible(&limits, &[neg(1)], 0, 0, &mut stop)
            .is_err());
    }
    let mut missing_reason = dag.clone();
    missing_reason.derived[0].rup_hints.remove(0);
    assert!(missing_reason
        .validate_with_limits_interruptible(&limits, &[neg(1)], 0, 0, &mut stop)
        .is_err());
}

#[test]
fn opposed_root_target_still_uses_full_original_synthesis() {
    let originals = branches(2);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = root_for(&originals, &mut meter);
    let items = root.index_items.clone();
    assert!(
        !items.contains(&0),
        "root unit was removed from the index only"
    );
    assert_eq!(repair(&mut root, &originals, pos(0), &mut meter), None);
    assert_eq!(
        repair(&mut root, &originals, neg(1), &mut meter),
        Some(vec![])
    );
    let synthesized = synthesize_rup_hints(
        &originals,
        &[],
        &[pos(0)],
        &[neg(1)],
        5,
        6,
        0,
        planned_synthesis_scratch_bytes(5, 6).unwrap(),
        &mut meter,
    )
    .unwrap();
    assert_eq!(synthesized, Some(vec![1]));
    assert_eq!(root.assign, vec![Some(true), Some(false), None, None, None]);
    assert_eq!(root.row_trail.len(), 0);
    assert_eq!(root.index_items, items);
    assert!(repair(&mut root, &originals, pos(2), &mut meter).is_some());
}
