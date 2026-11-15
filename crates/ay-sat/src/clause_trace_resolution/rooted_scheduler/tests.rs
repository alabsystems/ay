// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;
use std::cell::Cell;

#[path = "tests/oracle.rs"]
mod oracle;
#[path = "tests/original_retirement.rs"]
mod original_retirement;
#[path = "tests/resources.rs"]
mod resources;
#[path = "tests/selection.rs"]
mod selection_cases;

fn pos(variable: u32) -> Literal {
    Literal::positive(Variable::new(variable))
}
fn neg(variable: u32) -> Literal {
    Literal::negative(Variable::new(variable))
}

fn originals() -> Vec<(u64, Vec<Literal>)> {
    vec![
        (1, vec![pos(0), pos(1)]),
        (2, vec![pos(0), neg(1), pos(2)]),
        (3, vec![pos(0), neg(1), neg(2)]),
        (4, vec![neg(0), pos(3)]),
        (5, vec![neg(0), neg(3), pos(4)]),
        (6, vec![neg(0), neg(3), neg(4)]),
    ]
}

fn root_for(originals: &[(u64, Vec<Literal>)], num_vars: usize) -> RootPropagation {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    compute_root_propagation(
        originals,
        &[],
        num_vars,
        root_occurrence_index::planned_bytes(
            num_vars,
            originals.len(),
            originals.iter().map(|(_, c)| c.len()).sum(),
        )
        .unwrap(),
        &mut meter,
    )
    .unwrap()
}

fn admission(
    num_vars: usize,
    originals: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    hints: &[u64],
) -> usize {
    let literals = hints
        .iter()
        .map(|&id| prior_clause_by_id(originals, derived, id).unwrap().len())
        .sum();
    Scheduler::planned_bytes(num_vars, hints.len(), literals).unwrap()
}

fn assert_clean(root: &RootPropagation) {
    assert!(root.index_retired.is_clear());
    assert!(root.assign.iter().all(Option::is_none));
    assert!(root.cand_reason.iter().all(|&id| id == 0));
    assert!(root.row_trail.is_empty());
    assert!(root.cand_order.is_empty());
    assert!(root.cone_vars.is_empty());
    assert!(root.cone_stack.is_empty());
    assert!(root.cone_mark.iter().all(|&mark| mark == 0));
}

fn compare(
    originals: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    target: Literal,
    candidates: &[u64],
    num_vars: usize,
    use_index: bool,
) -> (Option<u64>, RootPropagation, u64) {
    let limits = ResolutionValidationLimits::unbounded();
    let run = |scheduled| {
        let mut root = root_for(originals, num_vars);
        if !use_index {
            root.index_heads = None;
            root.index_items.clear();
        }
        let mut stop = || false;
        let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
        assert!(matches!(
            seed_rooted_target(&mut root, &[target], &mut meter).unwrap(),
            RootSeedOutcome::Continue
        ));
        let before = meter.consumed_work();
        let result = if scheduled {
            sweep_rooted_candidates(
                &mut root,
                originals,
                derived,
                candidates,
                candidates.len(),
                usize::MAX,
                &mut meter,
            )
        } else {
            oracle::legacy_sweep(
                &mut root,
                originals,
                derived,
                candidates,
                candidates.len(),
                &mut meter,
            )
        }
        .unwrap();
        (result, root, meter.consumed_work() - before)
    };
    let (expected, old, _) = run(false);
    let (actual, new, work) = run(true);
    assert_eq!(actual, expected, "first conflict (not just SAT status)");
    assert_eq!(new.assign, old.assign);
    assert_eq!(
        new.cand_reason, old.cand_reason,
        "first reason for every assigned variable"
    );
    assert_eq!(new.cand_order, old.cand_order);
    assert_eq!(new.row_trail, old.row_trail);
    (actual, new, work)
}

#[test]
fn legacy_two_phase_oracle_preserves_conflicts_reasons_and_duplicate_positions() {
    let base = originals();
    for hints in [
        vec![3, 2, 1, 6, 5, 4],
        vec![1],
        vec![3, 3, 2, 1, 1],
        vec![6, 5, 4],
    ] {
        for target in [pos(0), neg(0)] {
            compare(&base, &[], target, &hints, 5, true);
            compare(&base, &[], target, &hints, 5, false);
        }
    }
    let derived = vec![RupStep {
        id: 7,
        clause: base[0].1.clone(),
        rup_hints: vec![1],
    }];
    compare(&base, &derived, pos(0), &[3, 2, 7, 1, 7], 5, true);
    let duplicated = vec![
        (1, vec![pos(0), pos(1), pos(1)]),
        (2, vec![pos(0), neg(1), pos(2)]),
        (3, vec![pos(0), neg(1), neg(2)]),
        (4, vec![pos(1), neg(1)]),
        (5, vec![pos(0), pos(1)]),
    ];
    compare(&duplicated, &[], pos(0), &[4, 2, 1, 1, 3, 5], 3, true);
    let competing = vec![
        (1, vec![pos(0), pos(1)]),
        (2, vec![pos(0), pos(2)]),
        (3, vec![neg(1), pos(3)]),
        (4, vec![neg(2), pos(3)]),
        (5, vec![neg(3), pos(4)]),
    ];
    let (_, root, _) = compare(&competing, &[], pos(0), &[4, 3, 5, 1, 2], 5, true);
    assert_eq!(
        root.cand_reason[3], 4,
        "earlier candidate wins the competing reason"
    );
}

#[test]
fn original_cascade_still_runs_when_candidate_events_have_no_ready_positions() {
    // First pass sets b, second pass sets c. No candidate contains !c, so
    // the next ready heap is empty; c nevertheless wakes the ORIGINAL CSR.
    let clauses = vec![
        (1, vec![pos(0), pos(1)]),
        (2, vec![neg(1), pos(2)]),
        (3, vec![neg(2), pos(3)]),
        (4, vec![neg(2), neg(3)]),
    ];
    // Duplicate live positions keep the conservative legacy bound above dense
    // setup, so this remains an indexed-empty-heap test after cheap-row bypass.
    let candidates = [2, 2, 1];
    let (conflict, root, _) = compare(&clauses, &[], pos(0), &candidates, 4, true);
    assert_eq!(conflict, Some(4));
    assert_eq!(root.cand_order, vec![1, 2, 3]);
    let mut root = root_for(&clauses, 4);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    assert!(matches!(
        compact_rup_hint_candidates_rooted(
            &mut root,
            &clauses,
            &[],
            &[pos(0)],
            &candidates,
            5,
            3,
            0,
            &mut meter,
        ),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
    assert_clean(&root);
    // During phase 2 originals are allowed to conflict BEFORE any candidate
    // rescan. Candidate scheduling must never move that boundary earlier.
    assert_eq!(compare(&originals(), &[], pos(0), &[1], 5, true).0, Some(3));
}

#[test]
fn lazy_first_pass_accepts_no_scheduler_budget_and_never_reads_unvisited_tail() {
    let clauses = vec![(1, vec![pos(0), pos(1)]), (2, vec![pos(0), neg(1)])];
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = root_for(&clauses, 25_000);
    let hints = compact_rup_hint_candidates_rooted(
        &mut root,
        &clauses,
        &[],
        &[pos(0)],
        &[1, 2, 999],
        3,
        3,
        0,
        &mut meter,
    )
    .unwrap();
    assert_eq!(hints, Some(vec![1, 2]));
    assert_clean(&root);
    let mut root = root_for(&clauses[..1], 25_000);
    root.index_heads = None;
    root.index_items.clear();
    assert_eq!(
        compact_rup_hint_candidates_rooted(
            &mut root,
            &clauses[..1],
            &[],
            &[neg(0)],
            &[1],
            1,
            1,
            0,
            &mut meter
        )
        .unwrap(),
        None
    );
    assert_clean(&root);
}

#[test]
fn repeated_rows_emit_exact_chains_with_independent_replay_and_corruption_refusal() {
    let clauses = originals();
    let hints = [3, 2, 1, 6, 5, 4];
    let admitted = admission(5, &clauses, &[], &hints);
    let mut root = root_for(&clauses, 5);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut derived = Vec::new();
    for (target, expected) in [
        (pos(0), vec![1, 3, 2]),
        (neg(0), vec![4, 6, 5]),
        (pos(0), vec![1, 3, 2]),
    ] {
        let chain = compact_rup_hint_candidates_rooted(
            &mut root,
            &clauses,
            &[],
            &[target],
            &hints,
            6,
            6,
            admitted,
            &mut meter,
        )
        .unwrap()
        .unwrap();
        assert_eq!(chain, expected);
        assert_clean(&root);
        derived.push(RupStep {
            id: 7 + derived.len() as u64,
            clause: vec![target],
            rup_hints: chain,
        });
    }
    derived.push(RupStep {
        id: 10,
        clause: vec![],
        rup_hints: vec![7, 8],
    });
    let dag = ResolutionDag {
        num_vars: 5,
        original_clauses: clauses,
        derived,
        empty_clause_id: 10,
    };
    assert_eq!(dag.validate_with_limits(&limits), Ok(()));
    for row in 0..3 {
        let mut corrupted = dag.clone();
        corrupted.derived[row].rup_hints.pop();
        assert!(corrupted.validate_with_limits(&limits).is_err());
    }
}

#[test]
fn cheap_candidate_rows_avoid_namespace_sized_setup() {
    let clauses = originals();
    let hints = [3, 2, 1];
    let (_, _, small) = compare(&clauses, &[], pos(0), &hints, 16, false);
    let (_, _, large) = compare(&clauses, &[], pos(0), &hints, 4096, false);
    assert_eq!(
        large, small,
        "the permanent legacy choice does not allocate dense heads"
    );
    assert_eq!(
        Scheduler::planned_bytes(4096, 3, 8).unwrap() - Scheduler::planned_bytes(16, 3, 8).unwrap(),
        4 * (4096 - 16) * size_of::<usize>()
    );
}

#[test]
fn reverse_chain_saves_metered_work_against_legacy_and_replays_exact_hints() {
    const LENGTH: u32 = 256;
    let mut clauses = vec![(1, vec![pos(0), pos(1)])];
    for variable in 1..LENGTH {
        clauses.push((
            u64::from(variable + 1),
            vec![neg(variable), pos(variable + 1)],
        ));
    }
    clauses.push((u64::from(LENGTH + 1), vec![neg(LENGTH), pos(LENGTH + 1)]));
    clauses.push((u64::from(LENGTH + 2), vec![neg(LENGTH), neg(LENGTH + 1)]));
    let candidates: Vec<u64> = (1..=u64::from(LENGTH + 2)).rev().collect();
    let num_vars = LENGTH as usize + 2;
    let bytes = admission(num_vars, &clauses, &[], &candidates);
    let run = |scheduled: bool, work_limit: u64| {
        let mut root = root_for(&clauses, num_vars);
        // Isolate candidate scheduling; separate tests retain the real CSR.
        root.index_heads = None;
        root.index_items.clear();
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = work_limit;
        let mut stop = || false;
        let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
        assert!(matches!(
            seed_rooted_target(&mut root, &[pos(0)], &mut meter).unwrap(),
            RootSeedOutcome::Continue
        ));
        let result = if scheduled {
            sweep_rooted_candidates(
                &mut root,
                &clauses,
                &[],
                &candidates,
                candidates.len(),
                bytes,
                &mut meter,
            )
        } else {
            oracle::legacy_sweep(
                &mut root,
                &clauses,
                &[],
                &candidates,
                candidates.len(),
                &mut meter,
            )
        };
        (result, root, meter.consumed_work())
    };
    let (legacy, old, old_work) = run(false, u64::MAX);
    let (scheduled, new, new_work) = run(true, u64::MAX);
    assert_eq!(scheduled.unwrap(), Some(u64::from(LENGTH + 1)));
    assert_eq!(legacy.unwrap(), Some(u64::from(LENGTH + 1)));
    assert_eq!(new.assign, old.assign);
    assert_eq!(new.cand_reason, old.cand_reason);
    assert_eq!(new.cand_order, old.cand_order);
    assert_eq!(new.row_trail, old.row_trail);
    assert!(new_work < old_work);
    assert_eq!(run(true, new_work).0.unwrap(), Some(u64::from(LENGTH + 1)));
    assert!(matches!(
        run(false, new_work).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));

    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = root_for(&clauses, num_vars);
    root.index_heads = None;
    root.index_items.clear();
    let chain = compact_rup_hint_candidates_rooted(
        &mut root,
        &clauses,
        &[],
        &[pos(0)],
        &candidates,
        candidates.len(),
        candidates.len(),
        bytes,
        &mut meter,
    )
    .unwrap()
    .unwrap();
    let mut expected: Vec<u64> = (1..=u64::from(LENGTH)).collect();
    expected.extend([u64::from(LENGTH + 2), u64::from(LENGTH + 1)]);
    assert_eq!(chain, expected);
    assert_clean(&root);
    let row_id = u64::from(LENGTH + 3);
    let dag = ResolutionDag {
        num_vars,
        original_clauses: clauses,
        derived: vec![
            RupStep {
                id: row_id,
                clause: vec![pos(0)],
                rup_hints: chain,
            },
            RupStep {
                id: row_id + 1,
                clause: vec![],
                rup_hints: vec![row_id],
            },
        ],
        empty_clause_id: row_id + 1,
    };
    // The database entails a, not UNSAT. Only the explicit fixed premise !a
    // makes this complete DAG a refutation; no unrecorded premise is invented.
    assert!(dag
        .validate_with_limits_interruptible(&limits, &[neg(0)], 0, 0, &mut stop)
        .is_ok());
    assert!(dag.validate_with_limits(&limits).is_err());
    let mut corrupt = dag;
    corrupt.derived[0].rup_hints.remove(1);
    assert!(corrupt
        .validate_with_limits_interruptible(&limits, &[neg(0)], 0, 0, &mut stop)
        .is_err());
}
