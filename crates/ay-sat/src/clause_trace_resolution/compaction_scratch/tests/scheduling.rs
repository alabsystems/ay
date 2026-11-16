// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod oracle;
mod resources;

struct Case {
    originals: Vec<(u64, Vec<Literal>)>,
    derived: Vec<RupStep>,
    candidates: Vec<u64>,
    num_vars: usize,
}

fn reverse_chains(length: u32, noise: usize) -> (Case, [Vec<u64>; 2]) {
    let mut originals = Vec::new();
    for _ in 0..noise {
        // Always open for +g, with a long false prefix unaffected by the chain.
        let mut clause = vec![pos(0); 32];
        clause.extend([pos(length + 2), pos(length + 3)]);
        originals.push((originals.len() as u64 + 1, clause));
    }
    let mut candidates: Vec<_> = (1..=noise as u64).collect();
    let mut expected = [Vec::new(), Vec::new()];
    for (branch, guard) in [pos(0), neg(0)].into_iter().enumerate() {
        let first = originals.len() as u64 + 1;
        originals.push((first, vec![guard, pos(1)]));
        for variable in 1..length {
            originals.push((
                originals.len() as u64 + 1,
                vec![guard, neg(variable), pos(variable + 1)],
            ));
        }
        let close = originals.len() as u64 + 1;
        originals.push((close, vec![guard, neg(length), pos(length + 1)]));
        originals.push((close + 1, vec![guard, neg(length), neg(length + 1)]));
        candidates.extend((first..=close + 1).rev());
        expected[branch].extend(first..close);
        expected[branch].extend([close + 1, close]);
    }
    (
        Case {
            originals,
            derived: vec![],
            candidates,
            num_vars: length as usize + 4,
        },
        expected,
    )
}

fn admission(case: &Case) -> usize {
    let literals = case
        .candidates
        .iter()
        .map(|&id| {
            prior_clause_by_id(&case.originals, &case.derived, id)
                .unwrap()
                .len()
        })
        .sum();
    rooted_scheduler::Scheduler::planned_bytes(case.num_vars, case.candidates.len(), literals)
        .unwrap()
}

fn scheduled_row(
    case: &Case,
    owner: CompactionScratch,
    target: &[Literal],
    premises: &[Literal],
    scheduler_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<(Option<Vec<u64>>, CompactionScratch), ResolutionValidationError> {
    let scratch_bytes = planned_synthesis_scratch_bytes(owner.assign.len(), case.candidates.len())?;
    compact_rup_hint_candidates(
        &case.originals,
        &case.derived,
        target,
        premises,
        &case.candidates,
        case.candidates.len(),
        owner,
        scratch_bytes,
        scheduler_bytes,
        meter,
    )
}

fn fresh_owner(num_vars: usize) -> CompactionScratch {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    scratch(num_vars, &mut meter)
}

fn assert_clean(owner: &CompactionScratch) {
    assert!(owner.assign.iter().all(Option::is_none));
    assert_eq!(owner.touched.len(), 0);
}

enum Sweep {
    Legacy,
    Scheduled,
}

fn measured(
    case: &Case,
    target: &[Literal],
    sweep: Sweep,
    max_work: u64,
) -> Result<(Option<Vec<u64>>, u64), ResolutionValidationError> {
    let owner = fresh_owner(case.num_vars);
    let mut limits = ResolutionValidationLimits::unbounded();
    limits.max_work = max_work;
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop)?;
    let (hints, owner) = match sweep {
        Sweep::Legacy => oracle::legacy_row(case, owner, target, &[], &mut meter),
        Sweep::Scheduled => scheduled_row(case, owner, target, &[], admission(case), &mut meter),
    }?;
    assert_clean(&owner);
    Ok((hints, meter.consumed_work()))
}

#[test]
fn ordinary_scheduler_beats_retired_oracle_on_reverse_chain_with_open_noise() {
    let (case, expected) = reverse_chains(128, 64);
    let old = measured(&case, &[pos(0)], Sweep::Legacy, u64::MAX).unwrap();
    let new = measured(&case, &[pos(0)], Sweep::Scheduled, u64::MAX).unwrap();
    assert_eq!(old.0, Some(expected[0].clone()));
    assert_eq!(new.0, old.0);
    assert!(new.1 < old.1);
    assert_eq!(
        measured(&case, &[pos(0)], Sweep::Scheduled, new.1).unwrap(),
        new
    );
    assert!(matches!(
        measured(&case, &[pos(0)], Sweep::Legacy, new.1),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));
}

#[test]
fn ordinary_duplicate_positions_opposite_rows_replay_and_corruption_refuses() {
    let (mut case, expected) = reverse_chains(8, 3);
    case.candidates = case.candidates.iter().flat_map(|&id| [id, id]).collect();
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut owner = fresh_owner(case.num_vars);
    let mut steps = Vec::new();
    let first = case.originals.len() as u64 + 1;
    for (index, target) in [pos(0), neg(0), pos(0), neg(0)].into_iter().enumerate() {
        let (old, _) = oracle::legacy_row(
            &case,
            fresh_owner(case.num_vars),
            &[target],
            &[],
            &mut meter,
        )
        .unwrap();
        let (actual, returned) =
            scheduled_row(&case, owner, &[target], &[], admission(&case), &mut meter).unwrap();
        assert_eq!(actual, old);
        assert_eq!(actual.as_ref(), Some(&expected[index % 2]));
        assert_clean(&returned);
        owner = returned;
        steps.push(RupStep {
            id: first + index as u64,
            clause: vec![target],
            rup_hints: actual.unwrap(),
        });
    }
    let empty_clause_id = first + steps.len() as u64;
    steps.push(RupStep {
        id: empty_clause_id,
        clause: vec![],
        rup_hints: vec![first, first + 1],
    });
    let dag = ResolutionDag {
        num_vars: case.num_vars,
        original_clauses: case.originals,
        derived: steps,
        empty_clause_id,
    };
    assert_eq!(dag.validate_with_limits(&limits), Ok(()));
    for index in 0..4 {
        let mut corrupt = dag.clone();
        corrupt.derived[index].rup_hints.pop();
        assert!(corrupt.validate_with_limits(&limits).is_err());
    }
}

#[test]
fn ordinary_competing_reasons_derived_ids_and_repeated_literals_keep_order() {
    let mut case = Case {
        originals: vec![
            (1, vec![pos(0), pos(1)]),
            (2, vec![pos(0), pos(2)]),
            (3, vec![neg(1), pos(3)]),
            (4, vec![neg(2), pos(3)]),
            (5, vec![neg(3), pos(4)]),
            (6, vec![neg(4)]),
            (7, vec![pos(5), pos(5)]),
            (8, vec![pos(5), neg(5)]),
        ],
        derived: vec![],
        candidates: vec![7, 8, 4, 3, 5, 6, 1, 2],
        num_vars: 6,
    };
    let old = measured(&case, &[pos(0)], Sweep::Legacy, u64::MAX)
        .unwrap()
        .0;
    assert_eq!(old, Some(vec![6, 1, 2, 4, 5]));
    assert_eq!(
        measured(&case, &[pos(0)], Sweep::Scheduled, u64::MAX)
            .unwrap()
            .0,
        old
    );
    case.derived.push(RupStep {
        id: 9,
        clause: case.originals[0].1.clone(),
        rup_hints: vec![1],
    });
    case.candidates = vec![7, 8, 4, 3, 5, 6, 9, 1, 9, 2];
    let old = measured(&case, &[pos(0)], Sweep::Legacy, u64::MAX)
        .unwrap()
        .0;
    assert_eq!(old, Some(vec![6, 9, 2, 4, 5]));
    assert_eq!(
        measured(&case, &[pos(0)], Sweep::Scheduled, u64::MAX)
            .unwrap()
            .0,
        old
    );
}

#[test]
fn ordinary_lazy_first_pass_needs_no_scheduler_bytes_or_unvisited_tail() {
    let mut case = Case {
        originals: vec![
            (1, vec![pos(0)]),
            (2, vec![neg(0)]),
            (3, vec![pos(1), pos(2)]),
        ],
        derived: vec![],
        candidates: vec![],
        num_vars: 4096,
    };
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    for (candidates, expected) in [
        (vec![], None),
        (vec![3], None),
        (vec![1], None),
        (vec![1, 2, 999], Some(vec![1, 2])),
    ] {
        case.candidates = candidates;
        let old = oracle::legacy_row(&case, fresh_owner(case.num_vars), &[], &[], &mut meter)
            .unwrap()
            .0;
        let (actual, owner) =
            scheduled_row(&case, fresh_owner(case.num_vars), &[], &[], 0, &mut meter).unwrap();
        assert_eq!(actual, expected);
        assert_eq!(actual, old);
        assert_clean(&owner);
    }
}

#[test]
fn ordinary_missing_conflict_and_malformed_ids_do_not_manufacture_hints() {
    let (mut case, expected) = reverse_chains(8, 2);
    case.candidates.retain(|id| Some(id) != expected[0].last());
    assert_eq!(
        measured(&case, &[pos(0)], Sweep::Legacy, u64::MAX)
            .unwrap()
            .0,
        None
    );
    assert_eq!(
        measured(&case, &[pos(0)], Sweep::Scheduled, u64::MAX)
            .unwrap()
            .0,
        None
    );
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    for id in [0, 999, 1] {
        case.candidates = vec![id];
        if id == 1 {
            case.originals[0].0 = 77;
        }
        let (actual, owner) = scheduled_row(
            &case,
            fresh_owner(case.num_vars),
            &[pos(0)],
            &[],
            usize::MAX,
            &mut meter,
        )
        .unwrap();
        assert_eq!(actual, None);
        assert_clean(&owner);
    }
    let derived_id = case.originals.len() as u64 + 1;
    case.derived.push(RupStep {
        id: derived_id + 1,
        clause: vec![],
        rup_hints: vec![],
    });
    case.candidates = vec![derived_id];
    assert_eq!(
        scheduled_row(
            &case,
            fresh_owner(case.num_vars),
            &[],
            &[],
            usize::MAX,
            &mut meter
        )
        .unwrap()
        .0,
        None
    );
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![pos(0)], true);
    trace.add_clause(2, vec![neg(0)], true);
    trace.add_clause_with_hints(3, vec![], false, vec![1, 2, 999]);
    assert!(matches!(
        validate_clause_trace_resolution(&trace, 1, &limits),
        Err(ClauseTraceResolutionError::UnknownHint { hint_id: 999, .. })
    ));
}
