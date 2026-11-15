// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;
use std::cell::Cell;

#[path = "tests/originals.rs"]
mod originals;

fn pos(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}

fn neg(var: u32) -> Literal {
    Literal::negative(Variable::new(var))
}

fn root_for(originals: &[(u64, Vec<Literal>)], num_vars: usize) -> RootPropagation {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let literals = originals.iter().map(|(_, clause)| clause.len()).sum();
    let root = compute_root_propagation(
        originals,
        &[],
        num_vars,
        root_occurrence_index::planned_bytes(num_vars, originals.len(), literals).unwrap(),
        &mut meter,
    )
    .unwrap();
    assert!(root.assign.iter().all(Option::is_none));
    assert!(root.conflict.is_none());
    root
}

fn assert_clean(root: &RootPropagation) {
    assert!(root.index_retired.is_clear());
    assert!(root.assign.iter().all(Option::is_none));
    assert!(root.cand_reason.iter().all(|&id| id == 0));
    assert!(root.row_trail.is_empty());
    assert!(root.cand_order.is_empty());
    assert!(root.cone_mark.iter().all(|&mark| mark == 0));
    assert!(root.cone_vars.is_empty());
    assert!(root.cone_stack.is_empty());
}

fn two_branch_conflict() -> Vec<(u64, Vec<Literal>)> {
    vec![
        (1, vec![pos(0), pos(1)]),
        (2, vec![pos(0), neg(1), pos(2)]),
        (3, vec![pos(0), neg(1), neg(2)]),
        (4, vec![neg(0), pos(3)]),
        (5, vec![neg(0), neg(3), pos(4)]),
        (6, vec![neg(0), neg(3), neg(4)]),
    ]
}

#[test]
fn reverse_candidates_replay_and_retirement_never_crosses_rows() {
    let originals = two_branch_conflict();
    let mut root = root_for(&originals, 5);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut derived = Vec::new();
    // There are no root units: the target alone starts each propagation.
    // A position retired as satisfied in one row must become eligible again
    // when the opposite target makes its clause open or unit in the next.
    for (target, expected) in [
        (pos(0), vec![1, 3, 2]),
        (neg(0), vec![4, 6, 5]),
        (pos(0), vec![1, 3, 2]),
        (neg(0), vec![4, 6, 5]),
    ] {
        let hints = compact_rup_hint_candidates_rooted(
            &mut root,
            &originals,
            &[],
            &[target],
            &[3, 2, 1, 6, 5, 4],
            6,
            6,
            usize::MAX, // Direct helper test: unbounded scheduler allowance.
            &mut meter,
        )
        .unwrap()
        .expect("the row-triggered candidate chain must conflict");
        assert_eq!(hints, expected);
        assert_clean(&root);
        derived.push(RupStep {
            id: 7 + derived.len() as u64,
            clause: vec![target],
            rup_hints: hints,
        });
    }
    derived.push(RupStep {
        id: 11,
        clause: vec![],
        rup_hints: vec![7, 8],
    });
    let dag = ResolutionDag {
        num_vars: 5,
        original_clauses: originals,
        derived,
        empty_clause_id: 11,
    };
    assert_eq!(dag.validate_with_limits(&limits), Ok(()));
    for row in 0..4 {
        let mut corrupted = dag.clone();
        corrupted.derived[row].rup_hints.pop();
        assert!(corrupted.validate_with_limits(&limits).is_err());
    }
}

fn reverse_chain(length: u32, satisfied: usize) -> (Vec<(u64, Vec<Literal>)>, Vec<u64>) {
    let mut originals = Vec::new();
    for _ in 0..satisfied {
        originals.push((originals.len() as u64 + 1, vec![neg(0), pos(length + 2)]));
    }
    for variable in 1..=length {
        originals.push((
            originals.len() as u64 + 1,
            vec![neg(variable), pos(variable + 1)],
        ));
    }
    originals.push((originals.len() as u64 + 1, vec![pos(0), pos(1)]));
    let mut candidates: Vec<u64> = (1..=satisfied as u64).collect();
    candidates.extend((satisfied as u64 + 1..originals.len() as u64).rev());
    candidates.push(originals.len() as u64);
    (originals, candidates)
}

// Test-only accounting comparator for the previous full candidate sweep,
// excluding the unchanged occurrence-index phase. It is not a proof oracle;
// the separate test above uses independent ResolutionDag replay.
fn unretired_sweep(
    root: &mut RootPropagation,
    originals: &[(u64, Vec<Literal>)],
    candidates: &[u64],
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<u64>, ResolutionValidationError> {
    loop {
        meter.check_controls()?;
        let mut propagated = false;
        for &id in candidates {
            meter.charge(1)?;
            let clause = prior_clause_by_id(originals, &[], id).unwrap();
            match scan_terminal_hint_clause(clause, &root.assign, meter)? {
                TerminalHintScan::Satisfied | TerminalHintScan::Open => {}
                TerminalHintScan::Unit(literal) => {
                    meter.charge(1)?;
                    let variable = literal.variable().index();
                    root.assign[variable] = Some(literal.is_positive());
                    root.cand_reason[variable] = id;
                    root.row_trail.push(variable as u32);
                    root.cand_order.push(variable as u32);
                    propagated = true;
                }
                TerminalHintScan::Conflict => return Ok(Some(id)),
            }
        }
        if !propagated {
            return Ok(None);
        }
    }
}

#[test]
fn scheduled_reverse_chain_preserves_retirement_and_saves_work() {
    const LENGTH: u32 = 128;
    const SATISFIED: usize = 32;
    let (originals, candidates) = reverse_chain(LENGTH, SATISFIED);
    let run = |retire: bool| {
        let mut root = root_for(&originals, LENGTH as usize + 3);
        // Isolate the supported candidate-only phase for an exact work
        // comparison; the production positive test retains the real CSR.
        root.index_heads = None;
        root.index_items.clear();
        let limits = ResolutionValidationLimits::unbounded();
        let mut stop = || false;
        let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
        assert!(matches!(
            seed_rooted_target(&mut root, &[pos(0)], &mut meter).unwrap(),
            RootSeedOutcome::Continue
        ));
        let before = meter.consumed_work();
        let result = if retire {
            sweep_rooted_candidates(
                &mut root,
                &originals,
                &[],
                &candidates,
                candidates.len(),
                usize::MAX, // Direct helper test: unbounded scheduler allowance.
                &mut meter,
            )
        } else {
            unretired_sweep(&mut root, &originals, &candidates, &mut meter)
        };
        assert_eq!(result.unwrap(), None);
        assert!(root.assign[1..=LENGTH as usize + 1]
            .iter()
            .all(|&value| value == Some(true)));
        (meter.consumed_work() - before, root.cand_order)
    };
    let (before, original_order) = run(false);
    let (after, retired_order) = run(true);
    assert_eq!(original_order, retired_order);
    // Synthetic end-to-end work comparison, not a claim that the original
    // range traces fit their allowance. Scheduler queue debits and whole-run
    // work refusal are checked in its dedicated tests.
    assert!(after < before);
}

#[test]
fn open_missing_malformed_and_hint_cap_paths_still_clean_the_row() {
    let originals = two_branch_conflict();
    let mut root = root_for(&originals, 5);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut satisfiable = root_for(&originals[..2], 5);
    // This prefix becomes unit after one pass, but neither its candidates
    // nor its real occurrence index can produce a conflict.
    assert_eq!(
        compact_rup_hint_candidates_rooted(
            &mut satisfiable,
            &originals[..2],
            &[],
            &[pos(0)],
            &[2, 1],
            2,
            2,
            usize::MAX, // Direct helper test: unbounded scheduler allowance.
            &mut meter,
        )
        .unwrap(),
        None
    );
    assert_clean(&satisfiable);
    for (candidates, cap, expected) in [
        (vec![1, 999], 6, None),
        (vec![3, 2, 1], 2, None),
        (vec![3, 2, 1], 3, Some(vec![1, 3, 2])),
    ] {
        assert_eq!(
            compact_rup_hint_candidates_rooted(
                &mut root,
                &originals,
                &[],
                &[pos(0)],
                &candidates,
                cap,
                candidates.len(),
                usize::MAX, // Direct helper test: unbounded scheduler allowance.
                &mut meter,
            )
            .unwrap(),
            expected
        );
        assert_clean(&root);
    }
    let malformed = vec![RupStep {
        id: 7,
        clause: vec![pos(99)],
        rup_hints: vec![],
    }];
    assert!(matches!(
        compact_rup_hint_candidates_rooted(
            &mut root,
            &originals,
            &malformed,
            &[pos(0)],
            &[7],
            1,
            1,
            usize::MAX, // Direct helper test: unbounded scheduler allowance.
            &mut meter,
        ),
        Err(ResolutionValidationError::Invalid(
            ResolutionDagValidateError::VarOutOfRange { .. }
        ))
    ));
    assert_clean(&root);
}

#[test]
fn recorded_slot_checks_requested_actual_and_overflow_without_root_slack() {
    assert_eq!(size_of::<RetiredCandidates>(), size_of::<Vec<u8>>());
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let flags = RetiredCandidates::new(64, 64, &mut meter).unwrap();
    assert_eq!(flags.0.len(), 64);
    assert!(flags.0.iter().all(|&flag| flag == 0));
    for result in [
        RetiredCandidates::new(65, 64, &mut meter).map(|_| ()),
        RetiredCandidates::check_capacity(65, 64),
    ] {
        assert!(matches!(
            result,
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                ..
            })
        ));
    }
    assert!(matches!(
        RetiredCandidates::check_capacity(usize::MAX, 64),
        Err(ResolutionValidationError::AccountingOverflow {
            resource: ResolutionValidationResource::Bytes
        })
    ));
    let shape = TraceShape {
        max_row_hints: 3,
        ..TraceShape::default()
    };
    let peaks = planned_trace_peaks(shape, 4096, 6, 0, 0, 0).unwrap();
    let without_recorded = synthesis_scratch_bytes_from_capacities(4096, 6, 6, 0, 4096).unwrap();
    assert_eq!(peaks.shape.synthesis_scratch_bytes - without_recorded, 6);
    // Even a large unrelated root/output allowance cannot fund a seventh
    // flag: only the preflighted recorded slot reaches this constructor.
    assert!(peaks.shape.synthesis_scratch_bytes > 4096);
    assert!(RetiredCandidates::new(7, 6, &mut meter).is_err());
    assert!(RetiredCandidates::new(6, 6, &mut meter).is_ok());
}

#[test]
fn every_stop_position_and_work_refusal_remain_terminal_with_cleanup() {
    let (originals, candidates) = reverse_chain(8, CONTROL_POLL_INTERVAL + 1);
    let run = |stop_at: usize, max_work: u64| {
        let mut root = root_for(&originals, 11);
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = max_work;
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            let result = compact_rup_hint_candidates_rooted(
                &mut root,
                &originals,
                &[],
                &[pos(0)],
                &candidates,
                candidates.len(),
                candidates.len(),
                usize::MAX, // Direct helper test: unbounded scheduler allowance.
                &mut meter,
            )?;
            assert_eq!(result, None);
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        assert_clean(&root);
        (result, calls.get())
    };
    let (success, polls) = run(usize::MAX, u64::MAX);
    let work = success.unwrap();
    assert!(polls > 10, "cover initialization, skips and later rounds");
    for stop_at in 1..=polls {
        let (result, calls) = run(stop_at, u64::MAX);
        assert!(matches!(result, Err(ResolutionValidationError::Cancelled)));
        assert_eq!(calls, stop_at, "no resource error becomes a fallback");
    }
    assert!(matches!(
        run(usize::MAX, work - 1).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));
}

#[test]
fn byte_refusal_and_expired_deadline_restore_target_seeding() {
    let originals = two_branch_conflict();
    let mut root = root_for(&originals, 5);
    let mut limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    assert!(matches!(
        compact_rup_hint_candidates_rooted(
            &mut root,
            &originals,
            &[],
            &[pos(0)],
            &[3, 2, 1],
            3,
            2,
            usize::MAX, // Direct helper test: unbounded scheduler allowance.
            &mut meter,
        ),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
    assert_clean(&root);
    limits.deadline = Some(Instant::now());
    // Direct construction lets the expired deadline be observed after the
    // small target seed, inside the new scratch admission control check.
    let mut meter = ConversionMeter {
        limits: &limits,
        should_stop: &mut stop,
        work: 0,
        attribution: WorkAttribution::default(),
    };
    assert!(matches!(
        compact_rup_hint_candidates_rooted(
            &mut root,
            &originals,
            &[],
            &[pos(0)],
            &[3, 2, 1],
            3,
            3,
            usize::MAX, // Direct helper test: unbounded scheduler allowance.
            &mut meter,
        ),
        Err(ResolutionValidationError::DeadlineExceeded)
    ));
    assert_clean(&root);
}
