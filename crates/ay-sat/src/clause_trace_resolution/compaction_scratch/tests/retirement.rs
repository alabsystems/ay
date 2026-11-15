// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

struct Fixture {
    originals: Vec<(u64, Vec<Literal>)>,
    candidates: Vec<u64>,
    expected: [Vec<u64>; 2],
    num_vars: usize,
}

fn reverse_chains(length: u32, satisfied: usize, width: usize) -> Fixture {
    assert!(length > 0);
    let mut originals = Vec::new();
    for _ in 0..satisfied {
        // Under target +g, every repeated +g is false before the final -g
        // satisfies this clause. Retirement avoids repeating that long scan.
        let mut clause = vec![pos(0); width];
        clause.push(neg(0));
        originals.push((originals.len() as u64 + 1, clause));
    }
    let mut candidates: Vec<u64> = (1..=satisfied as u64).collect();
    let mut expected = [Vec::new(), Vec::new()];
    for (branch, guard) in [pos(0), neg(0)].into_iter().enumerate() {
        let start = originals.len() as u64 + 1;
        originals.push((start, vec![guard, pos(1)]));
        for variable in 1..length {
            originals.push((
                originals.len() as u64 + 1,
                vec![guard, neg(variable), pos(variable + 1)],
            ));
        }
        let close = originals.len() as u64 + 1;
        originals.push((close, vec![guard, neg(length), pos(length + 1)]));
        originals.push((close + 1, vec![guard, neg(length), neg(length + 1)]));
        candidates.extend((start..=close + 1).rev());
        expected[branch].extend(start..close);
        expected[branch].extend([close + 1, close]);
    }
    Fixture {
        originals,
        candidates,
        expected,
        num_vars: length as usize + 2,
    }
}

// Bounded test-only copy of the former ordinary compactor: propagated units
// retire, satisfied clauses do not. The shared scanner/scratch are unchanged;
// independent ResolutionDag replay below supplies the separate proof oracle.
fn legacy_row(
    mut owner: CompactionScratch,
    originals: &[(u64, Vec<Literal>)],
    target: &[Literal],
    candidates: &[u64],
    meter: &mut ConversionMeter<'_>,
) -> Result<(Option<Vec<u64>>, CompactionScratch), ResolutionValidationError> {
    meter.check_controls()?;
    let CompactionState {
        mut hints,
        mut recorded,
    } = prepare_compaction_state(
        candidates,
        candidates.len(),
        planned_synthesis_scratch_bytes(owner.assign.len(), candidates.len())?,
        meter,
    )?;
    let result = if owner.seed(&[], target, meter)? {
        Some(hints)
    } else {
        let found = 'sweep: loop {
            let mut propagated = false;
            for (position, &id) in candidates.iter().enumerate() {
                if position % CONTROL_POLL_INTERVAL == 0 {
                    meter.check_controls()?;
                }
                meter.charge(1)?;
                if recorded[position] != 0 {
                    continue;
                }
                let Some(clause) = prior_clause_by_id(originals, &[], id) else {
                    break 'sweep false;
                };
                match scan_terminal_hint_clause(clause, &owner.assign, meter)? {
                    TerminalHintScan::Satisfied | TerminalHintScan::Open => {}
                    TerminalHintScan::Unit(literal) => {
                        hints.push(id);
                        meter.charge(1)?;
                        recorded[position] = 1;
                        owner.set_unassigned(literal.variable(), literal.is_positive(), meter)?;
                        propagated = true;
                    }
                    TerminalHintScan::Conflict => {
                        hints.push(id);
                        meter.charge(1)?;
                        break 'sweep true;
                    }
                }
            }
            if !propagated {
                break false;
            }
        };
        found.then_some(hints)
    };
    owner.clear(meter)?;
    Ok((result, owner))
}

enum Sweep {
    Legacy,
    Retirement,
}

fn measured(fixture: &Fixture, sweep: Sweep) -> (Option<Vec<u64>>, u64) {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let owner = scratch(fixture.num_vars, &mut meter);
    let (hints, owner) = match sweep {
        Sweep::Legacy => legacy_row(
            owner,
            &fixture.originals,
            &[pos(0)],
            &fixture.candidates,
            &mut meter,
        ),
        Sweep::Retirement => row(
            owner,
            &fixture.originals,
            &[pos(0)],
            &[],
            &fixture.candidates,
            &mut meter,
        ),
    }
    .unwrap();
    assert!(owner.assign.iter().all(Option::is_none));
    assert!(owner.touched.is_empty());
    (hints, meter.consumed_work())
}

#[test]
fn retirement_preserves_reverse_chain_hints_and_charges_first_pass_honestly() {
    let fixture = reverse_chains(24, 24, 128);
    let (old_hints, old_work) = measured(&fixture, Sweep::Legacy);
    let (new_hints, new_work) = measured(&fixture, Sweep::Retirement);
    assert_eq!(old_hints, Some(fixture.expected[0].clone()));
    assert_eq!(new_hints, old_hints);
    assert!(
        new_work < old_work,
        "repeated long satisfied scans must disappear"
    );
    assert_eq!(measured(&fixture, Sweep::Retirement).1, new_work);

    // A one-pass miss gains nothing: its single retirement costs one honest
    // extra debit. This optimization is not a universal work decrease.
    let one_pass = Fixture {
        originals: vec![(1, vec![pos(0), neg(0)])],
        candidates: vec![1],
        expected: [vec![], vec![]],
        num_vars: 1,
    };
    let (old_hints, old_work) = measured(&one_pass, Sweep::Legacy);
    let (new_hints, new_work) = measured(&one_pass, Sweep::Retirement);
    assert_eq!((old_hints, new_hints), (None, None));
    assert_eq!(new_work, old_work + 1);
}

#[test]
fn opposite_rows_and_duplicate_positions_replay_independently() {
    let fixture = reverse_chains(4, 3, 7);
    let candidates: Vec<_> = fixture.candidates.iter().flat_map(|&id| [id, id]).collect();
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut owner = scratch(fixture.num_vars, &mut meter);
    let mut derived = Vec::new();
    let first_id = fixture.originals.len() as u64 + 1;
    for (index, target) in [pos(0), neg(0), pos(0), neg(0)].into_iter().enumerate() {
        let fresh = scratch(fixture.num_vars, &mut meter);
        let (expected, _) = legacy_row(
            fresh,
            &fixture.originals,
            &[target],
            &candidates,
            &mut meter,
        )
        .unwrap();
        let (actual, returned) = row(
            owner,
            &fixture.originals,
            &[target],
            &[],
            &candidates,
            &mut meter,
        )
        .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(actual.as_ref(), Some(&fixture.expected[index % 2]));
        assert!(returned.assign.iter().all(Option::is_none));
        assert!(returned.touched.is_empty());
        owner = returned;
        derived.push(RupStep {
            id: first_id + index as u64,
            clause: vec![target],
            rup_hints: actual.unwrap(),
        });
    }
    let empty_clause_id = first_id + derived.len() as u64;
    derived.push(RupStep {
        id: empty_clause_id,
        clause: vec![],
        rup_hints: vec![first_id, first_id + 1],
    });
    let dag = ResolutionDag {
        num_vars: fixture.num_vars,
        original_clauses: fixture.originals,
        derived,
        empty_clause_id,
    };
    assert_eq!(dag.validate_with_limits(&limits), Ok(()));
    for index in 0..4 {
        let mut corrupted = dag.clone();
        corrupted.derived[index].rup_hints.pop();
        assert!(corrupted.validate_with_limits(&limits).is_err());
    }
}

#[test]
fn retirement_cannot_replace_a_missing_conflicting_candidate() {
    let mut fixture = reverse_chains(6, 8, 32);
    let conflict = *fixture.expected[0].last().unwrap();
    fixture.candidates.retain(|&id| id != conflict);
    assert_eq!(measured(&fixture, Sweep::Legacy).0, None);
    assert_eq!(measured(&fixture, Sweep::Retirement).0, None);
}

#[test]
fn retirement_obeys_every_transient_stop_and_exact_work_boundary() {
    let fixture = reverse_chains(16, 16, 128);
    let run = |stop_at: usize, max_work: u64| {
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = max_work;
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            let owner = CompactionScratch::new(
                fixture.num_vars,
                CompactionScratch::planned_bytes(fixture.num_vars)?,
                &mut meter,
            )?;
            let (hints, owner) = row(
                owner,
                &fixture.originals,
                &[pos(0)],
                &[],
                &fixture.candidates,
                &mut meter,
            )?;
            assert_eq!(hints, Some(fixture.expected[0].clone()));
            assert!(owner.assign.iter().all(Option::is_none));
            assert!(owner.touched.is_empty());
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        (result, calls.get())
    };
    let (completed, polls) = run(usize::MAX, u64::MAX);
    let work = completed.unwrap();
    assert!(polls > 5);
    for stop_at in 1..=polls {
        let (result, calls) = run(stop_at, u64::MAX);
        assert!(matches!(result, Err(ResolutionValidationError::Cancelled)));
        assert_eq!(calls, stop_at, "a transient stop must not rearm the row");
    }
    assert_eq!(run(usize::MAX, work).0.unwrap(), work);
    assert!(matches!(
        run(usize::MAX, work - 1).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));
    assert_eq!(run(usize::MAX, u64::MAX).0.unwrap(), work);
}
