// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::literal::Variable;
use std::cell::Cell;

mod oracle {
    use super::*;
    include!("oracle.rs");
}
mod resources {
    use super::*;
    include!("resources.rs");
}

fn pos(variable: u32) -> Literal {
    Literal::positive(Variable::new(variable))
}

fn neg(variable: u32) -> Literal {
    Literal::negative(Variable::new(variable))
}

struct Fixture {
    originals: Vec<(u64, Vec<Literal>)>,
    derived: Vec<RupStep>,
    num_vars: usize,
    expected: [Vec<u64>; 2],
}

fn fixture(length: u32, noise: usize, width: usize) -> Fixture {
    assert!(length >= 2 && noise > 0);
    let mut originals = Vec::new();
    for _ in 0..noise {
        let mut clause = vec![pos(0); width];
        clause.push(neg(0));
        originals.push((originals.len() as u64 + 1, clause));
    }
    let mut starts = Vec::new();
    for guard in [pos(0), neg(0)] {
        let start = originals.len() as u64 + 1;
        starts.push(start);
        originals.push((start, vec![guard, neg(length), pos(length + 1)]));
        originals.push((start + 1, vec![guard, neg(length), neg(length + 1)]));
        for variable in (1..length).rev() {
            originals.push((
                originals.len() as u64 + 1,
                vec![guard, neg(variable), pos(variable + 1)],
            ));
        }
        originals.push((originals.len() as u64 + 1, vec![guard, pos(1)]));
    }
    let first_derived = originals.len() as u64 + 1;
    let mut derived = vec![RupStep {
        id: first_derived,
        clause: originals[0].1.clone(),
        rup_hints: vec![1],
    }];
    let mut expected = [Vec::new(), Vec::new()];
    for (branch, guard) in [pos(0), neg(0)].into_iter().enumerate() {
        let start = starts[branch];
        let seed = start + u64::from(length) + 1;
        let shortcut = first_derived + branch as u64 + 1;
        derived.push(RupStep {
            id: shortcut,
            clause: vec![guard, pos(2)],
            rup_hints: vec![seed, seed - 1],
        });
        // The shortcut is an already-proved database clause. Its literal
        // depends on the guard, not on the seed used to prove that earlier
        // clause, so the current conflict cone must omit the seed.
        expected[branch].push(shortcut);
        expected[branch].extend((start + 2..seed - 1).rev());
        expected[branch].extend([start, start + 1]);
    }
    Fixture {
        originals,
        derived,
        num_vars: length as usize + 2,
        expected,
    }
}

fn synthesize(
    fixture: &Fixture,
    target: &[Literal],
    premises: &[Literal],
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    synthesize_rup_hints(
        &fixture.originals,
        &fixture.derived,
        target,
        premises,
        fixture.num_vars,
        usize::MAX,
        0,
        planned_synthesis_scratch_bytes(fixture.num_vars, 0)?,
        meter,
    )
}

enum Sweep {
    Legacy,
    Retirement,
}

#[cfg(test)]
fn measured(fixture: &Fixture, sweep: Sweep) -> (Option<Vec<u64>>, u64) {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let result = match sweep {
        Sweep::Legacy => oracle::synthesize(fixture, &[pos(0)], &mut meter),
        Sweep::Retirement => synthesize(fixture, &[pos(0)], &[], &mut meter),
    }
    .unwrap();
    (result, meter.consumed_work())
}

#[test]
fn synthesis_retirement_preserves_mixed_reverse_chain_and_saves_satisfied_scans() {
    let fixture = fixture(24, 24, 128);
    let (expected, old_work) = measured(&fixture, Sweep::Legacy);
    let (actual, new_work) = measured(&fixture, Sweep::Retirement);
    assert_eq!(expected, Some(fixture.expected[0].clone()));
    assert_eq!(actual, expected);
    assert!(
        new_work < old_work,
        "includes bitmap setup, reads, marks and reset"
    );
    assert_eq!(measured(&fixture, Sweep::Retirement).1, new_work);

    let one_pass = Fixture {
        originals: vec![(1, vec![pos(0), neg(0)])],
        derived: vec![],
        num_vars: 1,
        expected: [vec![], vec![]],
    };
    let (old_result, old_work) = measured(&one_pass, Sweep::Legacy);
    let (new_result, new_work) = measured(&one_pass, Sweep::Retirement);
    assert_eq!((old_result, new_result), (None, None));
    assert_eq!(
        new_work,
        old_work + 5,
        "one layout, read, two mark, one reset debits"
    );
}

#[test]
fn synthesis_retirement_keeps_reasons_order_and_clears_before_reuse() {
    let fixture = fixture(4, 10, 7);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut state = prepare_synthesis_state(fixture.num_vars, 0, usize::MAX, &mut meter).unwrap();
    let pointer = state.in_cone.as_ptr();
    let capacity = state.in_cone.capacity();
    for target in [pos(0), neg(0), pos(0)] {
        state.assign.fill(None);
        state.reason.fill(0);
        state.order.clear();
        assert!(state.in_cone.iter().all(|&byte| byte == 0));
        seed_synthesis_assignment(
            &mut state.assign,
            &[],
            &[target],
            fixture.num_vars,
            &mut meter,
        )
        .unwrap();
        let mut old_assign = state.assign.clone();
        let mut old_reason = state.reason.clone();
        let mut old_order = Vec::new();
        let expected = oracle::sweep(
            &fixture.originals,
            &fixture.derived,
            &mut old_assign,
            &mut old_reason,
            &mut old_order,
            &mut meter,
        )
        .unwrap();
        let actual = sweep_synthesis_database(
            &fixture.originals,
            &fixture.derived,
            &mut state.assign,
            &mut state.reason,
            &mut state.order,
            &mut state.in_cone,
            &mut meter,
        )
        .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(state.assign, old_assign);
        assert_eq!(state.reason, old_reason);
        assert_eq!(state.order, old_order);
        assert!(state.in_cone.iter().all(|&byte| byte == 0));
        assert_eq!(
            (state.in_cone.as_ptr(), state.in_cone.capacity()),
            (pointer, capacity)
        );
    }
}

#[cfg(test)]
fn completed_dag(fixture: &Fixture) -> ResolutionDag {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut derived = fixture.derived.clone();
    let first = fixture.originals.len() as u64 + derived.len() as u64 + 1;
    for (index, target) in [pos(0), neg(0), pos(0)].into_iter().enumerate() {
        let hints = synthesize(fixture, &[target], &[], &mut meter)
            .unwrap()
            .unwrap();
        assert_eq!(hints, fixture.expected[index % 2]);
        derived.push(RupStep {
            id: first + index as u64,
            clause: vec![target],
            rup_hints: hints,
        });
    }
    let empty_clause_id = first + 3;
    derived.push(RupStep {
        id: empty_clause_id,
        clause: vec![],
        rup_hints: vec![first, first + 1],
    });
    ResolutionDag {
        num_vars: fixture.num_vars,
        original_clauses: fixture.originals.clone(),
        derived,
        empty_clause_id,
    }
}

#[test]
fn synthesis_retirement_replays_independently_and_repairs_incomplete_public_hints() {
    let fixture = fixture(4, 10, 7);
    assert_eq!(
        fixture.expected,
        [vec![24, 14, 13, 11, 12], vec![25, 20, 19, 17, 18]]
    );
    let limits = ResolutionValidationLimits::unbounded();
    let dag = completed_dag(&fixture);
    assert_eq!(dag.validate_with_limits(&limits), Ok(()));
    for index in fixture.derived.len()..fixture.derived.len() + 3 {
        let mut corrupted = dag.clone();
        corrupted.derived[index].rup_hints.pop();
        assert!(corrupted.validate_with_limits(&limits).is_err());
    }
    let mut corrupted = dag.clone();
    corrupted.derived[fixture.derived.len()].rup_hints[1] = u64::MAX;
    assert!(corrupted.validate_with_limits(&limits).is_err());

    let mut trace = ClauseTrace::new();
    for (id, clause) in &dag.original_clauses {
        trace.add_clause(*id, clause.clone(), true);
    }
    for step in &dag.derived {
        let hints = if step.id == dag.empty_clause_id {
            // The assumption-free boundary rejects empty hint lists. Supply
            // only the earlier tautology: neither compaction nor its rooted
            // repair can conflict, so full synthesis must recover [26, 27].
            vec![fixture.derived[0].id]
        } else {
            step.rup_hints.clone()
        };
        trace.add_clause_with_hints(step.id, step.clause.clone(), false, hints);
    }
    let checked = validate_clause_trace_resolution(&trace, fixture.num_vars, &limits).unwrap();
    assert_eq!(
        checked.dag().derived.last().unwrap().rup_hints,
        vec![26, 27]
    );
    assert_eq!(checked.dag().validate_with_limits(&limits), Ok(()));
}

#[test]
fn synthesis_retirement_layout_declines_without_allocating_or_changing_fallback() {
    assert_eq!(SynthesisRetirement::layout(0, 0, 0), Some(0));
    assert_eq!(SynthesisRetirement::layout(8, 0, 1), Some(1));
    assert_eq!(SynthesisRetirement::layout(8, 1, 2), Some(2));
    assert_eq!(SynthesisRetirement::layout(8, 1, 1), None);
    assert_eq!(SynthesisRetirement::layout(usize::MAX, 1, usize::MAX), None);
    assert_eq!(SynthesisRetirement::layout(usize::MAX, 0, usize::MAX), None);
    let fixture = Fixture {
        originals: (1..=17)
            .map(|id| (id, vec![pos(0), neg(0)]))
            .chain([(18, vec![neg(0)])])
            .collect(),
        derived: vec![],
        num_vars: 2,
        expected: [vec![], vec![]],
    };
    let (old, old_work) = measured(&fixture, Sweep::Legacy);
    let (new, new_work) = measured(&fixture, Sweep::Retirement);
    assert_eq!((old, new), (None, None));
    assert_eq!(
        new_work,
        old_work + 1,
        "only the charged layout decision differs"
    );
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut bytes = [0xa5; 2];
    let mut retired = SynthesisRetirement::new(&mut bytes, 17, 1, &mut meter).unwrap();
    assert_eq!(retired.0.len(), 0);
    assert!(!retired.contains(0, &mut meter).unwrap());
    retired.mark(0, &mut meter).unwrap();
    retired.clear(&mut meter).unwrap();
    assert_eq!(bytes, [0xa5; 2]);
}

#[test]
fn synthesis_retirement_bitmap_spans_the_original_derived_byte_boundary() {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut bytes = [0, 0, 0xa5];
    let pointer = bytes.as_ptr();
    for _ in 0..3 {
        let mut retired = SynthesisRetirement::new(&mut bytes, 8, 1, &mut meter).unwrap();
        assert_eq!(retired.0.as_ptr(), pointer);
        assert_eq!(retired.0.len(), 2);
        for position in [0, 7, 8] {
            retired.mark(position, &mut meter).unwrap();
            assert!(retired.contains(position, &mut meter).unwrap());
        }
        assert!(!retired.contains(6, &mut meter).unwrap());
        assert_eq!(retired.0, &[0x81, 1]);
        retired.clear(&mut meter).unwrap();
        assert_eq!(bytes, [0, 0, 0xa5], "only the borrowed prefix is cleared");
    }
}

#[test]
fn synthesis_retirement_does_not_invent_conflict_or_widen_the_hint_cap() {
    let mut fixture = fixture(4, 10, 7);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    assert_eq!(
        synthesize_rup_hints(
            &fixture.originals,
            &fixture.derived,
            &[pos(0)],
            &[],
            fixture.num_vars,
            fixture.expected[0].len() - 1,
            0,
            planned_synthesis_scratch_bytes(fixture.num_vars, 0).unwrap(),
            &mut meter,
        )
        .unwrap(),
        None
    );
    let expected = Some(fixture.expected[0].clone());
    assert_eq!(
        synthesize(&fixture, &[], &[neg(0)], &mut meter).unwrap(),
        expected
    );
    // Replace only the active branch's conflict by another satisfied clause;
    // IDs remain canonical and the existing shortcut proofs remain valid.
    fixture.originals[11].1 = vec![pos(0), neg(0)];
    assert_eq!(measured(&fixture, Sweep::Legacy).0, None);
    assert_eq!(measured(&fixture, Sweep::Retirement).0, None);
    assert_eq!(
        synthesize(&fixture, &[neg(0)], &[], &mut meter).unwrap(),
        Some(fixture.expected[1].clone()),
        "the opposite row remains independent"
    );
}
