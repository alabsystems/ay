// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::literal::Variable;
use std::cell::Cell;

mod fixture;
use fixture::{Fixture, Lane};

fn pos(variable: u32) -> Literal {
    Literal::positive(Variable::new(variable))
}

fn neg(variable: u32) -> Literal {
    Literal::negative(Variable::new(variable))
}

#[test]
fn repair_paths_are_exclusive_and_first_scratch_setup_is_compaction_work() {
    for lane in [Lane::Compaction, Lane::Rooted, Lane::Synthesis] {
        let fixture = Fixture::new(lane);
        let limits = ResolutionValidationLimits::unbounded();
        let mut stop = || false;
        let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
        let mut state = fixture.state();
        let result = fixture.repair(&mut state, &mut meter).unwrap().unwrap();
        assert_eq!(result, fixture.expected);
        fixture.replay(result);
        let snapshot = meter.attribution.snapshot(meter.consumed_work());
        assert_total(&snapshot, meter.consumed_work());
        assert!(snapshot.0.complete);
        assert_eq!(count(&snapshot, ConversionPhase::Other), 0);
        assert!(count(&snapshot, ConversionPhase::Compaction) > fixture.num_vars as u64);
        assert_eq!(
            count(&snapshot, ConversionPhase::RootSetup) > 0,
            !matches!(lane, Lane::Compaction)
        );
        assert_eq!(
            count(&snapshot, ConversionPhase::RootedRepair) > 0,
            !matches!(lane, Lane::Compaction)
        );
        assert_eq!(
            count(&snapshot, ConversionPhase::Synthesis) > 0,
            matches!(lane, Lane::Synthesis)
        );

        let before = meter.consumed_work();
        let second = fixture.repair(&mut state, &mut meter).unwrap().unwrap();
        assert_eq!(second, fixture.expected);
        let after = meter.attribution.snapshot(meter.consumed_work());
        assert_total(&after, meter.consumed_work());
        assert_eq!(
            count(&after, ConversionPhase::RootSetup),
            count(&snapshot, ConversionPhase::RootSetup),
            "cached root setup is not charged twice"
        );
        let first_compaction = count(&snapshot, ConversionPhase::Compaction);
        let second_compaction = count(&after, ConversionPhase::Compaction) - first_compaction;
        assert_eq!(
            first_compaction - second_compaction,
            fixture.num_vars as u64,
            "only the first row constructs the zeroed assignment scratch"
        );
        assert!(meter.consumed_work() > before);
    }
}

#[test]
fn every_repair_stop_and_one_short_work_cap_keep_exact_partition_and_refusal() {
    for lane in [Lane::Compaction, Lane::Rooted, Lane::Synthesis] {
        let fixture = Fixture::new(lane);
        let limits = ResolutionValidationLimits::unbounded();
        let polls = Cell::new(0);
        let mut stop = || {
            polls.set(polls.get() + 1);
            false
        };
        let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
        fixture
            .repair(&mut fixture.state(), &mut meter)
            .unwrap()
            .unwrap();
        let work = meter.consumed_work();
        let poll_count = polls.get();
        assert!(work > 0 && poll_count > 1);
        for ordinal in 2..=poll_count {
            let seen = Cell::new(0);
            let mut stop = || {
                seen.set(seen.get() + 1);
                seen.get() == ordinal
            };
            let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
            assert_eq!(
                fixture.repair(&mut fixture.state(), &mut meter),
                Err(ResolutionValidationError::Cancelled)
            );
            assert_eq!(
                seen.get(),
                ordinal,
                "phase exit cannot resume a cancelled operation"
            );
            assert_eq!(meter.attribution.phase, ConversionPhase::Other);
            assert_total(
                &meter.attribution.snapshot(meter.consumed_work()),
                meter.consumed_work(),
            );
        }
        for cap in [work, work - 1] {
            let mut limits = limits.clone();
            limits.max_work = cap;
            let mut stop = || false;
            let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
            let result = fixture.repair(&mut fixture.state(), &mut meter);
            if cap == work {
                assert_eq!(result.unwrap(), Some(fixture.expected.clone()));
            } else {
                assert_eq!(
                    result,
                    Err(ResolutionValidationError::LimitExceeded {
                        resource: ResolutionValidationResource::Work,
                        limit: u128::from(cap),
                        actual: u128::from(work),
                    })
                );
            }
            assert_total(&meter.attribution.snapshot(meter.consumed_work()), work);
        }
    }
}

#[test]
fn terminal_empty_synthesis_is_attributed_including_failed_premise_context() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![pos(0), pos(1)], true);
    trace.add_clause(2, vec![neg(1)], true);
    trace.mark_empty();
    let originals = vec![(1, vec![pos(0), pos(1)]), (2, vec![neg(1)])];
    for premise in [neg(0), pos(0)] {
        let limits = ResolutionValidationLimits::unbounded();
        let mut stop = || false;
        let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
        let fixture = Fixture::new(Lane::Compaction);
        let mut state = fixture.state();
        let inputs = DerivedConversionInputs {
            entries: trace.entries(),
            original_clauses: &originals,
            unit_premises: &[premise],
            terminal_empty_index: None,
            shape: TraceShape {
                synthesis_scratch_bytes: planned_synthesis_scratch_bytes(2, 0).unwrap(),
                ..TraceShape::default()
            },
            num_vars: 2,
        };
        let result = append_synthesized_terminal(&inputs, &mut state, &mut meter);
        if premise == neg(0) {
            result.unwrap();
            assert_eq!(state.steps[0].rup_hints, vec![1, 2]);
            let mut replay_stop = || false;
            ResolutionDag {
                num_vars: 2,
                original_clauses: originals.clone(),
                derived: state.steps,
                empty_clause_id: state.empty_clause_id.unwrap(),
            }
            .validate_with_limits_interruptible(&limits, &[premise], 0, 0, &mut replay_stop)
            .unwrap();
        } else {
            assert_eq!(
                result,
                Err(ClauseTraceResolutionError::UnitPremisesDoNotRefuteTrace)
            );
            assert!(state.steps.is_empty());
        }
        let snapshot = meter.attribution.snapshot(meter.consumed_work());
        assert!(meter.consumed_work() > 0);
        assert_total(&snapshot, meter.consumed_work());
        assert_eq!(
            count(&snapshot, ConversionPhase::Synthesis),
            meter.consumed_work()
        );
        assert_eq!(count(&snapshot, ConversionPhase::Other), 0);
    }
}

#[test]
fn public_conversion_and_replay_keep_proof_work_and_poll_count_with_probe_on_or_off() {
    let fixture = Fixture::new(Lane::Rooted);
    let mut previous = None;
    for enabled in [false, true] {
        let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
            probe_cert_reject: enabled,
            ..Default::default()
        });
        let polls = Cell::new(0);
        let converted = validate_clause_trace_resolution_interruptible(
            &fixture.trace,
            fixture.num_vars,
            &ResolutionValidationLimits::unbounded(),
            || {
                polls.set(polls.get() + 1);
                false
            },
        )
        .unwrap();
        converted.dag().validate().unwrap();
        let result = (
            converted.dag().derived[0].rup_hints.clone(),
            converted.validation_work(),
            polls.get(),
        );
        if let Some(expected) = &previous {
            assert_eq!(&result, expected);
        }
        assert_eq!(result.0, fixture.expected);
        previous = Some(result);
    }
}
