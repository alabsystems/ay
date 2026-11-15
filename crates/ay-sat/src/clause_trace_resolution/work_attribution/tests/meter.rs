// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn nested_scopes_restore_after_none_and_error_without_control_calls() {
    let polls = Cell::new(0);
    let mut stop = || {
        polls.set(polls.get() + 1);
        false
    };
    let limits = ResolutionValidationLimits::unbounded();
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    meter.charge(2).unwrap();
    let result: Result<(), ResolutionValidationError> =
        meter.in_phase(ConversionPhase::Derived, |meter| {
            meter.charge(3)?;
            let result: Option<()> = meter.in_phase(ConversionPhase::Compaction, |meter| {
                meter.charge(5).unwrap();
                None
            });
            assert_eq!(result, None);
            assert_eq!(meter.attribution.phase, ConversionPhase::Derived);
            meter.charge(7)?;
            meter.in_phase(ConversionPhase::Synthesis, |meter| {
                meter.charge(11)?;
                Err(ResolutionValidationError::Cancelled)
            })
        });
    assert_eq!(result, Err(ResolutionValidationError::Cancelled));
    assert_eq!(meter.attribution.phase, ConversionPhase::Other);
    meter.charge(13).unwrap();
    let snapshot = meter.attribution.snapshot(meter.consumed_work());
    assert_total(&snapshot, 41);
    assert_eq!(count(&snapshot, ConversionPhase::Other), 15);
    assert_eq!(count(&snapshot, ConversionPhase::Derived), 10);
    assert_eq!(count(&snapshot, ConversionPhase::Compaction), 5);
    assert_eq!(count(&snapshot, ConversionPhase::Synthesis), 11);
    assert_eq!(polls.get(), 1, "phase boundaries do not poll");
}

#[test]
fn failing_debit_is_in_active_phase_before_restoration_with_probe_on_or_off() {
    for enabled in [false, true] {
        let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
            probe_cert_reject: enabled,
            ..Default::default()
        });
        let polls = Cell::new(0);
        let stop = Cell::new(false);
        let mut should_stop = || {
            polls.set(polls.get() + 1);
            stop.get()
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = 1_023;
        let mut meter = ConversionMeter::new(&limits, &mut should_stop).unwrap();
        meter.charge(3).unwrap();
        let error = meter.in_phase(ConversionPhase::Derived, |meter| {
            meter.charge(1_020).unwrap();
            stop.set(true);
            meter.in_phase(ConversionPhase::RootedRepair, |meter| {
                let result = meter.charge(1);
                let snapshot = meter.attribution.snapshot(meter.consumed_work());
                assert_total(&snapshot, 1_024);
                assert_eq!(snapshot.0.phase, ConversionPhase::RootedRepair);
                assert_eq!(count(&snapshot, ConversionPhase::Other), 3);
                assert_eq!(count(&snapshot, ConversionPhase::Derived), 1_020);
                assert_eq!(count(&snapshot, ConversionPhase::RootedRepair), 1);
                result
            })
        });
        assert_eq!(
            error,
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                limit: 1_023,
                actual: 1_024,
            })
        );
        assert_eq!(polls.get(), 1, "work refusal precedes the crossing poll");
        assert_eq!(meter.attribution.phase, ConversionPhase::Other);
        assert_total(&meter.attribution.snapshot(meter.consumed_work()), 1_024);
    }
}

#[test]
fn exact_limit_zero_debit_cancellation_and_overflow_keep_original_order() {
    let polls = Cell::new(0);
    let stop = Cell::new(false);
    let mut should_stop = || {
        polls.set(polls.get() + 1);
        stop.get()
    };
    let mut limits = ResolutionValidationLimits::unbounded();
    limits.max_work = 1_024;
    let mut meter = ConversionMeter::new(&limits, &mut should_stop).unwrap();
    meter
        .in_phase(ConversionPhase::Preflight, |meter| meter.charge(1_024))
        .unwrap();
    assert_eq!(polls.get(), 2);
    meter
        .in_phase(ConversionPhase::Finalize, |meter| meter.charge(0))
        .unwrap();
    assert_eq!(polls.get(), 2);
    assert_total(&meter.attribution.snapshot(meter.consumed_work()), 1_024);

    let limits = ResolutionValidationLimits::unbounded();
    let mut meter = ConversionMeter::new(&limits, &mut should_stop).unwrap();
    stop.set(true);
    assert_eq!(
        meter.in_phase(ConversionPhase::Synthesis, |meter| meter.charge(1_024)),
        Err(ResolutionValidationError::Cancelled)
    );
    assert_eq!(polls.get(), 4);
    let snapshot = meter.attribution.snapshot(meter.consumed_work());
    assert_total(&snapshot, 1_024);
    assert_eq!(count(&snapshot, ConversionPhase::Synthesis), 1_024);

    stop.set(false);
    let mut meter = ConversionMeter::new(&limits, &mut should_stop).unwrap();
    meter.work = u64::MAX;
    let before = polls.get();
    assert_eq!(
        meter.in_phase(ConversionPhase::Compaction, |meter| meter.charge(1)),
        Err(ResolutionValidationError::AccountingOverflow {
            resource: ResolutionValidationResource::Work,
        })
    );
    assert_eq!(polls.get(), before);
    assert_total(&meter.attribution.snapshot(meter.consumed_work()), u64::MAX);

    let mut expired = limits;
    expired.deadline = Some(Instant::now());
    assert!(matches!(
        ConversionMeter::new(&expired, &mut should_stop),
        Err(ResolutionValidationError::DeadlineExceeded)
    ));
    assert_eq!(polls.get(), before);
}
