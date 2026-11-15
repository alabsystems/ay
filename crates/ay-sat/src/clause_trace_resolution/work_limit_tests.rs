// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn conversion_work_refusal_keeps_payload_debit_and_poll_order_with_probe_on_or_off() {
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
        meter.charge(1_023).unwrap();
        assert_eq!(polls.get(), 1);
        stop.set(true);
        // Work refusal has always preceded the poll at this crossing.
        assert_eq!(
            meter.charge(1),
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                limit: 1_023,
                actual: 1_024,
            })
        );
        assert_eq!(meter.consumed_work(), 1_024);
        assert_eq!(polls.get(), 1);
    }
}

#[test]
fn conversion_control_and_overflow_failures_keep_their_original_priority() {
    let polls = Cell::new(0);
    let stop = Cell::new(false);
    let mut should_stop = || {
        polls.set(polls.get() + 1);
        stop.get()
    };
    let limits = ResolutionValidationLimits::unbounded();
    let mut meter = ConversionMeter::new(&limits, &mut should_stop).unwrap();
    stop.set(true);
    assert_eq!(
        meter.charge(1_024),
        Err(ResolutionValidationError::Cancelled)
    );
    assert_eq!(meter.consumed_work(), 1_024);
    assert_eq!(polls.get(), 2);
    drop(meter);

    stop.set(false);
    let mut meter = ConversionMeter::new(&limits, &mut should_stop).unwrap();
    meter.work = u64::MAX;
    let before = polls.get();
    assert_eq!(
        meter.charge(1),
        Err(ResolutionValidationError::AccountingOverflow {
            resource: ResolutionValidationResource::Work,
        })
    );
    assert_eq!(meter.consumed_work(), u64::MAX);
    assert_eq!(polls.get(), before);
    drop(meter);

    let mut expired = limits;
    expired.deadline = Some(Instant::now());
    assert!(matches!(
        ConversionMeter::new(&expired, &mut should_stop),
        Err(ResolutionValidationError::DeadlineExceeded)
    ));
    assert_eq!(polls.get(), before);
}
