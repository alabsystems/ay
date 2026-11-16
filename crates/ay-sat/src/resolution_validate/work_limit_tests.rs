// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn replay_prefix_and_later_refusal_keep_exact_work_and_controls_with_either_probe() {
    for enabled in [false, true] {
        let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
            probe_cert_reject: enabled,
            ..Default::default()
        });
        let polls = Cell::new(0);
        let stop = Cell::new(true);
        let mut should_stop = || {
            polls.set(polls.get() + 1);
            stop.get()
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = 37;
        limits.deadline = Some(Instant::now());
        // Prefix admission precedes deadline and callback checks.
        assert!(matches!(
            WorkMeter::new(&limits, 38, &mut should_stop),
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                limit: 37,
                actual: 38,
            })
        ));
        assert_eq!(polls.get(), 0);

        limits.deadline = None;
        stop.set(false);
        let mut meter = WorkMeter::new(&limits, 37, &mut should_stop).unwrap();
        assert_eq!(polls.get(), 1);
        assert_eq!(
            meter.charge_usize(1),
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                limit: 37,
                actual: 38,
            })
        );
        assert_eq!(meter.consumed_work(), 38);
        assert_eq!(polls.get(), 1);
    }
}

#[test]
fn replay_control_crossing_and_overflow_remain_distinct_from_work_exhaustion() {
    let polls = Cell::new(0);
    let stop = Cell::new(false);
    let mut should_stop = || {
        polls.set(polls.get() + 1);
        stop.get()
    };
    let limits = ResolutionValidationLimits::unbounded();
    let mut meter = WorkMeter::new(&limits, 1_023, &mut should_stop).unwrap();
    stop.set(true);
    assert_eq!(
        meter.charge_usize(1),
        Err(ResolutionValidationError::Cancelled)
    );
    assert_eq!(meter.consumed_work(), 1_024);
    assert_eq!(polls.get(), 2);
    stop.set(false);
    let mut meter = WorkMeter::new(&limits, u64::MAX, &mut should_stop).unwrap();
    let before = polls.get();
    assert_eq!(
        meter.charge(1),
        Err(ResolutionValidationError::AccountingOverflow {
            resource: ResolutionValidationResource::Work,
        })
    );
    assert_eq!(meter.consumed_work(), u64::MAX);
    assert_eq!(polls.get(), before);
}
