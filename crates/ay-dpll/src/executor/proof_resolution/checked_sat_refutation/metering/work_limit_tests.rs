// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn outer_work_refusal_keeps_payload_and_precedes_bytes_with_probe_on_or_off() {
    for enabled in [false, true] {
        let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
            probe_cert_reject: enabled,
            ..Default::default()
        });
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = 3;
        limits.max_bytes = 5;
        let mut meter = CheckedRefutationMeter::new(limits, None, None).unwrap();
        meter.charge(3, 5).unwrap();
        // The refused work debit is recorded; the byte debit is not attempted.
        assert_eq!(
            meter.charge(1, usize::MAX),
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                limit: 3,
                actual: 4,
            })
        );
        assert_eq!((meter.work, meter.bytes), (4, 5));
    }
}

#[test]
fn outer_controls_precede_debits_and_overflow_and_bytes_keep_their_errors() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let mut limits = ResolutionValidationLimits::unbounded();
    limits.max_work = 0;
    let mut meter = CheckedRefutationMeter::new(limits, Some(interrupt.clone()), None).unwrap();
    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(
        meter.charge(1, 1),
        Err(ResolutionValidationError::Cancelled)
    );
    assert_eq!((meter.work, meter.bytes), (0, 0));
    // Deadline remains ahead of even an already-fired interrupt.
    meter.limits.deadline = Some(ay_core::time::Instant::now());
    assert_eq!(
        meter.charge(1, 1),
        Err(ResolutionValidationError::DeadlineExceeded)
    );
    assert_eq!((meter.work, meter.bytes), (0, 0));

    let mut meter = CheckedRefutationMeter::unbounded();
    meter.work = u64::MAX;
    assert_eq!(
        meter.charge(1, 1),
        Err(ResolutionValidationError::AccountingOverflow {
            resource: ResolutionValidationResource::Work,
        })
    );
    assert_eq!((meter.work, meter.bytes), (u64::MAX, 0));

    let mut meter = CheckedRefutationMeter::unbounded();
    meter.limits.max_bytes = 0;
    assert_eq!(
        meter.charge(1, 1),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            limit: 0,
            actual: 1,
        })
    );
    assert_eq!((meter.work, meter.bytes), (1, 1));
}
