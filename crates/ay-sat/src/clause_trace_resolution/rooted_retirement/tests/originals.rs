// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn original_retirement_reuses_only_cursor_capacity_and_checked_layout() {
    assert_eq!(size_of::<RetiredOriginals>(), size_of::<Vec<u32>>());
    assert_eq!(RetiredOriginals::layout(1, 3), Some(3));
    assert_eq!(RetiredOriginals::layout(32, 3), Some(3));
    assert_eq!(RetiredOriginals::layout(33, 5), Some(5));
    assert_eq!(RetiredOriginals::layout(33, 4), None);
    assert_eq!(RetiredOriginals::layout(usize::MAX, usize::MAX), None);
    assert_eq!(RetiredOriginals::layout(0, 99), None);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let cursor = vec![77; 17];
    let pointer = cursor.as_ptr();
    let capacity = cursor.capacity();
    let mut retired = RetiredOriginals::from_cursor(cursor, 65, &mut meter).unwrap();
    assert_eq!(retired.0.as_ptr(), pointer, "no replacement allocation");
    assert_eq!(retired.0.capacity(), capacity);
    assert_eq!(retired.0.len(), 7);
    assert!(retired.is_clear());
    for position in [0, 31, 32, 64, 0] {
        retired.mark(position, &mut meter).unwrap();
        assert!(retired.contains(position, &mut meter).unwrap());
    }
    assert_eq!(retired.0[0], 3, "one trail entry per nonzero bitmap word");
    assert!(!retired.contains(1, &mut meter).unwrap());
    assert!(!retired.contains(usize::MAX, &mut meter).unwrap());
    let prepaid = meter.consumed_work();
    retired.clear();
    retired.clear();
    assert!(retired.is_clear());
    assert_eq!(meter.consumed_work(), prepaid, "reset was prepaid");
    assert_eq!(retired.0.as_ptr(), pointer);
    let mut declined = RetiredOriginals::from_cursor(vec![9; 3], 33, &mut meter).unwrap();
    let before = meter.consumed_work();
    declined.mark(0, &mut meter).unwrap();
    assert!(!declined.contains(0, &mut meter).unwrap());
    assert_eq!(declined.0.len(), 0);
    assert_eq!(
        meter.consumed_work(),
        before,
        "disabled lookup is the old path"
    );
}

#[test]
fn original_retirement_initialization_and_mutation_stop_exactly_without_dirty_reset() {
    let run = |stop_at, max_work| {
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = max_work;
        let mut retired = RetiredOriginals::default();
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            retired = RetiredOriginals::from_cursor(vec![99; 9], 96, &mut meter)?;
            for position in [0, 1, 32, 64] {
                retired.mark(position, &mut meter)?;
                assert!(retired.contains(position, &mut meter)?);
            }
            meter.check_controls()?;
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        retired.clear();
        assert!(retired.is_clear());
        (result, calls.get())
    };
    let (success, polls) = run(usize::MAX, u64::MAX);
    let work = success.unwrap();
    assert!(polls > 3);
    for stop_at in 1..=polls {
        let (result, calls) = run(stop_at, u64::MAX);
        assert!(matches!(result, Err(ResolutionValidationError::Cancelled)));
        assert_eq!(calls, stop_at);
    }
    assert_eq!(run(usize::MAX, work).0.unwrap(), work);
    for allowance in 0..work {
        assert!(matches!(
            run(usize::MAX, allowance).0,
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                ..
            })
        ));
    }
}
