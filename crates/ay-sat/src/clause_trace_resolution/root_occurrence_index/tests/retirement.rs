// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn retained_cursor_initialization_finishes_before_any_csr_publication() {
    let originals: Vec<_> = (1..=33).map(|id| (id, vec![pos(0), neg(1)])).collect();
    let admitted = planned_bytes(3, 33, 66).unwrap();
    let run = |stop_at: usize, work: u64, bytes: usize| {
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = work;
        let mut root = empty_root(3);
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            build(&mut root, &originals, 3, bytes, &mut meter)?;
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        if result.is_err() {
            assert!(root.index_heads.is_none());
            assert_eq!(root.index_items.len(), 0);
            assert!(root.index_retired.is_clear());
        }
        (result, calls.get(), root)
    };
    let (complete, polls, mut root) = run(usize::MAX, u64::MAX, admitted);
    let work = complete.unwrap();
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    root.index_retired.mark(32, &mut meter).unwrap();
    assert!(
        !root.index_retired.is_clear(),
        "the complete two-word layout was retained"
    );
    root.index_retired.clear();
    for stop_at in 1..=polls {
        let (result, calls, _) = run(stop_at, u64::MAX, admitted);
        assert_eq!(result, Err(ResolutionValidationError::Cancelled));
        assert_eq!(calls, stop_at);
    }
    assert_eq!(run(usize::MAX, work, admitted).0, Ok(work));
    assert!(matches!(
        run(usize::MAX, work - 1, admitted).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));
    assert!(matches!(
        run(usize::MAX, u64::MAX, admitted - 1).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
}

#[test]
fn retained_cursor_uses_the_existing_peak_even_with_candidate_scheduler() {
    let shape = TraceShape {
        original_clauses: 33,
        original_literals: 66,
        max_row_hints: 4,
        candidate_scheduler_bytes: 1234,
        ..TraceShape::default()
    };
    let peaks = planned_trace_peaks(shape, 3, 4, 0, 0, 0).unwrap();
    let root_bytes = (7 + 66 + 7) * size_of::<u32>() + 3 * size_of::<Vec<u32>>();
    assert_eq!(peaks.shape.root_index_scratch_bytes, root_bytes);
    assert_eq!(
        peaks.conversion,
        planned_retained_bytes(peaks.shape, 0).unwrap()
            + peaks.shape.synthesis_scratch_bytes
            + peaks.shape.compaction_scratch_bytes
            + root_bytes
            + 1234
    );
    let invalid = vec![(1, vec![pos(0), pos(99)])];
    let mut root = empty_root(3);
    root.assign[0] = Some(true);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    assert!(build(
        &mut root,
        &invalid,
        3,
        planned_bytes(3, 1, 2).unwrap(),
        &mut meter
    )
    .is_err());
    assert!(
        root.index_heads.is_none(),
        "satisfied malformed tails remain rejected"
    );
    assert_eq!(root.index_items.len(), 0);
    assert!(root.index_retired.is_clear());
}
