// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn original_retirement_every_row_stop_and_exact_work_boundary_clean_prepaid_marks() {
    let (originals, target) = noisy_originals(32);
    let run = |stop_at: usize, max_work: u64| {
        let mut root = root_for(&originals, 34);
        let calls = Cell::new(0usize);
        let mut stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = max_work;
        let result = (|| {
            let mut meter = ConversionMeter::new(&limits, &mut stop)?;
            assert_eq!(
                repair(&mut root, &originals, &target, &mut meter)?,
                Some(vec![2])
            );
            Ok::<_, ResolutionValidationError>(meter.consumed_work())
        })();
        assert_clean(&root);
        (result, calls.get())
    };
    let (complete, polls) = run(usize::MAX, u64::MAX);
    let work = complete.unwrap();
    assert!(polls > 3);
    for stop_at in 1..=polls {
        let (result, calls) = run(stop_at, u64::MAX);
        assert_eq!(result, Err(ResolutionValidationError::Cancelled));
        assert_eq!(calls, stop_at, "no restart after an observed stop");
    }
    assert_eq!(run(usize::MAX, work).0, Ok(work));
    // Includes failure immediately before every possible mark/reset precharge.
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

#[test]
fn original_retirement_hint_decline_and_opposed_root_fallback_restore_scratch() {
    let mut originals = originals();
    originals.push((7, vec![pos(5)]));
    let mut root = root_for(&originals, 6);
    let baseline = root.assign.clone();
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    assert!(
        !root.index_items.contains(&6),
        "root-satisfied clause stays filtered"
    );
    assert_eq!(
        compact_rup_hint_candidates_rooted(
            &mut root,
            &originals,
            &[],
            &[pos(0)],
            &[],
            0,
            0,
            0,
            &mut meter,
        )
        .unwrap(),
        None,
        "cone-cap decline follows actual CSR propagation"
    );
    assert_eq!(root.assign, baseline);
    assert!(root.index_retired.is_clear());
    assert_eq!(
        repair(&mut root, &originals, &[pos(5)], &mut meter).unwrap(),
        None
    );
    assert_eq!(root.assign, baseline);
    assert!(root.index_retired.is_clear());
    assert_eq!(
        synthesize_rup_hints(
            &originals,
            &[],
            &[pos(5)],
            &[],
            6,
            7,
            0,
            planned_synthesis_scratch_bytes(6, 7).unwrap(),
            &mut meter,
        )
        .unwrap(),
        Some(vec![7])
    );
    assert_eq!(
        repair(&mut root, &originals, &[neg(0)], &mut meter).unwrap(),
        Some(vec![4, 5, 6])
    );
    assert_eq!(root.assign, baseline);
    assert!(root.index_retired.is_clear());
    assert_eq!(root.row_trail.len(), 0);
    assert!(root.cand_reason.iter().all(|&reason| reason == 0));
    let mut expired = ResolutionValidationLimits::unbounded();
    expired.deadline = Some(Instant::now());
    assert_eq!(
        ConversionMeter::new(&expired, &mut stop).err(),
        Some(ResolutionValidationError::DeadlineExceeded)
    );
    assert_eq!(root.assign, baseline);
}
