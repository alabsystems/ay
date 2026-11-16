// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn exact_and_one_short_fill_work_and_bytes_are_cumulative_and_sticky() {
    let end = Instant::now() + Duration::from_secs(20);
    let dst = base(0, &[(0, 7)]);
    let target = base(0, &[(0, 7), (1, 9), (2, 9)]);
    let value = literal(9);
    let work = Cell::new(0u64);
    let bytes = Cell::new(0usize);
    assert!(target
        .confirms_range_fill_with_progress(&dst, 1, 3, &value, &mut |w, b| {
            work.set(work.get() + w as u64);
            bytes.set(bytes.get() + b);
            Instant::now() < end
        })
        .expect("actual offers"));
    assert!(confirm(
        &owner(end, work.get(), bytes.get()),
        &target,
        &dst,
        1,
        3,
        &value
    ));
    for (w, b) in [
        (work.get() - 1, bytes.get()),
        (work.get(), bytes.get() - 1),
        (0, 0),
    ] {
        let owner = owner(end, w, b);
        let retained = owner.clone();
        assert!(owner
            .with_work(|work| target
                .confirms_range_fill_with_progress(&dst, 1, 3, &value, &mut |w, b| work
                    .admit(w, b)
                    .is_ok())
                .map_err(|_| work.refuse_exhaustion()))
            .is_err());
        assert!(retained.check().is_err());
        assert!(retained.with_work(|work| work.charge(0)).is_err());
    }
    assert!(Instant::now() < end);
}

#[test]
fn final_fill_zero_poll_runs_after_all_partition_storage_is_dropped() {
    let end = Instant::now() + Duration::from_secs(20);
    let dst = base(7, &[]);
    let value = literal(9);
    let observed = Cell::new(0usize);
    assert!(dst
        .confirms_range_fill_with_progress(&dst, 3, 1, &value, &mut |_, _| {
            observed.set(observed.get() + 1);
            Instant::now() < end
        })
        .expect("actual trace"));
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    let index = Cell::new(0);
    assert!(owner
        .with_work(|work| dst
            .confirms_range_fill_with_progress(&dst, 3, 1, &value, &mut |w, b| {
                index.set(index.get() + 1);
                if index.get() == observed.get() {
                    assert_eq!((w, b), (0, 0));
                    work.refuse_exhaustion();
                    false
                } else {
                    work.admit(w, b).is_ok()
                }
            })
            .map_err(|_| work.refuse_exhaustion()))
        .is_err());
    assert_eq!(index.get(), observed.get());
    assert!(owner.clone().check().is_err());
    assert!(Instant::now() < end);
}

#[test]
fn original_fill_end_and_stop_refusal_survive_raw_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    let dst = base(7, &[]);
    let value = literal(9);
    let stopped = Arc::new(AtomicBool::new(false));
    let flag = stopped.clone();
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 128 * 1024 * 1024),
        end,
        Arc::new(move || flag.load(Ordering::Acquire)),
    );
    assert!(owner
        .with_work(|work| {
            assert!(dst
                .confirms_range_fill_with_progress(&dst, 3, 1, &value, &mut |w, b| work
                    .admit(w, b)
                    .is_ok())
                .map_err(|_| work.refuse_exhaustion())?);
            stopped.store(true, Ordering::Release);
            Ok(())
        })
        .is_err());
    stopped.store(false, Ordering::Release);
    assert!(owner.clone().check().is_err());
    let expired = super::owner(
        Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("a current instant has an earlier representable second"),
        1_000_000,
        128 * 1024 * 1024,
    );
    assert!(expired
        .with_work(|work| dst
            .confirms_range_fill_with_progress(&dst, 3, 1, &value, &mut |w, b| work
                .admit(w, b)
                .is_ok())
            .map_err(|_| work.refuse_exhaustion()))
        .is_err());
    assert!(Instant::now() < end);
}
