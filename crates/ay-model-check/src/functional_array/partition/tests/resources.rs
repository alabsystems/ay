// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn exact_and_one_short_work_or_bytes_keep_the_same_original_ledger() {
    let end = Instant::now() + Duration::from_secs(20);
    let dst = base(0, &[(0, 7)]);
    let src = base(0, &[(0, 9)]);
    let target = base(0, &[(0, 7), (1, 9)]);
    let work = Cell::new(0u64);
    let bytes = Cell::new(0usize);
    assert!(target
        .confirms_range_copy_with_progress(&dst, &src, 1, 3, 0, &mut |w, b| {
            work.set(work.get() + w as u64);
            bytes.set(bytes.get() + b);
            Instant::now() < end
        })
        .expect("measured actual offers"));
    let exact = owner(end, work.get(), bytes.get());
    assert!(confirm(&exact, &target, &dst, &src, 1, 3, 0));
    for (w, b) in [
        (work.get() - 1, bytes.get()),
        (work.get(), bytes.get() - 1),
        (0, 0),
    ] {
        let short = owner(end, w, b);
        let cloned = short.clone();
        assert!(short
            .with_work(|work| target
                .confirms_range_copy_with_progress(&dst, &src, 1, 3, 0, &mut |w, b| work
                    .admit(w, b)
                    .is_ok())
                .map_err(|_| work.refuse_exhaustion()))
            .is_err());
        assert!(cloned.check().is_err());
        assert!(cloned.with_work(|work| work.charge(0)).is_err());
    }
    assert!(Instant::now() < end);
}

#[test]
fn final_post_scratch_poll_refusal_is_sticky_after_raw_observer_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    let data = base(7, &[]);
    let stopped = Arc::new(AtomicBool::new(false));
    let flag = stopped.clone();
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 128 * 1024 * 1024),
        end,
        Arc::new(move || flag.load(Ordering::Acquire)),
    );
    let refused = owner.with_work(|work| {
        let result = data
            .confirms_range_copy_with_progress(&data, &data, 1, 0, 0, &mut |w, b| {
                // This leg checks the enclosing owner's post-operation fence;
                // kernel final-poll refusal is exercised separately below.
                work.admit(w, b).is_ok()
            })
            .map_err(|_| work.refuse_exhaustion())?;
        assert!(result);
        stopped.store(true, Ordering::Release);
        Ok(())
    });
    assert!(
        refused.is_err(),
        "OriginalAdmission's post-operation cleanup fence"
    );
    stopped.store(false, Ordering::Release);
    assert!(owner.clone().check().is_err());
    assert!(Instant::now() < end);
}

#[test]
fn kernel_final_zero_offer_runs_after_topology_and_cut_scratch_drop() {
    let end = Instant::now() + Duration::from_secs(20);
    let data = base(7, &[]);
    let observed = Cell::new(0usize);
    assert!(data
        .confirms_range_copy_with_progress(&data, &data, 1, 0, 0, &mut |_, _| {
            observed.set(observed.get() + 1);
            Instant::now() < end
        })
        .expect("complete actual offer trace"));
    let index = Cell::new(0usize);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    let result = owner.with_work(|work| {
        data.confirms_range_copy_with_progress(&data, &data, 1, 0, 0, &mut |w, b| {
            index.set(index.get() + 1);
            if index.get() == observed.get() {
                assert_eq!((w, b), (0, 0));
                work.refuse_exhaustion();
                false
            } else {
                work.admit(w, b).is_ok()
            }
        })
        .map_err(|_| work.refuse_exhaustion())
    });
    assert!(result.is_err());
    assert_eq!(index.get(), observed.get());
    assert!(owner.clone().check().is_err());
    assert!(Instant::now() < end);
}

#[test]
fn expired_original_end_cannot_be_replaced_by_another_adapter() {
    let end = Instant::now() + Duration::from_secs(20);
    let data = base(7, &[]);
    let expired = owner(
        Instant::now() - Duration::from_secs(1),
        1_000_000,
        128 * 1024 * 1024,
    );
    assert!(expired
        .with_work(|work| data
            .confirms_range_copy_with_progress(&data, &data, 0, 1, 0, &mut |w, b| work
                .admit(w, b)
                .is_ok())
            .map_err(|_| QueryError::Exhausted))
        .is_err());
    assert!(expired.clone().check().is_err());
    assert!(Instant::now() < end);
}
