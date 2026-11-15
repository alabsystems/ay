// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_and_one_short_original_work_and_storage_include_scalar_components() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::bitvec(8));
    let source = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = costs(&source, &values, end);
    assert!(units < 1_000_000 && bytes < 128 << 20);
    let original = owner(end, units, bytes);
    drop(run(&source, &values, &original));
    original.check().unwrap();
    for (u, b) in [
        (units - 1, bytes),
        (units, bytes - 1),
        (0, bytes),
        (units, 0),
    ] {
        let original = owner(end, u, b);
        assert!(matches!(
            original.with_work(|work| {
                source.try_extract_prepared_flat_model_with_budget(&values, work)
            }),
            Err(OriginalAdmissionError::Query(QueryError::Exhausted))
        ));
        assert!(original.clone().with_work(|_| Ok(())).is_err());
    }
}

#[test]
fn repeated_scalar_extraction_uses_the_same_cumulative_clone_not_a_copy_grant() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::Bool);
    let source = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = costs(&source, &values, end);
    let original = owner(end, 2 * units - 1, 2 * bytes);
    drop(run(&source, &values, &original));
    assert!(original
        .clone()
        .with_work(|work| { source.try_extract_prepared_flat_model_with_budget(&values, work) })
        .is_err());
    assert!(original.check().is_err());
}

#[test]
fn scalar_plan_cleanup_stop_remains_sticky_after_raw_observer_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::bitvec(8));
    let source = fixture.solver();
    let values = fixture.values();
    let (units, bytes, polls) = costs(&source, &values, end);
    let calls = Arc::new(AtomicUsize::new(0));
    let armed = Arc::new(AtomicBool::new(true));
    let observed = calls.clone();
    let enabled = armed.clone();
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64, bytes),
        end,
        Arc::new(move || {
            enabled.load(Ordering::Acquire) && observed.fetch_add(1, Ordering::AcqRel) + 1 >= polls
        }),
    );
    assert!(matches!(
        original.with_work(|work| {
            source.try_extract_prepared_flat_model_with_budget(&values, work)
        }),
        Err(OriginalAdmissionError::ObserverStopped)
    ));
    assert_eq!(calls.load(Ordering::Acquire), polls);
    armed.store(false, Ordering::Release);
    assert!(original.clone().check().is_err());
    assert!(!source.dirty && !source.assign_dirty);
}

#[test]
fn original_expired_end_refuses_scalar_preparation_without_replacing_the_end() {
    let fixture = Pinned::new(Sort::bitvec(8));
    let source = fixture.solver();
    let values = fixture.values();
    let original = owner(
        Instant::now() - Duration::from_secs(1),
        1_000_000,
        128 << 20,
    );
    assert!(matches!(
        original.with_work(|work| {
            source.try_extract_prepared_flat_model_with_budget(&values, work)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert!(original.clone().check().is_err());
    assert!(!source.dirty && !source.assign_dirty);
}
