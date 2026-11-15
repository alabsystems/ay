// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn complete_class_extraction_has_exact_work_and_logical_copy_one_short_refusals() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = class_costs(&solver, &values, end);
    let exact = owner(end, units, bytes);
    let output = controlled(&solver, &values, &exact);
    assert!(output.array_values.contains_key(&fixture.arrays[2]));
    drop(output);
    exact.check().unwrap();
    for (work, storage) in [(units - 1, bytes), (units, bytes - 1)] {
        // Distinct test attempts, never renewal after a refused attempt.
        let original = owner(end, work, storage);
        assert!(original
            .with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w))
            .is_err());
        assert!(original.clone().with_work(|_| Ok(())).is_err());
    }
}

#[test]
fn zero_grants_and_clone_retries_share_the_original_cumulative_class_cost() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = class_costs(&solver, &values, end);
    for (work, storage) in [(0, bytes), (units, 0)] {
        let original = owner(end, work, storage);
        assert!(original
            .with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w))
            .is_err());
        assert!(original.clone().check().is_err());
    }
    let original = owner(end, 2 * units - 1, 2 * bytes);
    let first = controlled(&solver, &values, &original);
    drop(first);
    assert!(original
        .clone()
        .with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w))
        .is_err());
    assert!(original.check().is_err());
}

#[test]
fn original_late_stop_after_ordered_plan_and_copy_cleanup_stays_latched_after_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, polls) = class_costs(&solver, &values, end);
    let calls = Arc::new(AtomicUsize::new(0));
    let enabled = Arc::new(AtomicBool::new(true));
    let count = calls.clone();
    let armed = enabled.clone();
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64, bytes),
        end,
        Arc::new(move || {
            armed.load(Ordering::Acquire) && count.fetch_add(1, Ordering::AcqRel) + 1 >= polls
        }),
    );
    // class_costs includes one explicit post-output drop poll. Thus poll
    // (polls-1) is the API's final owned::finish; initial owner check shifts
    // that frontier to polls here, after class/reads/array scratch cleanup.
    assert!(matches!(
        original.with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w)),
        Err(OriginalAdmissionError::ObserverStopped)
    ));
    assert_eq!(calls.load(Ordering::Acquire), polls);
    enabled.store(false, Ordering::Release);
    assert!(original
        .clone()
        .with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w))
        .is_err());
}

#[test]
fn already_expired_original_end_refuses_class_work_and_every_retry() {
    let end = Instant::now() - Duration::from_secs(1);
    let fixture = ClassFixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let original = owner(end, 1_000_000, 128 << 20);
    assert!(matches!(
        original.with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w)),
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert!(original.clone().check().is_err());
}
