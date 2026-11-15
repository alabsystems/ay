// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_cumulative_work_and_storage_frontiers_have_one_short_refusals() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = costs(&solver, &values, end);
    let exact = owner(end, units, bytes);
    drop(run(&solver, &values, &exact));
    exact.check().unwrap();
    for (u, b) in [(units - 1, bytes), (units, bytes - 1)] {
        let original = owner(end, u, b);
        assert!(original
            .with_work(|w| solver.try_extract_prepared_flat_model_with_budget(&values, w))
            .is_err());
        assert!(original.clone().with_work(|_| Ok(())).is_err());
    }
}

#[test]
fn repeated_extraction_and_clone_retry_do_not_renew_original_allowances() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = costs(&solver, &values, end);
    let original = owner(end, 2 * units - 1, 2 * bytes);
    drop(run(&solver, &values, &original));
    assert!(original
        .clone()
        .with_work(|w| solver.try_extract_prepared_flat_model_with_budget(&values, w))
        .is_err());
    assert!(original.check().is_err());
}

#[test]
fn final_cleanup_observation_remains_sticky_after_raw_callback_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, polls) = costs(&solver, &values, end);
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
    // Calibration has API offers + post-output drop poll. OA adds its
    // initial check: the same threshold reaches API's final cleanup fence.
    assert!(matches!(
        original.with_work(|w| solver.try_extract_prepared_flat_model_with_budget(&values, w)),
        Err(OriginalAdmissionError::ObserverStopped)
    ));
    assert_eq!(calls.load(Ordering::Acquire), polls);
    armed.store(false, Ordering::Release);
    assert!(original.clone().check().is_err());
}

#[test]
fn caught_original_callback_panic_revokes_retry_without_source_mutation() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let enabled = Arc::new(AtomicBool::new(true));
    let armed = enabled.clone();
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 128 << 20),
        end,
        Arc::new(move || {
            if armed.load(Ordering::Acquire) {
                panic!("controlled test callback panic");
            }
            false
        }),
    );
    assert!(original
        .with_work(|w| solver.try_extract_prepared_flat_model_with_budget(&values, w))
        .is_err());
    enabled.store(false, Ordering::Release);
    assert!(original.clone().check().is_err());
    assert!(!solver.dirty && !solver.assign_dirty && !solver.var_layer_dirty);
}

#[test]
fn already_expired_original_end_refuses_first_work_and_every_later_attempt() {
    let end = Instant::now() - Duration::from_secs(1);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let original = owner(end, 1_000_000, 128 << 20);
    assert!(matches!(
        original.with_work(|w| solver.try_extract_prepared_flat_model_with_budget(&values, w)),
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert!(original.clone().check().is_err());
}
