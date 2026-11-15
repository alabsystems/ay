// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use std::sync::Mutex;

fn input(original: CountedAdmission) -> CountedInitialCnf {
    CountedInitialCnf::try_new(2, &[&[p(0)], &[n(0), p(1)]], original).unwrap()
}
fn measured(work: u64, bytes: usize) -> (CountedAdmission, Result<CountedInitialSolver>) {
    let original = owner(work, bytes);
    let result = build(2, &[&[p(0)], &[n(0), p(1)]], &[p(1)], original.clone());
    (original, result)
}

#[test]
fn traced_source_assumptions_registration_bcp_exact_and_one_short_grants() {
    let (baseline, result) = measured(100_000_000, 100_000_000);
    drop(result.unwrap());
    let used = baseline.usage().unwrap();
    let (exact, result) = measured(used.work_admitted, used.storage_admitted);
    drop(result.unwrap());
    assert_eq!(exact.usage().unwrap().work_remaining, 0);
    assert_eq!(exact.usage().unwrap().storage_remaining, 0);
    for (work, bytes, error) in [
        (
            used.work_admitted - 1,
            used.storage_admitted,
            CountedAdmissionError::WorkExhausted,
        ),
        (
            used.work_admitted,
            used.storage_admitted - 1,
            CountedAdmissionError::StorageExhausted,
        ),
    ] {
        let (short, result) = measured(work, bytes);
        assert_eq!(result.err(), Some(error));
        let before = short.usage().unwrap();
        assert_eq!(short.check(), Err(error));
        assert_eq!(short.usage().unwrap(), before);
    }
}

#[test]
fn each_observed_positive_debit_boundary_refuses_one_short_without_output() {
    let _ = ay_core::misc_cli_flags();
    let current = Arc::new(Mutex::new(None::<CountedAdmission>));
    let marks = Arc::new(Mutex::new(Vec::new()));
    let (captured, output) = (Arc::clone(&current), Arc::clone(&marks));
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 100_000_000),
        None,
        Arc::new(move || {
            if let Some(owner) = captured.lock().unwrap().as_ref() {
                let u = owner.usage().unwrap();
                output
                    .lock()
                    .unwrap()
                    .push((u.work_admitted, u.storage_admitted));
            }
            false
        }),
    )
    .unwrap();
    *current.lock().unwrap() = Some(original.clone());
    drop(build(2, &[&[p(0)], &[n(0), p(1)]], &[p(1)], original.clone()).unwrap());
    let total = original.usage().unwrap();
    current.lock().unwrap().take(); // break the test observer/owner cycle
    let mut work: Vec<_> = marks
        .lock()
        .unwrap()
        .iter()
        .map(|v| v.0)
        .filter(|n| *n > 0)
        .collect();
    let mut bytes: Vec<_> = marks
        .lock()
        .unwrap()
        .iter()
        .map(|v| v.1)
        .filter(|n| *n > 0)
        .collect();
    work.push(total.work_admitted);
    bytes.push(total.storage_admitted);
    work.sort_unstable();
    work.dedup();
    bytes.sort_unstable();
    bytes.dedup();
    assert!(work.len() > 30 && bytes.len() > 10);
    for cut in work {
        let (owner, result) = measured(cut - 1, total.storage_admitted);
        assert_eq!(
            result.err(),
            Some(CountedAdmissionError::WorkExhausted),
            "work {cut}"
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
    }
    for cut in bytes {
        let (owner, result) = measured(total.work_admitted, cut - 1);
        assert_eq!(
            result.err(),
            Some(CountedAdmissionError::StorageExhausted),
            "bytes {cut}"
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
    }
}

pub(super) fn observed(stop_at: usize) -> (usize, CountedAdmission, Result<CountedInitialSolver>) {
    let armed = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let (active, count) = (Arc::clone(&armed), Arc::clone(&calls));
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 100_000_000),
        None,
        Arc::new(move || {
            active.load(Ordering::SeqCst) && count.fetch_add(1, Ordering::SeqCst) + 1 == stop_at
        }),
    )
    .unwrap();
    let input = input(original.clone());
    armed.store(true, Ordering::SeqCst);
    let result = input.construct_traced(&[p(1)]);
    (calls.load(Ordering::SeqCst), original, result)
}

#[test]
fn every_actual_bootstrap_observer_cut_is_sticky_and_returns_no_solver() {
    let _ = ay_core::misc_cli_flags();
    let (polls, _, baseline) = observed(usize::MAX);
    drop(baseline.unwrap());
    assert!(polls > 50);
    let stopped = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
    for cut in 1..=polls {
        let (reached, owner, result) = observed(cut);
        assert_eq!(reached, cut);
        assert_eq!(result.err(), Some(stopped), "poll {cut}");
        let frozen = owner.usage().unwrap();
        assert_eq!(owner.check(), Err(stopped));
        assert_eq!(owner.usage().unwrap(), frozen);
    }
}

#[test]
fn exhausted_original_owner_and_post_cleanup_cancellation_do_not_publish() {
    let original = ample();
    let prepared = input(original.clone());
    original
        .admit(original.usage().unwrap().work_remaining as usize, 0)
        .unwrap();
    assert_eq!(
        prepared.construct_traced(&[]).err(),
        Some(CountedAdmissionError::WorkExhausted)
    );
    let stop = Arc::new(AtomicBool::new(false));
    let capture = Arc::clone(&stop);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 100_000_000),
        None,
        Arc::new(move || capture.load(Ordering::SeqCst)),
    )
    .unwrap();
    let input = input(original.clone());
    AFTER_SCRATCH_DROP.with(|slot| {
        let stop = Arc::clone(&stop);
        *slot.borrow_mut() = Some(Box::new(move || stop.store(true, Ordering::SeqCst)));
    });
    assert_eq!(
        input.construct_traced(&[]).err(),
        Some(CountedAdmissionError::Original(
            OriginalAdmissionError::ObserverStopped
        ))
    );
    assert!(stop.load(Ordering::SeqCst));
}
