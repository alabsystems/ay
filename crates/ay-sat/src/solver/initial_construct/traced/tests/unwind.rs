// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

struct FirstPayload(Arc<AtomicUsize>);
struct SecondPayload(Arc<AtomicUsize>);
impl Drop for FirstPayload {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic_any(SecondPayload(Arc::clone(&self.0)));
    }
}
impl Drop for SecondPayload {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("last finite bootstrap panic payload");
    }
}
struct ObserverDrop(Arc<AtomicUsize>);
impl Drop for ObserverDrop {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("last retained bootstrap observer destructor");
    }
}

#[test]
fn entry_interior_and_final_poll_hostile_payloads_retire_last_owner_without_escape() {
    let _ = ay_core::misc_cli_flags();
    let (polls, _, healthy) = super::resources::observed(usize::MAX);
    drop(healthy.unwrap());
    for trigger in [1, polls / 2, polls] {
        let armed = Arc::new(AtomicBool::new(false));
        let calls = Arc::new(AtomicUsize::new(0));
        let payload_drops = Arc::new(AtomicUsize::new(0));
        let callback_drops = Arc::new(AtomicUsize::new(0));
        let retired = Arc::new(AtomicUsize::new(0));
        let (active, count, payload) = (
            Arc::clone(&armed),
            Arc::clone(&calls),
            Arc::clone(&payload_drops),
        );
        let capture = ObserverDrop(Arc::clone(&callback_drops));
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 100_000_000),
            None,
            Arc::new(move || {
                let _keep_capture = &capture;
                if active.load(Ordering::SeqCst)
                    && count.fetch_add(1, Ordering::SeqCst) + 1 == trigger
                {
                    panic_any(FirstPayload(Arc::clone(&payload)));
                }
                false
            }),
        )
        .unwrap();
        // No retained external owner: the constructor owns the final callback.
        let input = CountedInitialCnf::try_new(2, &[&[p(0)], &[n(0), p(1)]], original).unwrap();
        AFTER_SCRATCH_DROP.with(|slot| {
            let retired = Arc::clone(&retired);
            *slot.borrow_mut() = Some(Box::new(move || {
                retired.fetch_add(1, Ordering::SeqCst);
            }));
        });
        armed.store(true, Ordering::SeqCst);
        let outcome = catch_unwind(AssertUnwindSafe(|| input.construct_traced(&[p(1)])));
        assert_eq!(
            outcome.unwrap().err(),
            Some(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverPanicked
            ))
        );
        assert_eq!(calls.load(Ordering::SeqCst), trigger);
        assert_eq!(payload_drops.load(Ordering::SeqCst), 2);
        assert_eq!(callback_drops.load(Ordering::SeqCst), 1);
        assert_eq!(retired.load(Ordering::SeqCst), 1);
    }
}

#[test]
fn earlier_work_refusal_survives_last_callback_destructor_panic() {
    let _ = ay_core::misc_cli_flags();
    let drops = Arc::new(AtomicUsize::new(0));
    let capture = ObserverDrop(Arc::clone(&drops));
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 100_000_000),
        None,
        Arc::new(move || {
            let _keep = &capture;
            false
        }),
    )
    .unwrap();
    let input = CountedInitialCnf::try_new(1, &[&[p(0)]], owner).unwrap();
    input
        .owner()
        .admit(input.owner().usage().unwrap().work_remaining as usize, 0)
        .unwrap();
    let outcome = catch_unwind(AssertUnwindSafe(|| input.construct_traced(&[])));
    assert_eq!(
        outcome.unwrap().err(),
        Some(CountedAdmissionError::WorkExhausted)
    );
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn late_trace_arming_and_selected_external_proof_state_refuse_before_trace_creation() {
    for mode in 0..3 {
        let original = ample();
        let mut s = if mode == 2 {
            Solver::with_proof(2, std::io::sink())
        } else {
            Solver::new(2)
        };
        s.cold.counted_admission = Some(original.clone());
        if mode == 0 {
            s.add_clause(vec![p(0)]);
        }
        if mode == 1 {
            s.enable_clause_trace();
        }
        let before = s.cold.clause_trace.as_ref().map(|t| t.entries().len());
        assert!(arm(&mut s, &original).is_err());
        assert_eq!(
            s.cold.clause_trace.as_ref().map(|t| t.entries().len()),
            before
        );
        assert!(original.usage().unwrap().refusal.is_some());
    }
}
