// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

struct RoundStop<'budget, 'owner> {
    work: &'budget mut WorkBudget<'owner>,
    stopped: Arc<AtomicBool>,
    rounds: usize,
}
impl Control for RoundStop<'_, '_> {
    fn offer(&mut self, units: usize, bytes: usize) -> Result<(), QueryError> {
        if units == 256 && bytes == 32 {
            self.rounds += 1;
            if self.rounds == 3 {
                self.stopped.store(true, Ordering::SeqCst);
            }
        }
        self.work.admit(units, bytes)
    }
    fn exhausted(&mut self) -> QueryError {
        self.work.refuse_exhaustion()
    }
}

#[test]
fn exact_cumulative_and_one_short_digest_work_or_storage_refuse_stickily() {
    let source = fixture();
    let (units, bytes) = totals(&source);
    let end = Instant::now() + Duration::from_secs(20);
    consume(&owner_at(end, units, bytes, Arc::new(|| false)), &source).unwrap();
    for original in [
        owner_at(end, units - 1, bytes, Arc::new(|| false)),
        owner_at(end, units, bytes - 1, Arc::new(|| false)),
    ] {
        assert!(consume(&original, &source).is_err());
        assert!(original.check().is_err());
        assert!(consume(&original.clone(), &source).is_err());
    }
}

#[test]
fn repeated_digest_consumption_debits_one_original_owner_across_clones() {
    let source = fixture();
    let (units, bytes) = totals(&source);
    let original = owner_at(
        Instant::now() + Duration::from_secs(20),
        2 * units,
        2 * bytes,
        Arc::new(|| false),
    );
    let retained = original.clone();
    consume(&original, &source).unwrap();
    consume(&retained, &source).unwrap();
    assert!(consume(&retained, &source).is_err());
    assert!(original.check().is_err());
}

#[test]
fn original_stop_during_round_is_observed_before_next_round_and_cannot_reset() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observer = stopped.clone();
    let original = owner_at(
        Instant::now() + Duration::from_secs(20),
        2_000_000,
        8 * 1024 * 1024,
        Arc::new(move || observer.load(Ordering::SeqCst)),
    );
    let result = original.with_work(|work| {
        let mut relay = RoundStop {
            work,
            stopped: stopped.clone(),
            rounds: 0,
        };
        let result = hash::run(b"abc", &mut relay);
        assert!(result.is_err());
        assert_eq!(relay.rounds, 3);
        result.map(|_| ())
    });
    assert_eq!(result, Err(OriginalAdmissionError::ObserverStopped));
    stopped.store(false, Ordering::SeqCst);
    assert!(original.check().is_err());
    assert!(consume(&original, &fixture()).is_err());
}

#[test]
fn retained_callback_receives_the_same_budget_without_renewing_remaining_work() {
    let source = fixture();
    let original = owner_at(
        Instant::now() + Duration::from_secs(20),
        2_000_000,
        8 * 1024 * 1024,
        Arc::new(|| false),
    );
    original
        .with_work(|work| {
            let pointer = std::ptr::from_mut(work).cast::<()>();
            let prepared = prepare_normalized_chc_input_with_work(&source, work)?;
            prepared.with_sha256(|_, _, _, actual| {
                assert_eq!(std::ptr::from_mut(actual).cast::<()>(), pointer);
                actual.charge(17)
            })
        })
        .unwrap();
}

#[test]
fn ordinary_carrier_drop_is_data_only_and_does_not_call_the_digest_callback() {
    let source = fixture();
    let original = owner_at(
        Instant::now() + Duration::from_secs(20),
        2_000_000,
        8 * 1024 * 1024,
        Arc::new(|| false),
    );
    original
        .with_work(|work| {
            drop(prepare_normalized_chc_input_with_work(&source, work)?);
            work.charge(0)
        })
        .unwrap();
    assert!(original.check().is_ok());
}
