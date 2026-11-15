// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::executor_adapter::ReplayCancellation;
use std::cell::Cell;

mod diagnostic;
mod rows;
mod settlement;
fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

#[test]
fn request_defaults_derive_existing_finite_caps_and_transport_only_tightens() {
    let mut callback = || true;
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    // Three metered walks per retained row (see progress.rs); bytes bound
    // live memory and stay one proof's.
    assert_eq!(
        owner.max_work as u64,
        3 * MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF as u64 * MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA
    );
    assert!(
        owner.max_bytes
            <= MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF * MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
    );
    let limits = owner.transport_limits();
    assert_eq!(limits.max_json_bytes, DOCUMENT_BYTES);
    assert!(limits.max_storage_bytes <= owner.max_bytes - owner.bytes);
    assert_eq!(limits.max_work, MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA);
    owner.max_work = owner.work + 7;
    owner.max_bytes = owner.bytes + 11;
    let limits = owner.transport_limits();
    assert_eq!(
        (
            limits.max_work,
            limits.max_json_bytes,
            limits.max_storage_bytes
        ),
        (7, 11, 11)
    );
    assert!(owner.charge(7, 11));
    let limits = owner.transport_limits();
    assert_eq!(
        (
            limits.max_work,
            limits.max_json_bytes,
            limits.max_storage_bytes
        ),
        (0, 0, 0)
    );
    assert!(!owner.charge(1, 0));
    assert!(owner.check().is_err());
}

#[test]
fn accounting_overflow_and_zero_memory_refuse_without_reset() {
    for bytes in [false, true] {
        let mut callback = || true;
        let mut owner =
            RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        if bytes {
            owner.bytes = usize::MAX;
        } else {
            owner.work = usize::MAX;
        }
        assert!(!owner.charge(1, 1));
        assert!(!owner.charge(0, 0));
    }
    let _scope = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
    let mut callback = || true;
    assert!(RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).is_err());
}

#[test]
fn impossible_debits_refuse_before_invoking_the_caller_callback() {
    for overflow in [false, true] {
        let calls = Cell::new(0usize);
        let mut callback = || {
            calls.set(calls.get() + 1);
            true
        };
        let mut owner =
            RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        if overflow {
            owner.work = usize::MAX;
        } else {
            owner.max_bytes = owner.bytes;
        }
        let before = calls.get();
        assert!(!owner.charge(1, 1));
        assert_eq!(calls.get(), before);
        assert!(owner.check().is_err());
        assert_eq!(calls.get(), before);
    }
}

#[test]
fn callback_refusal_and_caught_callback_panic_permanently_poison_owner() {
    let calls = Cell::new(0usize);
    let stop = Cell::new(usize::MAX);
    let mut callback = || {
        calls.set(calls.get() + 1);
        calls.get() != stop.get()
    };
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    stop.set(calls.get() + 2); // refuse the post-charge poll, not only entry.
    assert!(!owner.charge(1, 1));
    stop.set(usize::MAX);
    let after = calls.get();
    assert!(owner.check().is_err());
    assert_eq!(calls.get(), after);

    let panic_now = Cell::new(false);
    let mut callback = || {
        assert!(!panic_now.get(), "intentional callback panic");
        true
    };
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    panic_now.set(true);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| owner.charge(1, 1))).is_err());
    panic_now.set(false);
    assert!(owner.check().is_err());
}

#[test]
fn inherited_cancel_expiry_and_retained_legacy_wall_keep_original_owner() {
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let mut callback = || true;
    let mut owner = RetainedReplayProgress::new(
        ReplayLimit::Cancellable {
            deadline: deadline(),
            cancellation: &cancellation,
        },
        &mut callback,
    )
    .unwrap();
    parent.cancel();
    assert!(owner.check().is_err());
    parent.reset();
    assert!(owner.check().is_err());
    let mut callback = || true;
    assert!(
        RetainedReplayProgress::new(ReplayLimit::Until(Instant::now()), &mut callback).is_err()
    );
    let before = Instant::now();
    let mut callback = || true;
    let mut legacy = RetainedReplayProgress::new(ReplayLimit::Legacy, &mut callback).unwrap();
    let original = legacy.deadline();
    assert!(original >= before + Duration::from_secs(LEGACY_REQUEST_SECONDS));
    assert!(matches!(legacy.limit(), ReplayLimit::Until(deadline) if deadline == original));
    assert!(legacy.charge(1, 1));
    assert_eq!(legacy.deadline(), original);
}

#[test]
fn first_use_inventory_order_and_exact_one_short_are_cumulatively_charged() {
    let input = [TermId(7), TermId(3), TermId(7), TermId(2), TermId(3)];
    let mut callback = || true;
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let base = (owner.work, owner.bytes);
    let used = owner.ordered_unique(&input).unwrap();
    let ordered_work = owner.work - base.0;
    let ordered_bytes = owner.bytes - base.1;
    assert_eq!(used, [TermId(7), TermId(3), TermId(2)]);
    assert!(owner.equal_ids(&used, &[TermId(7), TermId(3), TermId(2)]));
    assert!(!owner.equal_ids(&used, &[TermId(3), TermId(7), TermId(2)]));
    for (short_work, short_bytes) in [(false, false), (true, false), (false, true)] {
        let mut callback = || true;
        let mut owner =
            RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        owner.max_work = owner.work + ordered_work - usize::from(short_work);
        owner.max_bytes = owner.bytes + ordered_bytes - usize::from(short_bytes);
        assert_eq!(
            owner.ordered_unique(&input).is_ok(),
            !(short_work || short_bytes)
        );
        if short_work || short_bytes {
            assert!(owner.check().is_err());
        }
    }
}
