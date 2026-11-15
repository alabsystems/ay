// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn combined_cost() -> (usize, usize) {
    let (mut work, mut bytes) = (0usize, 0usize);
    let mut progress = |w, b| {
        work = work.checked_add(w).unwrap();
        bytes = bytes.checked_add(b).unwrap();
        true
    };
    let pending =
        capture_strict_retained_bundle_with_resource_control(bv_snapshot(), end(), &mut progress)
            .unwrap();
    pending
        .finish_exact_with_resource_control(&mut progress)
        .unwrap();
    (work, bytes)
}

#[test]
fn capture_and_second_replay_share_nonrefundable_exact_and_one_short_combined_credit() {
    let (work, bytes) = combined_cost();
    assert!(work > 0 && bytes > 0);
    for (work_cap, byte_cap, succeeds) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut used_work, mut used_bytes) = (0usize, 0usize);
        let mut progress = |w, b| {
            used_work = used_work.checked_add(w).unwrap();
            used_bytes = used_bytes.checked_add(b).unwrap();
            used_work <= work_cap && used_bytes <= byte_cap
        };
        let pending = capture_strict_retained_bundle_with_resource_control(
            bv_snapshot(),
            end(),
            &mut progress,
        )
        .expect("combined shortfall must occur after the authentic first check");
        let before = producer_test_counter::count();
        let result = pending.finish_exact_with_resource_control(&mut progress);
        assert_eq!(result.is_ok(), succeeds);
        if !succeeds {
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        } else {
            assert_eq!((used_work, used_bytes), (work, bytes));
        }
        assert_eq!(producer_test_counter::count(), before);
    }
}

#[test]
fn interphase_expiry_and_later_deadlines_cannot_renew_the_original_owner() {
    let deadline = Instant::now() + Duration::from_secs(2);
    let pending = capture_strict_retained_bundle_with_resource_control(
        repeated_bool_snapshot(),
        deadline,
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(pending.deadline, deadline);
    let (owner, _) = capture_strict_retained_bundle_with_resource_control(
        repeated_bool_snapshot(),
        deadline,
        &mut |_, _| true,
    )
    .unwrap()
    .finish_exact_with_resource_control(&mut |_, _| true)
    .unwrap();
    assert_eq!(owner.deadline, deadline);
    let bytes = owner
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap();
    std::thread::sleep(deadline.saturating_duration_since(Instant::now()));
    let before = producer_test_counter::count();
    let mut calls = 0;
    let mut progress = |_, _| {
        calls += 1;
        true
    };
    assert!(matches!(
        pending.finish_exact_with_resource_control(&mut progress),
        Err(ProofCheckError::Cancelled)
    ));
    assert!(matches!(
        owner.replay_exact_with_resource_control(end(), &mut progress),
        Err(ProofCheckError::Cancelled)
    ));
    assert!(matches!(
        owner.encode_with_resource_control(transport_limits(), end(), &mut progress),
        Err(ProofCheckError::Cancelled)
    ));
    assert_eq!(calls, 0);
    // Separate bytes enter a genuinely NEW offline consumer request, without
    // renewing the expired producer owner or trusting a wire-supplied deadline.
    let (offline, report) = read_retained_proof_bundle_with_resource_control(
        &bytes,
        transport_limits(),
        end(),
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(
        offline.obligation_assertions(),
        owner.obligation_assertions()
    );
    assert!(report.quality.is_complete());
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn entry_refusal_cancels_capture_finish_encode_and_replay_without_retry() {
    let before = producer_test_counter::count();
    let mut calls = 0;
    assert!(matches!(
        capture_strict_retained_bundle_with_resource_control(bv_snapshot(), end(), &mut |_, _| {
            calls += 1;
            false
        },),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, 1);
    assert_eq!(producer_test_counter::count(), before);
    let pending =
        capture_strict_retained_bundle_with_resource_control(bv_snapshot(), end(), &mut |_, _| {
            true
        })
        .unwrap();
    let before = producer_test_counter::count();
    calls = 0;
    assert!(matches!(
        pending.finish_exact_with_resource_control(&mut |_, _| {
            calls += 1;
            false
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, 1);
    assert_eq!(producer_test_counter::count(), before);
    let owner = finished();
    for encode in [false, true] {
        calls = 0;
        let mut refuse = |_, _| {
            calls += 1;
            false
        };
        if encode {
            assert!(matches!(
                owner.encode_with_resource_control(transport_limits(), end(), &mut refuse),
                Err(ProofCheckError::ResourceLimit)
            ));
        } else {
            assert!(matches!(
                owner.replay_exact_with_resource_control(end(), &mut refuse),
                Err(ProofCheckError::ResourceLimit)
            ));
        }
        assert_eq!(calls, 1);
    }
}

#[test]
fn final_checkpoint_refusal_never_publishes_a_pending_or_finished_owner() {
    let mut capture_calls = 0;
    capture_strict_retained_bundle_with_resource_control(
        repeated_bool_snapshot(),
        end(),
        &mut |_, _| {
            capture_calls += 1;
            true
        },
    )
    .unwrap();
    let mut calls = 0;
    assert!(matches!(
        capture_strict_retained_bundle_with_resource_control(
            repeated_bool_snapshot(),
            end(),
            &mut |_, _| {
                calls += 1;
                calls != capture_calls
            },
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, capture_calls);
    let pending = capture_strict_retained_bundle_with_resource_control(
        repeated_bool_snapshot(),
        end(),
        &mut |_, _| true,
    )
    .unwrap();
    let mut finish_calls = 0;
    pending
        .finish_exact_with_resource_control(&mut |_, _| {
            finish_calls += 1;
            true
        })
        .unwrap();
    let pending = capture_strict_retained_bundle_with_resource_control(
        repeated_bool_snapshot(),
        end(),
        &mut |_, _| true,
    )
    .unwrap();
    calls = 0;
    assert!(matches!(
        pending.finish_exact_with_resource_control(&mut |_, _| {
            calls += 1;
            calls != finish_calls
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, finish_calls);
}

#[test]
fn caught_callback_panic_poison_and_temporary_cleanup_precede_terminal_admission() {
    let mut calls = 0;
    let result = super::super::control::run(
        end(),
        &mut |_, _| {
            calls += 1;
            if calls == 2 {
                panic!("test callback panic");
            }
            true
        },
        |control| {
            assert!(catch_unwind(AssertUnwindSafe(|| control.charge(1, 0))).is_err());
            Ok(()) // Deliberately try to ignore the caught panic.
        },
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(calls, 2);

    struct Temporary<'a>(&'a Cell<bool>);
    impl Drop for Temporary<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    let dropped = Cell::new(false);
    let mut calls = 0;
    super::super::control::run(
        end(),
        &mut |_, _| {
            calls += 1;
            if calls == 3 {
                assert!(dropped.get());
            }
            true
        },
        |control| {
            let _temporary = Temporary(&dropped);
            control.charge(1, 0)?;
            Ok(())
        },
    )
    .unwrap();
    assert!(dropped.get());
    assert_eq!(calls, 3);
}
