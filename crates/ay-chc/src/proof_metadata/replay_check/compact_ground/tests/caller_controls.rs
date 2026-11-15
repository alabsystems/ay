// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::deadline::{ScopedLaneCancellation, ScopedSmtDeadline};
use std::cell::RefCell;

thread_local! {
    static DEADLINE: RefCell<Option<ScopedSmtDeadline>> = const { RefCell::new(None) };
    static LANE: RefCell<Option<ScopedLaneCancellation>> = const { RefCell::new(None) };
}

struct ClearScopes;

impl Drop for ClearScopes {
    fn drop(&mut self) {
        DEADLINE.with(|slot| drop(slot.borrow_mut().take()));
        LANE.with(|slot| drop(slot.borrow_mut().take()));
    }
}

fn removing_callback(armed: Arc<AtomicBool>) -> ay_core::resource::CheckStop {
    Arc::new(move || {
        if armed.swap(false, Ordering::SeqCst) {
            DEADLINE.with(|slot| drop(slot.borrow_mut().take()));
            LANE.with(|slot| drop(slot.borrow_mut().take()));
        }
        false
    })
}

#[test]
fn expired_later_deadline_cannot_be_removed_by_original_callback() {
    let armed = Arc::new(AtomicBool::new(false));
    let _original = ay_core::resource::enter_check_stop(removing_callback(Arc::clone(&armed)));
    let run = run();
    let _cleanup = ClearScopes;
    DEADLINE.with(|slot| {
        *slot.borrow_mut() = Some(ScopedSmtDeadline::install_until(
            Instant::now() - Duration::from_millis(1),
        ));
    });
    armed.store(true, Ordering::SeqCst);
    assert!(run.run_checked_replay(Duration::from_secs(60)).is_err());
    assert!(
        armed.load(Ordering::SeqCst),
        "admit deadline before callback"
    );
    DEADLINE.with(|slot| drop(slot.borrow_mut().take()));
    assert!(
        run.run_checked_replay(Duration::from_secs(60)).is_err(),
        "removing the deadline cannot revive the original witness"
    );
}

#[test]
fn cancelled_later_lane_cannot_be_removed_by_original_callback() {
    let armed = Arc::new(AtomicBool::new(false));
    let _original = ay_core::resource::enter_check_stop(removing_callback(Arc::clone(&armed)));
    let run = run();
    let _cleanup = ClearScopes;
    let token = crate::CancellationToken::new();
    token.cancel();
    LANE.with(|slot| {
        *slot.borrow_mut() = Some(ScopedLaneCancellation::install(token, None));
    });
    armed.store(true, Ordering::SeqCst);
    assert!(run.run_checked_replay(Duration::from_secs(60)).is_err());
    assert!(armed.load(Ordering::SeqCst), "admit lane before callback");
    LANE.with(|slot| drop(slot.borrow_mut().take()));
    assert!(
        run.run_checked_replay(Duration::from_secs(60)).is_err(),
        "removing the lane cannot revive the original witness"
    );
}

#[test]
fn interrupted_later_lane_cannot_be_removed_by_original_callback() {
    let armed = Arc::new(AtomicBool::new(false));
    let _original = ay_core::resource::enter_check_stop(removing_callback(Arc::clone(&armed)));
    let run = run();
    let _cleanup = ClearScopes;
    let flag = Arc::new(AtomicBool::new(true));
    LANE.with(|slot| {
        *slot.borrow_mut() = Some(ScopedLaneCancellation::install(
            crate::CancellationToken::new(),
            Some(Arc::clone(&flag)),
        ));
    });
    armed.store(true, Ordering::SeqCst);
    assert!(run.run_checked_replay(Duration::from_secs(60)).is_err());
    assert!(
        armed.load(Ordering::SeqCst),
        "admit interrupt before callback"
    );
    LANE.with(|slot| drop(slot.borrow_mut().take()));
    flag.store(false, Ordering::SeqCst);
    assert!(run.run_checked_replay(Duration::from_secs(60)).is_err());
}

#[test]
fn later_lane_cancelled_and_removed_inside_original_callback_stays_terminal() {
    let armed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&armed);
    let token = crate::CancellationToken::new();
    let cancelling = token.clone();
    let _original = ay_core::resource::enter_check_stop(Arc::new(move || {
        if observed.swap(false, Ordering::SeqCst) {
            cancelling.cancel();
            LANE.with(|slot| drop(slot.borrow_mut().take()));
        }
        false
    }));
    let run = run();
    // Restore the true initial TLS state even if the callback drops an outer
    // scope out of order while replay's nested scope is installed.
    let _baseline = ScopedLaneCancellation::install(crate::CancellationToken::new(), None);
    let _cleanup = ClearScopes;
    LANE.with(|slot| {
        *slot.borrow_mut() = Some(ScopedLaneCancellation::install(token, None));
    });
    armed.store(true, Ordering::SeqCst);
    assert!(run.run_checked_replay(Duration::from_secs(60)).is_err());
    assert!(!armed.load(Ordering::SeqCst), "original callback ran");
    assert!(
        LANE.with(|slot| slot.borrow().is_none()),
        "caller scope removed"
    );
    assert!(
        run.run_checked_replay(Duration::from_secs(60)).is_err(),
        "captured cancellation remains terminal after its TLS scope vanished"
    );
}

#[test]
fn healthy_later_deadline_and_lane_allow_complete_replay_and_retry() {
    let run = run();
    let deadline = ScopedSmtDeadline::install(Duration::from_secs(60));
    let lane = ScopedLaneCancellation::install(
        crate::CancellationToken::new(),
        Some(Arc::new(AtomicBool::new(false))),
    );
    let checked = run
        .run_checked_replay(Duration::from_secs(60))
        .expect("healthy caller limits permit full checked evidence");
    assert_eq!(
        checked.summary().obligations[0].payload_format,
        Format::CompactGroundDerivationV1
    );
    drop(checked);
    drop(lane);
    drop(deadline);
    run.run_checked_replay(Duration::from_secs(60))
        .expect("healthy scopes do not poison later replay");
}
