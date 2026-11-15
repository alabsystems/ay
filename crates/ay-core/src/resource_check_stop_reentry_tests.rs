// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Mutex;

#[test]
fn observed_callback_can_enter_and_restore_a_nested_scope() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let original: CheckStop = Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst);
        let nested: CheckStop = Arc::new(|| false);
        let scope = enter_check_stop(Arc::clone(&nested));
        assert!(Arc::ptr_eq(
            &current_check_stop().unwrap().unwrap(),
            &nested
        ));
        assert!(!check_stop_requested());
        drop(scope);
        true
    });
    let _scope = enter_check_stop(Arc::clone(&original));
    assert!(check_stop_requested());
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert!(Arc::ptr_eq(
        &current_check_stop().unwrap().unwrap(),
        &original
    ));
}

#[test]
fn scope_restoration_drops_displaced_callback_without_borrowing_tls() {
    struct Cleanup(Arc<AtomicBool>);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            assert!(!check_stop_requested());
            let nested = enter_check_stop(Arc::new(|| false));
            assert!(!check_stop_requested());
            drop(nested);
            self.0.store(true, Ordering::SeqCst);
        }
    }
    let original: CheckStop = Arc::new(|| false);
    let _original = enter_check_stop(Arc::clone(&original));
    let cleaned = Arc::new(AtomicBool::new(false));
    let cleanup = Cleanup(Arc::clone(&cleaned));
    let scope = enter_check_stop(Arc::new(move || {
        let _keep = &cleanup;
        true
    }));
    drop(scope);
    assert!(cleaned.load(Ordering::SeqCst));
    assert!(Arc::ptr_eq(
        &current_check_stop().unwrap().unwrap(),
        &original
    ));
}

#[test]
fn observed_last_arc_cleanup_can_reenter_after_callback_removes_its_scope() {
    struct Cleanup(Arc<AtomicBool>);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let scope = enter_check_stop(Arc::new(|| false));
            assert!(!check_stop_requested());
            drop(scope);
            self.0.store(true, Ordering::SeqCst);
        }
    }
    let scope = Arc::new(Mutex::new(None::<CheckStopScope>));
    let callback_scope = Arc::clone(&scope);
    let cleaned = Arc::new(AtomicBool::new(false));
    let cleanup = Cleanup(Arc::clone(&cleaned));
    *scope.lock().unwrap() = Some(enter_check_stop(Arc::new(move || {
        let _keep = &cleanup;
        drop(callback_scope.lock().unwrap().take());
        false
    })));
    assert!(!check_stop_requested());
    assert!(cleaned.load(Ordering::SeqCst));
    assert!(scope.lock().unwrap().is_none());
}

#[test]
fn unavailable_callback_capture_is_a_stop_not_healthy_absence() {
    CHECK_STOP.with(|cell| {
        let _borrowed = cell.borrow_mut();
        assert!(check_stop_requested());
    });
    assert!(current_check_stop().is_ok());
}
