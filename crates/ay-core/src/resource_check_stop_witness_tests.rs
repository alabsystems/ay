// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A witnessed stop is captured with its witness, an opaque one without, and
//! the plain capture is unchanged by either.

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn a_witnessed_stop_is_captured_with_its_witness_and_restored_without_it() {
    let opaque: CheckStop = Arc::new(|| false);
    let _outer = enter_check_stop(Arc::clone(&opaque));
    let (stop, witness) = current_check_stop_and_witness();
    assert!(Arc::ptr_eq(&stop.unwrap().unwrap(), &opaque));
    assert!(witness.is_none(), "an embedder's stop is opaque");

    let flag = Arc::new(AtomicBool::new(false));
    let read = Arc::clone(&flag);
    let witnessed: CheckStop = Arc::new(move || read.load(Ordering::Relaxed));
    {
        let _inner = enter_witnessed_check_stop(
            Arc::clone(&witnessed),
            CheckStopWitness::new([Arc::clone(&flag)]),
        );
        let (stop, witness) = current_check_stop_and_witness();
        assert!(Arc::ptr_eq(&stop.unwrap().unwrap(), &witnessed));
        assert!(witness.expect("entered with its witness").quiet());
        assert!(
            Arc::ptr_eq(&current_check_stop().unwrap().unwrap(), &witnessed),
            "the plain capture returns the exact stop"
        );
        flag.store(true, Ordering::Relaxed);
        assert!(check_stop_requested(), "the stop itself is still polled");
        flag.store(false, Ordering::Relaxed);
    }
    let (stop, witness) = current_check_stop_and_witness();
    assert!(Arc::ptr_eq(&stop.unwrap().unwrap(), &opaque));
    assert!(witness.is_none(), "the enclosing stop is restored, opaque");
}

#[test]
fn a_witness_is_quiet_only_while_every_flag_is_down() {
    let flags = [
        Arc::new(AtomicBool::new(false)),
        Arc::new(AtomicBool::new(false)),
    ];
    let witness = CheckStopWitness::new(flags.iter().cloned());
    assert!(witness.quiet() || process_cancelled());
    for flag in &flags {
        flag.store(true, Ordering::Relaxed);
        assert!(!witness.quiet());
        flag.store(false, Ordering::Relaxed);
    }
    assert!(!CheckStopWitness::new([Arc::new(AtomicBool::new(true))]).quiet());
}

#[test]
fn a_capture_that_fails_carries_no_witness() {
    let flag = Arc::new(AtomicBool::new(false));
    let _scope = enter_witnessed_check_stop(
        Arc::new(|| false),
        CheckStopWitness::new([Arc::clone(&flag)]),
    );
    CHECK_STOP.with(|cell| {
        let _borrowed = cell.borrow_mut();
        let (stop, witness) = current_check_stop_and_witness();
        assert!(matches!(stop, Err(CheckStopCaptureError::Borrowed)));
        assert!(witness.is_none());
    });
}
