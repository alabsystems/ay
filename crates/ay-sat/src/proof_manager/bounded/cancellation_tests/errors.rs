// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use std::io::Write;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

#[test]
fn reached_malformed_and_expired_deadline_errors_are_not_overwritten() {
    let mut malformed = manager();
    let error = malformed
        .emit_bounded_empty_rup_step_with_cancellation(&[], Some(Instant::now()), &|| {
            panic!("empty hints are rejected before polling")
        })
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    assert!(!is_bounded_emission_cancelled(&error));
    assert!(!malformed.has_file_visible_terminal_empty());

    let mut expired = manager();
    let error = expired
        .emit_bounded_empty_rup_step_with_cancellation(&[1, 2, 3], Some(Instant::now()), &|| {
            panic!("reached deadline is rejected before polling")
        })
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    assert_eq!(error.to_string(), "bounded LRAT emission deadline exceeded");
    assert!(!is_bounded_emission_cancelled(&error));
    assert!(expired.has_io_error());
    assert_eq!(expired.added_count(), 0);
    assert!(expired.into_output().into_inner().is_err());

    let mut unknown = manager();
    let polls = Cell::new(0usize);
    let error = unknown
        .emit_bounded_empty_rup_step_with_cancellation(&[99], None, &|| {
            polls.set(polls.get() + 1);
            assert_eq!(polls.get(), 1);
            true
        })
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    assert!(!is_bounded_emission_cancelled(&error));
}

struct FailingSink(Arc<AtomicUsize>);

impl Write for FailingSink {
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        self.0.fetch_add(1, Ordering::Relaxed);
        Err(io::Error::new(
            io::ErrorKind::BrokenPipe,
            "manager frozen sink failure",
        ))
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn original_sink_error_returns_without_post_error_poll_and_closes_authority() {
    let writes = Arc::new(AtomicUsize::new(0));
    let mut manager = manager_with_output(ProofOutput::lrat_binary(FailingSink(writes.clone()), 3));
    let error = manager
        .emit_bounded_empty_rup_step_with_cancellation(&[1, 2, 3], None, &|| {
            assert_eq!(writes.load(Ordering::Relaxed), 0, "post-error callback");
            true
        })
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
    assert_eq!(error.to_string(), "manager frozen sink failure");
    assert!(!is_bounded_emission_cancelled(&error));
    assert_eq!(writes.load(Ordering::Relaxed), 1);
    assert!(manager.has_io_error());
    assert!(!manager.has_file_visible_terminal_empty());
    assert!(manager.into_output().into_inner().is_err());
}

#[test]
fn caught_flush_callback_panic_revokes_an_existing_terminal() {
    let mut manager = manager();
    emit(&mut manager, &|| true).unwrap();
    assert!(manager.has_file_visible_terminal_empty());
    assert!(catch_unwind(AssertUnwindSafe(|| {
        let _ =
            manager.flush_with_cancellation(&|| panic!("deliberate finalization callback panic"));
    }))
    .is_err());
    assert!(manager.has_io_error());
    assert!(!manager.has_file_visible_terminal_empty());
    let error = manager
        .flush_with_cancellation(&|| panic!("caught panic cannot revive control"))
        .unwrap_err();
    assert!(is_bounded_emission_cancelled(&error));
    assert!(manager.into_output().into_inner().is_err());
}

#[test]
fn accepted_final_callback_cannot_extend_original_deadline() {
    let mut manager = manager();
    let deadline = Instant::now() + Duration::from_millis(20);
    let error = manager
        .controlled_bounded_emission(|manager| {
            manager.admit_bounded_emission(Some(deadline), &|| {
                while Instant::now() < deadline {
                    std::hint::spin_loop();
                }
                true
            })
        })
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    assert!(!is_bounded_emission_cancelled(&error));
    assert!(manager.has_io_error());
    assert!(!manager.has_file_visible_terminal_empty());
    assert!(manager.into_output().into_inner().is_err());
}
