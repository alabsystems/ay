// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use std::cell::RefCell;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::rc::Rc;

enum Fault {
    None,
    Interrupted,
    BrokenPipeAfter(usize),
    Flush,
}

struct ShortSink {
    bytes: Rc<RefCell<Vec<u8>>>,
    writes: Rc<Cell<usize>>,
    fault: Fault,
}

impl Write for ShortSink {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.writes.set(self.writes.get() + 1);
        match self.fault {
            Fault::Interrupted => return Err(io::Error::from(io::ErrorKind::Interrupted)),
            Fault::BrokenPipeAfter(limit) if self.bytes.borrow().len() >= limit => {
                return Err(io::Error::new(
                    io::ErrorKind::BrokenPipe,
                    "frozen sink failure",
                ));
            }
            _ => {}
        }
        if bytes.is_empty() {
            return Ok(0);
        }
        self.bytes.borrow_mut().push(bytes[0]);
        Ok(1)
    }

    fn flush(&mut self) -> io::Result<()> {
        match self.fault {
            Fault::Flush => Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "frozen flush failure",
            )),
            _ => Ok(()),
        }
    }
}

fn sink(fault: Fault) -> ShortSink {
    ShortSink {
        bytes: Rc::new(RefCell::new(Vec::new())),
        writes: Rc::new(Cell::new(0)),
        fault,
    }
}

#[test]
fn short_text_writes_preserve_bytes_and_late_refusal_is_terminal() {
    let accepted_sink = sink(Fault::None);
    let bytes = accepted_sink.bytes.clone();
    let mut accepted = LratWriter::new_text(accepted_sink, 2);
    accepted
        .add_bounded_prevalidated_rup_with_cancellation(&[literal(0, true)], &[1, 2], &|| true)
        .unwrap();
    assert_eq!(bytes.borrow().as_slice(), b"3 1 0 1 2 0\n");

    let refused_sink = sink(Fault::None);
    let bytes = refused_sink.bytes.clone();
    let writes = refused_sink.writes.clone();
    let mut refused = LratWriter::new_text(refused_sink, 2);
    let error = refused
        .add_bounded_prevalidated_rup_with_cancellation(&[literal(0, true)], &[1, 2], &|| {
            writes.get() < 5
        })
        .unwrap_err();
    assert!(is_bounded_emission_cancelled(&error));
    assert_eq!(bytes.borrow().as_slice(), b"3 1 0");
    assert_eq!(refused.added_count(), 0);
    assert!(refused.has_io_error());
    assert!(refused.into_inner().is_err());
    assert_eq!(writes.get(), 5);
}

#[test]
fn interrupted_sink_retries_only_until_typed_cancellation() {
    let interrupted = sink(Fault::Interrupted);
    let writes = interrupted.writes.clone();
    let mut writer = LratWriter::new_binary(interrupted, 2);
    let polls = Cell::new(0usize);
    let error = writer
        .add_bounded_prevalidated_rup_with_cancellation(&[], &[1, 2], &|| {
            polls.set(polls.get() + 1);
            polls.get() < 4
        })
        .unwrap_err();
    assert_eq!(writes.get(), 3);
    assert_eq!(polls.get(), 4);
    assert_eq!(error.kind(), io::ErrorKind::Other);
    assert!(is_bounded_emission_cancelled(&error));
    assert!(!is_bounded_emission_cancelled(&io::Error::from(
        io::ErrorKind::Interrupted
    )));
    assert!(!is_bounded_emission_cancelled(&io::Error::other(
        "bounded proof emission cancelled"
    )));
    assert!(writer
        .flush_with_cancellation(&|| panic!("must remain latched"))
        .is_err());
    assert_eq!(writes.get(), 3);
}

#[test]
fn ordinary_write_and_flush_errors_are_not_overwritten_by_later_callbacks() {
    let failed = sink(Fault::BrokenPipeAfter(3));
    let writes = failed.writes.clone();
    let mut writer = LratWriter::new_binary(failed, 2);
    let error = writer
        .add_bounded_prevalidated_rup_with_cancellation(&[], &[1, 2], &|| {
            assert!(writes.get() <= 3, "callback invoked after first sink error");
            true
        })
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
    assert_eq!(error.to_string(), "frozen sink failure");
    assert!(!is_bounded_emission_cancelled(&error));
    assert!(writer.has_io_error());
    assert_eq!(writer.added_count(), 0);

    let mut writer = LratWriter::new_binary(sink(Fault::Flush), 2);
    let polls = Cell::new(0usize);
    let error = writer
        .flush_with_cancellation(&|| {
            polls.set(polls.get() + 1);
            assert_eq!(polls.get(), 1);
            true
        })
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
    assert_eq!(error.to_string(), "frozen flush failure");
    assert!(writer.has_io_error());
}

#[test]
fn caught_callback_panic_poisoned_record_and_typed_retry_refusal() {
    let mut writer = LratWriter::new_binary(Vec::new(), 2);
    let polls = Cell::new(0usize);
    assert!(catch_unwind(AssertUnwindSafe(|| {
        let _ = writer.add_bounded_prevalidated_rup_with_cancellation(&[], &[1, 2], &|| {
            polls.set(polls.get() + 1);
            assert_ne!(polls.get(), 4, "deliberate callback panic after prefix");
            true
        });
    }))
    .is_err());
    assert!(!writer.get_ref().is_empty());
    assert!(writer.has_io_error());
    assert_eq!(writer.added_count(), 0);
    let error = writer
        .flush_with_cancellation(&|| panic!("poisoned callback retried"))
        .unwrap_err();
    assert!(is_bounded_emission_cancelled(&error));
    assert!(writer.into_inner().is_err());
}
