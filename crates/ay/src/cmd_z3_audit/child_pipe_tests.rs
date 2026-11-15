// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The audit's stdin feeders against a child that exits without reading.
//!
//! `ay` is built with the `unix_hardened` Trust profile, whose `main` runs with
//! SIGPIPE at `SIG_DFL`: a z3 (or an audited `ay`) that died before reading its
//! input killed `ay z3-audit` with exit 141 on the feeder's write, before the
//! error the caller reports was ever returned. Each scenario runs alone
//! ([`run_alone`]), where a bypass of `ChildPipeWriter` is a SIGPIPE death
//! named as one. The input is larger than a pipe, so the write is parked on
//! the full pipe when the child exits, whatever the scheduling.

#![cfg(unix)]

use super::*;
use ay_test_support::sigpipe::run_alone;

/// More than any pipe buffer holds.
const UNREAD_INPUT_BYTES: usize = 1 << 20;

#[test]
fn capture_with_stdin_reports_a_child_that_exits_unread() {
    if !run_alone(
        module_path!(),
        "capture_with_stdin_reports_a_child_that_exits_unread",
    )
    .expect("re-exec this test alone")
    {
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let input = vec![b'x'; UNREAD_INPUT_BYTES];
    let error =
        run_command_capture_with_stdin(dir.path(), Path::new("/bin/sh"), &["-c", "exit 3"], &input)
            .expect_err("the child read none of its input");
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe, "{error}");
}

#[test]
fn program_stdin_reports_a_child_that_exits_unread() {
    if !run_alone(
        module_path!(),
        "program_stdin_reports_a_child_that_exits_unread",
    )
    .expect("re-exec this test alone")
    {
        return;
    }
    let input = "x".repeat(UNREAD_INPUT_BYTES);
    let error = run_program_stdin(std::ffi::OsStr::new("/bin/sh"), &["-c", "exit 3"], &input)
        .expect_err("the child read none of its input");
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe, "{error}");
}
