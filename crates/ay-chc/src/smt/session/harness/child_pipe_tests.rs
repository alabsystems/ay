// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The harness's z3 driver against a z3 that exits without reading its script.
//!
//! This crate is built with the `unix_hardened` Trust profile, whose `main`
//! runs with SIGPIPE at `SIG_DFL`: feeding a script through a plain
//! `ChildStdin` to a z3 that had already exited killed the differential run
//! with exit 141, where the driver is documented to return a short verdict
//! list. Each scenario runs alone ([`run_alone`]), where a bypass of
//! `ChildPipeWriter` is a SIGPIPE death named as one. The script is larger than
//! a pipe, so the write is parked on the full pipe when the fake z3 exits.

use super::*;
use ay_test_support::sigpipe::run_alone;

/// A "z3" that reads nothing and exits at once.
fn exits_unread_z3(directory: &Path) -> Z3 {
    use std::os::unix::fs::PermissionsExt as _;
    let path = directory.join("z3");
    std::fs::write(&path, "#!/bin/sh\nexit 0\n").expect("write fake z3");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
        .expect("make fake z3 executable");
    Z3 {
        path,
        identity: "fake z3 that exits unread".to_string(),
    }
}

/// Several pipe buffers of `(check-sat)` queries.
fn oversized_script() -> String {
    "(check-sat)\n".repeat(64 * 1024)
}

#[test]
fn run_against_a_z3_that_exits_unread_is_a_short_answer_not_a_kill() {
    if !run_alone(
        module_path!(),
        "run_against_a_z3_that_exits_unread_is_a_short_answer_not_a_kill",
    )
    .expect("re-exec this test alone")
    {
        return;
    }
    let directory = tempfile::tempdir().expect("tempdir");
    let z3 = exits_unread_z3(directory.path());
    assert_eq!(z3.run(&oversized_script(), 5), [] as [Verdict; 0]);
}

#[test]
fn run_marked_against_a_z3_that_exits_unread_is_all_unknown_not_a_kill() {
    if !run_alone(
        module_path!(),
        "run_marked_against_a_z3_that_exits_unread_is_all_unknown_not_a_kill",
    )
    .expect("re-exec this test alone")
    {
        return;
    }
    let directory = tempfile::tempdir().expect("tempdir");
    let z3 = exits_unread_z3(directory.path());
    assert_eq!(
        z3.run_marked(&oversized_script(), 3, 5),
        vec![Verdict::Unknown; 3]
    );
}
