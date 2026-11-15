// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A sidecar or target that stops reading must cost the harness an error, never
//! the process.
//!
//! This crate is built with the `unix_hardened` Trust profile, whose `main`
//! runs with SIGPIPE at `SIG_DFL`: a write through a plain `ChildStdin` to a
//! child that has gone away killed the harness (and a whole `ay-bench` test
//! run) with exit 141 before the `io::Result` the callers handle was ever
//! looked at. Each scenario runs alone ([`run_alone`]), where a bypass of
//! `ChildPipeWriter` is a SIGPIPE death named as one.
//!
//! Only where `ChildPipeWriter` keeps SIGPIPE off a dead child's pipe (Linux,
//! Android, Apple): on another Unix it passes writes through, and these
//! scenarios would die of the signal they test for.

#![cfg(all(
    unix,
    any(
        target_os = "android",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    )
))]

use super::*;
use ay_test_support::sigpipe::{run_alone, stops_reading_watch_server};

/// The transcript runner's documented contract: a target that closes stdin
/// before consuming the whole transcript is child behaviour, reported as
/// `stdin_complete: false` beside its exit status. The input is larger than a
/// pipe, so the writer is parked on the full pipe when the target exits.
#[test]
fn guarded_transcript_target_that_exits_unread_is_incomplete_not_a_kill() {
    if !run_alone(
        module_path!(),
        "guarded_transcript_target_that_exits_unread_is_incomplete_not_a_kill",
    )
    .expect("re-exec this test alone")
    {
        return;
    }
    let resources = PlannedResources::for_test(&crate::runner::repo_root_public(), 10_000);
    let stdin = vec![b'i'; GUARDED_TRANSCRIPT_INPUT_LIMIT];
    let output = resources
        .run_external_transcript(
            "/bin/sh",
            ["-c", "exit 3"],
            &stdin,
            Duration::from_secs(10),
            "unread guarded transcript",
        )
        .expect("an unread transcript is the target's behaviour, not a harness failure");
    assert_eq!(output.status.and_then(|status| status.code()), Some(3));
    assert!(!output.stdin_complete, "the target read nothing");
    assert!(!output.timed_out && !output.memout);
}

/// A watch server that stops reading its stdin while it still heartbeats
/// passes the health check, so the next registration writes to a pipe with no
/// reader. That registration must fail with the write error, and the campaign
/// parent must live to report it.
#[test]
fn watch_server_that_stops_reading_fails_the_registration_not_the_parent() {
    use std::os::unix::process::CommandExt as _;

    if !run_alone(
        module_path!(),
        "watch_server_that_stops_reading_fails_the_registration_not_the_parent",
    )
    .expect("re-exec this test alone")
    {
        return;
    }
    let temp = tempfile::tempdir().expect("tempdir");
    let fake_server = temp.path().join("watch-server.py");
    let script =
        stops_reading_watch_server(WATCHDOG_SERVER_READY).expect("the ready marker is UTF-8");
    std::fs::write(&fake_server, script).expect("write fake watch server");
    let server = SharedWatchdogServer::new(fake_server);

    // A target of our own in its own process group: the registration's
    // watchdog kills that group when it drops.
    let mut target = Command::new("/bin/sh")
        .args(["-c", "exec sleep 60"])
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn watch target");
    let first = server
        .register(target.id(), 10_000, "first registration")
        .expect("the server answers the first registration");
    let error = server
        .register(target.id(), 10_000, "second registration")
        .expect_err("a server that stopped reading must fail the registration");
    assert!(
        error.to_string().contains("registering RSS watchdog"),
        "the failure is the registration write: {error}"
    );
    drop(first);
    let _ = target.kill();
    let _ = target.wait();
    drop(server);
}
