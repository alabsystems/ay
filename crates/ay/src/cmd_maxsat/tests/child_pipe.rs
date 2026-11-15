// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A campaign sidecar that stops reading must cost the campaign an error,
//! never the `ay` process.
//!
//! `ay` is built with the `unix_hardened` Trust profile, whose `main` runs with
//! SIGPIPE at `SIG_DFL`: a registration written through a plain `ChildStdin`
//! to a watch server that had stopped reading killed `ay` with exit 141 before
//! the registration's `io::Result` was looked at. The scenario runs alone
//! ([`run_alone`]), where a bypass of `ChildPipeWriter` is a SIGPIPE death
//! named as one.

#![cfg(unix)]

use super::*;
use ay_test_support::sigpipe::{run_alone, stops_reading_watch_server};

/// A watch server that closes its stdin while it keeps heartbeating passes
/// every health check, so the next registration writes to a pipe with no
/// reader: that registration must fail with the write error.
#[test]
fn maxsat_watch_server_that_stops_reading_fails_the_registration_not_ay() {
    use std::os::unix::process::CommandExt as _;

    if !run_alone(
        module_path!(),
        "maxsat_watch_server_that_stops_reading_fails_the_registration_not_ay",
    )
    .expect("re-exec this test alone")
    {
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let fake_server = dir.path().join("watch-server.py");
    let script = stops_reading_watch_server(MAXSAT_WATCHDOG_SERVER_READY)
        .expect("the ready marker is UTF-8");
    fs::write(&fake_server, script).expect("write fake watch server");
    let server = MaxSatWatchdogServer::new(OomGuardSource::Checkout(fake_server));

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
        .register(target.id(), 10_000, "first registration", None)
        .expect("the server answers the first registration");
    let Err(error) = server.register(target.id(), 10_000, "second registration", None) else {
        panic!("a server that stopped reading must fail the registration");
    };
    assert!(
        format!("{error:#}").contains("registering MaxSAT RSS watchdog"),
        "the failure is the registration write: {error:#}"
    );
    drop(first);
    let _ = target.kill();
    let _ = target.wait();
    drop(server);
}
