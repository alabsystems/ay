// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::os::unix::process::ExitStatusExt as _;

fn status() -> ExitStatus {
    ExitStatus::from_raw(0)
}

#[test]
fn preexisting_breach_wins_but_cleanup_breach_cannot_replace_timeout() {
    for (breach, memout) in [(9, true), (10, true), (11, false)] {
        let result = finish_deadline_cleanup(
            Ok(10),
            Ok(status()),
            Ok(WatchdogOutcome {
                breached: true,
                breach_time_ns: Some(breach),
            }),
        )
        .expect("complete cleanup receipt");
        assert_eq!(result.memout, memout);
        assert_eq!(result.timed_out, !memout);
        assert!(result.status.expect("reaped status is retained").success());
    }
    let result = finish_deadline_cleanup(
        Ok(10),
        Ok(status()),
        Ok(WatchdogOutcome {
            breached: false,
            breach_time_ns: None,
        }),
    )
    .expect("ordinary deadline receipt");
    assert!(result.timed_out && !result.memout);
}

#[test]
fn missing_breach_timestamp_refuses_deadline_classification() {
    let error = finish_deadline_cleanup(
        Ok(10),
        Ok(status()),
        Ok(WatchdogOutcome {
            breached: true,
            breach_time_ns: None,
        }),
    )
    .expect_err("a breach without a timestamp has no admitted first cause");
    assert!(error.to_string().contains("breach timestamp is missing"));
}

#[test]
fn deadline_cleanup_retains_all_failures() {
    let error = finish_deadline_cleanup(
        Err(BenchError::msg("cannot timestamp timeout trigger")),
        Err(BenchError::msg("leader could not be reaped")),
        Err(BenchError::msg("terminal watchdog receipt missing")),
    )
    .expect_err("all failed prerequisites are retained");
    let message = error.to_string();
    for expected in [
        "cannot timestamp timeout trigger",
        "leader could not be reaped",
        "watchdog cleanup failed: terminal watchdog receipt missing",
    ] {
        assert!(message.contains(expected), "{message}");
    }
}

#[test]
#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
fn expired_guarded_run_is_killed_and_reaped_with_its_watchdog_receipt() {
    let resources =
        super::super::PlannedResources::for_test(&crate::runner::repo_root_public(), 64);
    let mut command = resources.external_command("/bin/sh");
    command.args(["-c", "sleep 30"]);
    let (mut child, watchdog) = resources
        .spawn_external_child(&mut command, "expired-run cleanup test")
        .expect("start guarded child");
    let result = terminate_after_deadline(&mut child, watchdog, "expired-run cleanup test")
        .expect("finish both child and watchdog cleanup");
    assert!(result.timed_out && !result.memout);
    assert!(result.status.is_some());
    assert!(child.try_wait().expect("query reaped child").is_some());
}
