// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PAR-2 conformance: an `s` line must land PROMPTLY after SIGTERM even when
//! the solve thread cannot wind down (competition harnesses SIGKILL a few
//! seconds after SIGTERM; a silent kill forfeits the instance entirely).
//!
//! The debug-only `AY_PB_TEST_STALL_BEFORE_RESULT_MS` hook simulates a stuck
//! wind-down: the solve completes but stalls before the final write, and the
//! SIGTERM flush watchdog must force out a fail-closed result within its
//! 800ms grace instead of leaving silence for the harness to kill.

#![cfg(unix)]

use std::io::Read;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

#[test]
fn sigterm_forces_prompt_s_line_when_wind_down_stalls() {
    let dir = std::env::temp_dir().join(format!("ay-sigterm-flush-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let bench = dir.join("trivial.opb");
    std::fs::write(
        &bench,
        "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n",
    )
    .expect("write bench");

    let mut child = Command::new(env!("CARGO_BIN_EXE_ay-pb"))
        .args(["pb", "solve", "--timeout", "60000"])
        .arg(&bench)
        .env("AY_PB_TEST_STALL_BEFORE_RESULT_MS", "60000")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn ay-pb");

    // Let it solve and enter the stall, then deliver SIGTERM.
    std::thread::sleep(Duration::from_millis(1500));
    let kill = Command::new("kill")
        .args(["-TERM", &child.id().to_string()])
        .status()
        .expect("send SIGTERM");
    assert!(kill.success(), "kill -TERM must be delivered");

    // The watchdog grace is 800ms; require the whole process gone well inside
    // any realistic harness SIGKILL window.
    let deadline = Instant::now() + Duration::from_secs(5);
    let status = loop {
        if let Some(status) = child.try_wait().expect("try_wait") {
            break status;
        }
        assert!(
            Instant::now() < deadline,
            "process must exit promptly after SIGTERM (watchdog failed)"
        );
        std::thread::sleep(Duration::from_millis(50));
    };
    let _ = status;

    let mut stdout = String::new();
    child
        .stdout
        .take()
        .expect("stdout piped")
        .read_to_string(&mut stdout)
        .expect("read stdout");

    let s_lines: Vec<&str> = stdout
        .lines()
        .filter(|line| line.starts_with("s "))
        .collect();
    assert_eq!(
        s_lines.len(),
        1,
        "exactly one s line must be flushed, got: {stdout:?}"
    );
    assert!(
        s_lines[0] == "s SATISFIABLE" || s_lines[0] == "s UNKNOWN",
        "flushed status must be fail-closed (SATISFIABLE from the VIG-gated \
         store, else UNKNOWN), got: {}",
        s_lines[0]
    );
    // A SATISFIABLE flush must carry its model.
    if s_lines[0] == "s SATISFIABLE" {
        assert!(
            stdout.lines().any(|line| line.starts_with("v ")),
            "SATISFIABLE flush must include a v line: {stdout:?}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn sigterm_watchdog_stands_down_on_normal_completion() {
    // No stall: the normal path emits and exits; the watchdog must not add a
    // second s line or extra output.
    let dir = std::env::temp_dir().join(format!("ay-sigterm-normal-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let bench = dir.join("trivial.opb");
    std::fs::write(
        &bench,
        "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n",
    )
    .expect("write bench");

    let output = Command::new(env!("CARGO_BIN_EXE_ay-pb"))
        .args(["pb", "solve", "--timeout", "10000"])
        .arg(&bench)
        .output()
        .expect("run ay-pb");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        stdout.lines().filter(|l| l.starts_with("s ")).count(),
        1,
        "exactly one s line on the normal path: {stdout:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
