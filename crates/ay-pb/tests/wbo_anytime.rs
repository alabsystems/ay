// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AY-SAT-8, end to end on the built `ay-pb`.
//!
//! 1. `elf.rf7` (all-soft WBO, one core, 60 s): the first `o` line reaches
//!    stdout within seconds, not with the final answer at the deadline, and
//!    the optimum, 1, is proven well before the 35 s the uncapped LP floor of
//!    the native-OLL pre-pass took. The measured build printed nothing but its
//!    banner until its own deadline (`--timeout 20000`: `o 8385` at 20.3 s),
//!    because the WBO arm suppressed every intermediate `o` line, and its
//!    pre-pass spent the whole slice in the LP floor. Timing test: release
//!    builds only.
//! 2. A WBO run whose wind-down stalls after SIGTERM (debug-only hook
//!    `AY_PB_TEST_STALL_BEFORE_RESULT_MS`) gets its checked model out through
//!    the SIGTERM watchdog's forced flush. The emergency store used to be
//!    disarmed for WBO, so that flush printed `s UNKNOWN`. (A cooperative
//!    SIGTERM already printed the cached WBO incumbent before the change;
//!    only the watchdog and panic paths were affected.)

#![cfg(unix)]

use std::io::{BufRead, BufReader};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

const FIXTURE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/instances/elf.rf7.ucl--soft-0-100-0.wbo"
);

/// Parses the `v` lines into one value per WBO variable; panics on a
/// variable outside the instance, a repeated variable or a missing one.
fn parse_model(lines: &[String], num_vars: usize) -> Vec<bool> {
    let mut values: Vec<Option<bool>> = vec![None; num_vars];
    for line in lines.iter().filter(|line| line.starts_with("v")) {
        for token in line.split_whitespace().skip(1) {
            let (value, name) = match token.strip_prefix('-') {
                Some(name) => (false, name),
                None => (true, token),
            };
            let index: usize = name
                .strip_prefix('x')
                .and_then(|digits| digits.parse().ok())
                .unwrap_or_else(|| panic!("malformed v token {token:?}"));
            assert!(
                (1..=num_vars).contains(&index),
                "v line names x{index}, outside the {num_vars} variables"
            );
            assert!(
                values[index - 1].replace(value).is_none(),
                "x{index} assigned twice"
            );
        }
    }
    values
        .into_iter()
        .enumerate()
        .map(|(index, value)| value.unwrap_or_else(|| panic!("x{} unassigned", index + 1)))
        .collect()
}

/// Reads `child`'s stdout lines on a thread, stamped with their arrival time.
fn stamped_lines(child: &mut std::process::Child) -> mpsc::Receiver<(Duration, String)> {
    let stdout = child.stdout.take().expect("stdout piped");
    let started = Instant::now();
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        for line in BufReader::new(stdout).lines() {
            let Ok(line) = line else { break };
            if tx.send((started.elapsed(), line)).is_err() {
                break;
            }
        }
    });
    rx
}

#[test]
#[cfg_attr(debug_assertions, ignore = "timing test: run with --release")]
fn wbo_rf7_streams_its_first_o_at_once_and_proves_the_optimum_early() {
    let wbo = ay_pb::parse_wbo(&std::fs::read_to_string(FIXTURE).expect("read fixture"))
        .expect("fixture should parse");
    let num_vars = usize::try_from(wbo.num_vars).expect("fits usize");

    // One core, as the scoreboard runs the job, with its 60 s budget: the
    // pre-pass slice is 36 s, so the capped LP floor gets 12 s where the
    // uncapped one took 35 s.
    let mut child = Command::new(env!("CARGO_BIN_EXE_ay-pb"))
        .args(["pb", "solve", "--timeout", "60000"])
        .arg(FIXTURE)
        .env("NBCORE", "1")
        .env_remove("AY_PB_LP_FLOOR_MS")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn ay-pb");
    let rx = stamped_lines(&mut child);
    let mut lines: Vec<(Duration, String)> = Vec::new();
    let hard_stop = Instant::now() + Duration::from_secs(75);
    while let Ok(entry) = rx.recv_timeout(hard_stop.saturating_duration_since(Instant::now())) {
        lines.push(entry);
    }
    let _ = child.kill();
    let _ = child.wait();

    let first_o = lines
        .iter()
        .find(|(_, line)| line.starts_with("o "))
        .unwrap_or_else(|| panic!("no o line: {lines:?}"));
    assert!(
        first_o.0 < Duration::from_secs(5),
        "the first incumbent must stream at once, not with the final answer: {lines:?}"
    );
    let status = lines
        .iter()
        .find(|(_, line)| line.starts_with("s "))
        .unwrap_or_else(|| panic!("no s line: {lines:?}"));
    assert_eq!(status.1, "s OPTIMUM FOUND", "{lines:?}");
    assert!(
        status.0 < Duration::from_secs(30),
        "rf7 must be proven before the 35 s the uncapped LP floor took: {lines:?}"
    );

    let text: Vec<String> = lines.into_iter().map(|(_, line)| line).collect();
    let costs: Vec<i128> = text
        .iter()
        .filter_map(|line| line.strip_prefix("o "))
        .map(|value| value.trim().parse().expect("o value is an integer"))
        .collect();
    assert!(
        costs.windows(2).all(|pair| pair[1] < pair[0]),
        "o lines must strictly improve: {costs:?}"
    );
    assert_eq!(costs.last(), Some(&1), "the optimum of elf.rf7 is 1");
    let model = parse_model(&text, num_vars);
    assert_eq!(
        ay_pb::wbo_admissible_cost(&wbo, &model),
        Some(1),
        "the printed model must be a WBO model of cost 1"
    );
}

/// The forced flush of the SIGTERM watchdog prints the checked WBO model. The
/// solve finishes at once, then the debug-only hook stalls the cooperative
/// write, so only the watchdog can print the answer.
#[test]
#[cfg(debug_assertions)]
fn wbo_sigterm_watchdog_flush_prints_the_checked_model() {
    // Hard x1 + x2 >= 1; soft [3] x1 >= 1. Optimum 0 at x1 = 1.
    let text = concat!("soft: 5 ;\n", "+1 x1 +1 x2 >= 1 ;\n", "[3] +1 x1 >= 1 ;\n");
    let wbo = ay_pb::parse_wbo(text).expect("fixture should parse");
    let dir = std::env::temp_dir().join(format!("ay-wbo-flush-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let bench = dir.join("tiny.wbo");
    std::fs::write(&bench, text).expect("write bench");

    let mut child = Command::new(env!("CARGO_BIN_EXE_ay-pb"))
        .args(["pb", "solve", "--timeout", "60000"])
        .arg(&bench)
        .env("NBCORE", "1")
        .env("AY_PB_TEST_STALL_BEFORE_RESULT_MS", "60000")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn ay-pb");
    let rx = stamped_lines(&mut child);

    // Let it solve and enter the stall, then deliver SIGTERM.
    std::thread::sleep(Duration::from_millis(1500));
    let kill = Command::new("kill")
        .args(["-TERM", &child.id().to_string()])
        .status()
        .expect("send SIGTERM");
    assert!(kill.success(), "kill -TERM must be delivered");
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if child.try_wait().expect("try_wait").is_some() {
            break;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            panic!("ay-pb must exit promptly after SIGTERM");
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    let mut text_lines: Vec<String> = Vec::new();
    while let Ok((_, line)) = rx.recv_timeout(Duration::from_secs(2)) {
        text_lines.push(line);
    }
    let _ = std::fs::remove_dir_all(&dir);

    let statuses: Vec<&String> = text_lines
        .iter()
        .filter(|line| line.starts_with("s "))
        .collect();
    assert_eq!(statuses.len(), 1, "exactly one s line: {text_lines:?}");
    assert_eq!(
        statuses[0], "s SATISFIABLE",
        "the forced flush must print the checked WBO model, not UNKNOWN: {text_lines:?}"
    );
    let model = parse_model(&text_lines, 2);
    let cost = ay_pb::wbo_admissible_cost(&wbo, &model);
    assert!(
        cost.is_some(),
        "the flushed model must be a WBO model: {text_lines:?}"
    );
    // When an `o` line was streamed, the flushed model is that incumbent.
    if let Some(last_o) = text_lines
        .iter()
        .filter_map(|line| line.strip_prefix("o "))
        .map(|value| value.trim().parse::<i128>().expect("o value is an integer"))
        .next_back()
    {
        assert_eq!(cost, Some(last_o), "{text_lines:?}");
    }
}
