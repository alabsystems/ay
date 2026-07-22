// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch coverage for the strings witness/escalation lanes.
//!
//! The strings increments (W4/W5/W6/W7 witness search, P2/P3 preregister
//! escalations, the W1-W3 `AY_STR_WITNESS` family) are all DEFAULT-ON with a
//! per-lane `=0` env kill switch. When each lane was flipped default-on, the
//! flags-off pipeline was A/B-measured byte-identical — but that old
//! defaults-off mode had no executable regression coverage afterwards,
//! because the gates are `OnceLock`-cached env reads and cannot be toggled
//! in-process. These tests restore that coverage the only way that works:
//! spawning the `ay` binary as a subprocess with the kill switches set.
//!
//! Every solve runs under `--self-check` (fail-closed: a `sat` is only
//! printed when AY's own model validation certifies it), so `sat` here pins
//! both the verdict AND a validated model in each mode.

use std::process::Command;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

/// Every strings-lane kill switch, so the "all off" run exercises the
/// pre-flip (defaults-off) pipeline end to end.
const ALL_KILL_SWITCHES: &[&str] = &[
    "AY_STR_WITNESS",
    "AY_STR_W4",
    "AY_STR_W5",
    "AY_STR_W6",
    "AY_STR_W7",
    "AY_STR_P2",
    "AY_STR_P3",
];

/// Small QF_S problems that were sat BEFORE the default-on flips: their
/// models come from equality-with-literal / word-equation reasoning, not
/// from the gated witness-search lanes, so they must stay sat with every
/// lane killed.
const QF_S_SAT_PROBLEMS: &[(&str, &str)] = &[
    (
        "literal_pin",
        "(set-logic QF_S)\n\
         (declare-const x String)\n\
         (assert (= x \"ab\"))\n\
         (assert (= (str.len x) 2))\n\
         (check-sat)\n\
         (get-model)\n",
    ),
    (
        "concat_split",
        "(set-logic QF_S)\n\
         (declare-const x String)\n\
         (declare-const y String)\n\
         (assert (= (str.++ x y) \"hello\"))\n\
         (assert (= (str.len x) 2))\n\
         (check-sat)\n\
         (get-model)\n",
    ),
];

/// Spawn `ay solve --self-check` on `input` (via stdin) with the given env
/// pairs, and return stdout+stderr.
fn solve_self_check(input: &str, env: &[(&str, &str)]) -> (String, String) {
    let mut cmd = Command::new(ay_binary());
    cmd.args(["solve", "--self-check", "--stdin"]);
    for (k, v) in env {
        cmd.env(k, v);
    }
    let output = cmd
        .output_timeout_with_stdin(input.as_bytes(), DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay solve --self-check --stdin");
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

fn assert_certified_sat(name: &str, mode: &str, stdout: &str, stderr: &str) {
    // `sat` is a substring of `unsat`, so check the verdict line exactly.
    let verdict = stdout
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("<no verdict line>");
    assert_eq!(
        verdict, "sat",
        "[{name}/{mode}] expected a self-check-certified sat; \
         stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("define-fun"),
        "[{name}/{mode}] (get-model) after certified sat should print a \
         model; stdout={stdout} stderr={stderr}"
    );
}

/// Pre-flip mode: every strings lane killed via its `=0` switch. This is the
/// executable pin of the old defaults-off pipeline that the default-on flips
/// (W4/P3: 87796d22f9, 360a85b477; and the later W5/W6/W7 flips) previously
/// left covered only by flip-time A/B measurements.
#[test]
fn qf_s_sat_survives_all_string_kill_switches() {
    let env: Vec<(&str, &str)> = ALL_KILL_SWITCHES.iter().map(|k| (*k, "0")).collect();
    for (name, input) in QF_S_SAT_PROBLEMS {
        let (stdout, stderr) = solve_self_check(input, &env);
        assert_certified_sat(name, "all-lanes-killed", &stdout, &stderr);
    }
}

/// Each master switch killed individually (the exact `=0` contract each gate
/// documents), with the remaining lanes at their defaults.
#[test]
fn qf_s_sat_survives_each_string_kill_switch_alone() {
    for switch in ALL_KILL_SWITCHES {
        for (name, input) in QF_S_SAT_PROBLEMS {
            let (stdout, stderr) = solve_self_check(input, &[(switch, "0")]);
            assert_certified_sat(name, &format!("{switch}=0"), &stdout, &stderr);
        }
    }
}

/// Default mode (no env): the flipped default-on pipeline certifies the same
/// problems, so both sides of every kill switch are pinned by execution.
#[test]
fn qf_s_sat_certified_in_default_on_mode() {
    for (name, input) in QF_S_SAT_PROBLEMS {
        let (stdout, stderr) = solve_self_check(input, &[]);
        assert_certified_sat(name, "defaults", &stdout, &stderr);
    }
}
