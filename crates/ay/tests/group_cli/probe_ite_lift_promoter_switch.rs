// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--no-probe-ite-lift-promoter` is a flag (a574c240e documents it as one).
//!
//! Its `SolveAbSwitches` field was declared without `#[arg(long, ..)]`, which
//! made it a positional argument. Release builds then rejected the documented
//! flag with "unexpected argument", and every debug-assertion build (the test
//! profile) panicked in clap's command validation on EVERY solve invocation,
//! so no CLI integration test that spawns `ay` to solve could pass.

use std::io::Write;
use std::process::Command;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

const UNSAT: &str = "(set-logic QF_UF)\n\
                     (declare-const p Bool)\n\
                     (assert p)\n\
                     (assert (not p))\n\
                     (check-sat)\n";

fn solve(extra: &[&str]) -> (bool, String, String) {
    let mut input = tempfile::Builder::new()
        .suffix(".smt2")
        .tempfile()
        .expect("temp input");
    input.write_all(UNSAT.as_bytes()).expect("write input");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(extra)
        .arg("--no-proof")
        .arg(input.path())
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn a_plain_solve_parses_its_command_line() {
    let (ok, stdout, stderr) = solve(&[]);
    assert!(ok, "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert_eq!(stdout.trim(), "unsat", "stderr:\n{stderr}");
}

#[test]
fn the_documented_kill_switch_is_accepted() {
    let (ok, stdout, stderr) = solve(&["--no-probe-ite-lift-promoter"]);
    assert!(
        !stderr.contains("unexpected argument"),
        "the flag must parse: {stderr}"
    );
    assert!(ok, "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert_eq!(stdout.trim(), "unsat", "stderr:\n{stderr}");
}
