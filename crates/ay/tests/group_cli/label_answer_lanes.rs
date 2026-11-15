// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Answer lanes for the label-conformance repro tests: `--z3-mode` on stdin
//! and on a file, and plain mode on a file, quiet and in the default
//! posture.

use std::io::Write;
use std::process::{Command, Stdio};

fn run_stdin(input: &str, args: &[&str]) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay -in");
    child
        .stdin
        .as_mut()
        .expect("child stdin")
        .write_all(input.as_bytes())
        .expect("write SMT-LIB input");
    child.wait_with_output().expect("wait for ay -in")
}

fn run_file(input: &str, args: &[&str]) -> std::process::Output {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("input.smt2");
    std::fs::write(&path, input).expect("write SMT-LIB file");
    Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg(&path)
        .current_dir(dir.path())
        .output()
        .expect("run ay on a file")
}

fn answers(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

/// Check the answers in z3 mode (stdin and file) and in plain mode (quiet
/// and default posture).
fn assert_answers(name: &str, input: &str, z3_mode: &[&str], plain: &[&str]) {
    for (lane, output, expected) in [
        (
            "z3 stdin",
            run_stdin(input, &["-q", "--z3-mode", "-in"]),
            z3_mode,
        ),
        ("z3 file", run_file(input, &["-q", "--z3-mode"]), z3_mode),
        ("plain file", run_file(input, &["-q"]), plain),
        ("default file", run_file(input, &[]), plain),
    ] {
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            answers(&stdout),
            expected,
            "{name}, {lane}:\n{input}\nstdout: {stdout}\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

/// A repro and its sat twin: (name, script, z3-mode answer, plain answer).
pub(crate) type Case = (&'static str, &'static str, &'static str, &'static str);

pub(crate) fn assert_pairs(pairs: &[(Case, Case)]) {
    for ((name, input, z3_mode, plain), (twin_name, twin, twin_z3_mode, twin_plain)) in pairs {
        assert_answers(name, input, &[*z3_mode], &[*plain]);
        assert_answers(twin_name, twin, &[*twin_z3_mode], &[*twin_plain]);
    }
}

/// Check every answer of a script in z3 mode and plain mode, on stdin and on
/// a file, and in the default posture on stdin and on a file.
pub(crate) fn assert_answers_on_every_input(
    name: &str,
    input: &str,
    z3_mode: &[&str],
    plain: &[&str],
) {
    for (lane, output, expected) in [
        (
            "z3 stdin",
            run_stdin(input, &["-q", "--z3-mode", "-in"]),
            z3_mode,
        ),
        ("z3 file", run_file(input, &["-q", "--z3-mode"]), z3_mode),
        ("plain stdin", run_stdin(input, &["-q", "-in"]), plain),
        ("plain file", run_file(input, &["-q"]), plain),
        ("default stdin", run_stdin(input, &["-in"]), plain),
        ("default file", run_file(input, &[]), plain),
    ] {
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            answers(&stdout),
            expected,
            "{name}, {lane}:\n{input}\nstdout: {stdout}\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

/// A script and the answers to its queries: (name, script, z3-mode answers,
/// plain answers).
pub(crate) type Script = (
    &'static str,
    &'static str,
    &'static [&'static str],
    &'static [&'static str],
);

/// Check each repro and its twin on every input lane.
pub(crate) fn assert_script_pairs_on_every_input(pairs: &[(Script, Script)]) {
    for (repro, twin) in pairs {
        for (name, input, z3_mode, plain) in [repro, twin] {
            assert_answers_on_every_input(name, input, z3_mode, plain);
        }
    }
}
