// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PAR-2 conformance fault-injection matrix (campaign M0): EVERY termination
//! of `pb solve` must emit EXACTLY ONE `s` line, fail-closed, no matter how
//! broken the input is. A silent hard exit is scored by the harness as a
//! forfeited instance; `s UNKNOWN` costs nothing and keeps the record clean.

use std::process::Command;

fn solve_output(args: &[&str]) -> (String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_ay-pb"))
        .args(["pb", "solve", "--timeout", "5000"])
        .args(args)
        .output()
        .expect("run ay-pb");
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

fn s_lines(stdout: &str) -> Vec<&str> {
    stdout.lines().filter(|l| l.starts_with("s ")).collect()
}

fn case_dir(case: &str) -> std::path::PathBuf {
    // Unique per CASE: the test binary runs cases on threads of one process,
    // so a pid-keyed shared dir races with sibling cleanups.
    let dir = std::env::temp_dir().join(format!("ay-fault-matrix-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    dir
}

#[test]
fn nonexistent_file_emits_single_unknown() {
    let (stdout, stderr) = solve_output(&["/nonexistent/definitely-missing.opb"]);
    assert_eq!(s_lines(&stdout), vec!["s UNKNOWN"], "stdout: {stdout:?}");
    assert!(stderr.contains("failed to read"), "stderr: {stderr:?}");
}

#[test]
fn garbage_syntax_emits_single_unknown() {
    let dir = case_dir("garbage");
    let path = dir.join("garbage.opb");
    std::fs::write(&path, "this is ;;; not opb at all\n").expect("write");
    let (stdout, stderr) = solve_output(&[path.to_str().unwrap()]);
    assert_eq!(s_lines(&stdout), vec!["s UNKNOWN"], "stdout: {stdout:?}");
    assert!(stderr.contains("failed to parse"), "stderr: {stderr:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn invalid_utf8_emits_single_unknown() {
    let dir = case_dir("badutf8");
    let path = dir.join("bad.opb");
    std::fs::write(&path, [0xff, 0xfe, 0x00, b'x']).expect("write");
    let (stdout, _) = solve_output(&[path.to_str().unwrap()]);
    assert_eq!(s_lines(&stdout), vec!["s UNKNOWN"], "stdout: {stdout:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn truncated_constraint_emits_single_unknown() {
    let dir = case_dir("truncated");
    let path = dir.join("truncated.opb");
    std::fs::write(&path, "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >=").expect("write");
    let (stdout, _) = solve_output(&[path.to_str().unwrap()]);
    assert_eq!(s_lines(&stdout), vec!["s UNKNOWN"], "stdout: {stdout:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn oversized_variable_count_emits_single_unsupported() {
    let dir = case_dir("huge");
    let path = dir.join("huge.opb");
    std::fs::write(
        &path,
        "* #variable= 400000000 #constraint= 1\n+1 x1 >= 1 ;\n",
    )
    .expect("write");
    let (stdout, _) = solve_output(&[path.to_str().unwrap()]);
    assert_eq!(
        s_lines(&stdout),
        vec!["s UNSUPPORTED"],
        "stdout: {stdout:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn wbo_negative_weight_with_zero_top_emits_single_unsupported() {
    // The soundness-ordering regression case from the top-cost work: a
    // parser-accepted negative weight must fail closed, never claim a verdict.
    let dir = case_dir("negwbo");
    let path = dir.join("neg.wbo");
    std::fs::write(&path, "soft: 0 ;\n+1 x1 >= 1 ;\n[-5] +1 x1 >= 1 ;\n").expect("write");
    let (stdout, _) = solve_output(&[path.to_str().unwrap()]);
    assert_eq!(
        s_lines(&stdout),
        vec!["s UNSUPPORTED"],
        "stdout: {stdout:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn empty_file_emits_exactly_one_s_line() {
    // Empty OPB = zero constraints over zero variables: trivially SATISFIABLE
    // is acceptable, as is a fail-closed UNKNOWN — but exactly one s line.
    let dir = case_dir("empty");
    let path = dir.join("empty.opb");
    std::fs::write(&path, "").expect("write");
    let (stdout, _) = solve_output(&[path.to_str().unwrap()]);
    let lines = s_lines(&stdout);
    assert_eq!(lines.len(), 1, "stdout: {stdout:?}");
    assert!(
        lines[0] == "s SATISFIABLE" || lines[0] == "s UNKNOWN",
        "got: {}",
        lines[0]
    );
    let _ = std::fs::remove_dir_all(&dir);
}
