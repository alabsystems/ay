// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The CDCL(T) kernel's production routes and the `--engine` measurement
//! switches (design the development design notes §10.1): QF_UF, QF_UFLRA
//! and QF_UFLIA check-sats are the kernel's in both postures,
//! `--engine=lane` keeps every family on its lane, and
//! `--engine=own:<families>` gives the kernel exactly the listed families.
//! `(get-info :all-statistics)` names the engine that answered
//! (`:engine.kernel`).

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

fn run(args: &[&str], input: &str) -> (String, String, Option<i32>) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .args(["-q", "-T:20", "-in"])
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
    let output = child.wait_with_output().expect("wait for ay -in");
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        output.status.code(),
    )
}

fn answers(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

const UF: &str = "(set-logic QF_UF)\n(declare-sort U 0)\n\
    (declare-fun a () U) (declare-fun b () U) (declare-fun f (U) U)\n\
    (assert (not (= (f a) (f b))))\n(check-sat)\n(get-value ((= a b)))\n\
    (get-info :all-statistics)\n";

const UFLIA: &str = "(set-logic QF_UFLIA)\n(declare-fun x () Int) (declare-fun f (Int) Int)\n\
    (assert (> (f x) (+ x 1)))\n(check-sat)\n(get-info :all-statistics)\n";

#[test]
#[timeout(60_000)]
fn qf_uf_is_the_kernels_in_both_postures() {
    for posture in [&["--z3-mode"][..], &[][..]] {
        let (stdout, stderr, _) = run(posture, UF);
        assert_eq!(answers(&stdout), ["sat"], "{stdout}\n{stderr}");
        assert!(stdout.contains("((= a b) false)"), "{stdout}");
        assert!(stdout.contains(":engine.kernel"), "{stdout}");
        assert!(!stdout.contains(":engine.fallback"), "{stdout}");
    }
}

#[test]
#[timeout(60_000)]
fn engine_lane_keeps_qf_uf_on_its_lane() {
    let (stdout, stderr, _) = run(&["--engine=lane"], UF);
    assert_eq!(answers(&stdout), ["sat"], "{stdout}\n{stderr}");
    assert!(!stdout.contains(":engine.kernel"), "{stdout}");
}

#[test]
#[timeout(60_000)]
fn engine_own_routes_exactly_the_listed_families() {
    let (stdout, stderr, _) = run(&[], UFLIA);
    assert_eq!(answers(&stdout), ["sat"], "{stdout}\n{stderr}");
    assert!(
        stdout.contains(":engine.kernel"),
        "production gives QF_UFLIA to the kernel: {stdout}"
    );

    let (stdout, stderr, _) = run(&["--engine=own:uf"], UFLIA);
    assert_eq!(answers(&stdout), ["sat"], "{stdout}\n{stderr}");
    assert!(
        !stdout.contains(":engine.kernel"),
        "QF_UFLIA is not listed: {stdout}"
    );

    let (stdout, stderr, _) = run(&["--engine=own:uflia"], UF);
    assert_eq!(answers(&stdout), ["sat"], "{stdout}\n{stderr}");
    assert!(
        !stdout.contains(":engine.kernel"),
        "QF_UF is not listed: {stdout}"
    );
}

#[test]
#[timeout(60_000)]
fn engine_own_refuses_an_unknown_family() {
    let (stdout, stderr, code) = run(&["--engine=own:uf,nope"], UF);
    assert_ne!(code, Some(0), "{stdout}\n{stderr}");
    assert!(stderr.contains("unknown kernel family `nope`"), "{stderr}");
}

/// `--engine=shadow` writes a row for every top-level check: a
/// `check-sat-assuming` row carries its assumptions (the kernel decides the
/// stack under them), and both commands' rows name the command.
#[test]
#[timeout(60_000)]
fn the_shadow_covers_check_sat_assuming() {
    let dir = tempfile::tempdir().expect("temp dir");
    let log = dir.path().join("shadow.jsonl");
    let script = "(set-logic QF_UF)\n(declare-sort U 0)\n\
        (declare-fun a () U) (declare-fun b () U) (declare-fun s () Bool) (declare-fun f (U) U)\n\
        (assert (=> s (= a b))) (assert (not (= (f a) (f b))))\n\
        (check-sat-assuming (s))\n(check-sat)\n";
    let flag = format!("--engine-shadow-log={}", log.display());
    let (stdout, stderr, _) = run(&["--engine=shadow", &flag], script);
    assert_eq!(answers(&stdout), ["unsat", "sat"], "{stdout}\n{stderr}");
    let rows: Vec<serde_json::Value> = std::fs::read_to_string(&log)
        .expect("shadow log")
        .lines()
        .map(|line| serde_json::from_str(line).expect("a JSON row"))
        .collect();
    assert_eq!(rows.len(), 2, "{rows:?}");
    assert_eq!(rows[0]["command"], "check-sat-assuming", "{rows:?}");
    assert_eq!(rows[0]["assumptions"], 1, "{rows:?}");
    assert_eq!(rows[0]["kernel"], "unsat", "{rows:?}");
    assert_eq!(rows[1]["command"], "check-sat", "{rows:?}");
    assert_eq!(rows[1]["kernel"], "sat", "{rows:?}");
    assert_eq!(rows[1]["kernel_model"], "satisfied", "{rows:?}");
}
