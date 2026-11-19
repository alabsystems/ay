// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay qbf solve`: QBF Gallery exit codes (10 true, 20 false, 0 unknown) for
//! QDIMACS and prenex QCIR input, and the `--timeout` option.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct DirGuard(PathBuf);

impl Drop for DirGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// ∃x ∀u. (x ∨ u)(x ∨ ¬u): true with x = true.
const TRUE_QDIMACS: &str = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n1 -2 0\n";
/// ∃x ∀u. (x ∨ u)(¬x ∨ ¬u): false, u always falsifies one clause.
const FALSE_QDIMACS: &str = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n-1 -2 0\n";
/// ∀u. (u): false by universal reduction, before any search.
const UNIVERSAL_UNIT: &str = "p cnf 1 1\na 1 0\n1 0\n";
/// ∀x ∃y. x xor y: true.
const TRUE_QCIR: &str = "#QCIR-G14\nforall(x)\nexists(y)\noutput(g)\ng = xor(x, y)\n";
/// ∃y ∀x. x xor y: false.
const FALSE_QCIR: &str = "#QCIR-G14\nexists(y)\nforall(x)\noutput(g)\ng = xor(x, y)\n";

fn scratch() -> (PathBuf, DirGuard) {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "ay_qbf_solve_cli_{}_{}",
        std::process::id(),
        ID.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    for (name, text) in [
        ("true.qdimacs", TRUE_QDIMACS),
        ("false.qdimacs", FALSE_QDIMACS),
        ("unit.qdimacs", UNIVERSAL_UNIT),
        ("true.qcir", TRUE_QCIR),
        ("false.qcir", FALSE_QCIR),
    ] {
        std::fs::write(dir.join(name), text).unwrap();
    }
    (dir.clone(), DirGuard(dir))
}

/// Run `ay qbf solve <args> <dir/file>`; return (exit code, stdout, stderr).
fn qbf(dir: &Path, file: &str, args: &[&str]) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["qbf", "solve"])
        .args(args)
        .arg(dir.join(file))
        .output()
        .expect("run ay");
    let code = output.status.code().expect("ay died on a signal");
    (
        code,
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn qbf_solve_qdimacs_keeps_gallery_exit_codes() {
    let (dir, _guard) = scratch();
    let (code, out, err) = qbf(&dir, "true.qdimacs", &[]);
    assert_eq!((code, out.trim()), (10, "s TRUE"), "stderr: {err}");
    let (code, out, err) = qbf(&dir, "false.qdimacs", &[]);
    assert_eq!((code, out.trim()), (20, "s FALSE"), "stderr: {err}");
}

#[test]
fn qbf_solve_reads_qcir_by_its_header() {
    let (dir, _guard) = scratch();
    let (code, out, err) = qbf(&dir, "false.qcir", &[]);
    assert_eq!((code, out.trim()), (20, "s FALSE"), "stderr: {err}");
    let (code, out, err) = qbf(&dir, "true.qcir", &[]);
    assert_eq!((code, out.trim()), (10, "s TRUE"), "stderr: {err}");
}

#[test]
fn qbf_solve_refuses_a_timeout_that_is_not_a_positive_duration() {
    let (dir, _guard) = scratch();
    // 1e-12 s rounds to a zero Duration; "-1" also exercises clap's handling
    // of a leading dash in an option value.
    for bad in ["0", "NaN", "inf", "-1", "1e-12", "abc"] {
        let flag = format!("--timeout={bad}");
        let (code, out, err) = qbf(&dir, "true.qdimacs", &[&flag]);
        assert_eq!(code, 2, "--timeout {bad} must be a usage error: {out}{err}");
        assert!(out.is_empty(), "--timeout {bad} printed a verdict: {out}");
        assert!(err.contains("timeout") || err.contains("seconds"), "{err}");
    }
    let (code, out, err) = qbf(&dir, "true.qdimacs", &["--timeout", "0.5"]);
    assert_eq!((code, out.trim()), (10, "s TRUE"), "stderr: {err}");
    let (code, out, err) = qbf(&dir, "false.qcir", &["--timeout", "30"]);
    assert_eq!((code, out.trim()), (20, "s FALSE"), "stderr: {err}");
}

#[test]
fn qbf_solve_observes_a_timeout_that_passes_before_the_search() {
    let (dir, _guard) = scratch();
    // Without a limit, universal reduction decides the formula at once.
    let (code, out, err) = qbf(&dir, "unit.qdimacs", &[]);
    assert_eq!((code, out.trim()), (20, "s FALSE"), "stderr: {err}");
    // One nanosecond has passed by the time the file is read: ay must stop
    // there instead of going on to parse, prepare and answer.
    let (code, out, err) = qbf(&dir, "unit.qdimacs", &["--timeout", "1e-9"]);
    assert_eq!((code, out.trim()), (0, "s UNKNOWN"), "stderr: {err}");
}
