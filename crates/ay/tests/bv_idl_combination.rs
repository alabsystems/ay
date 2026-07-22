// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_BV x QF_IDL boundary check for #8721 / Z3 #8940.
//!
//! AY has frontend support for the legacy `bv2nat` BV-to-Int boundary and
//! auto-detects such formulas as internal `_BV_LIA`. The conservative bridge
//! derives unsigned BV comparison bounds into the Int side strongly enough for
//! this IDL contradiction.

use ntest::timeout;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, ExitStatus, Stdio};

struct AYOutput {
    status: ExitStatus,
    stdout: String,
    stderr: String,
}

fn run_ay_stdin(input: &str) -> AYOutput {
    let mut child = Command::new(ay_binary())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");

    child
        .stdin
        .as_mut()
        .expect("stdin is piped")
        .write_all(input.as_bytes())
        .expect("write SMT-LIB to ay");

    let output = child.wait_with_output().expect("wait for ay");
    AYOutput {
        status: output.status,
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    }
}

fn ay_binary() -> PathBuf {
    let cargo_bin = PathBuf::from(env!("CARGO_BIN_EXE_ay"));
    if cargo_bin.is_file() {
        return cargo_bin;
    }

    let current = std::env::current_exe().expect("resolve current test executable");
    let deps_dir = current.parent().expect("test executable has parent dir");
    let profile_dir = deps_dir
        .parent()
        .expect("test executable is under target profile deps dir");
    let candidate = profile_dir.join(format!("ay{}", std::env::consts::EXE_SUFFIX));
    assert!(
        candidate.is_file(),
        "ay CLI integration test requires a built ay binary at {} or {}",
        cargo_bin.display(),
        candidate.display()
    );
    candidate
}

fn first_check_sat_result(stdout: &str) -> Option<&str> {
    stdout
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

#[test]
#[timeout(30_000)]
fn qf_bv_idl_bv2nat_boundary_is_unsat() {
    let input = r#"
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(declare-const b (_ BitVec 4))
(assert (= x (bv2nat b)))
(assert (<= (- x y) 0))
(assert (<= (- y x) 0))
(assert (= y 10))
(assert (bvult b #x8))
(check-sat)
(get-info :reason-unknown)
"#;

    let output = run_ay_stdin(input);
    let result = first_check_sat_result(&output.stdout);

    assert!(
        output.status.success(),
        "ay should exit cleanly for BV/IDL boundary input.\nstdout:\n{}\nstderr:\n{}",
        output.stdout,
        output.stderr
    );

    assert_eq!(
        result,
        Some("unsat"),
        "BV/IDL bridge formula should be unsat: IDL pins x = y = 10, \
         x = bv2nat(b), and bvult(b, #x8) requires bv2nat(b) < 8.\nstdout:\n{}\nstderr:\n{}",
        output.stdout,
        output.stderr
    );
}
