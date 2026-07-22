// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--self-check` BV DRAT self-certification.
//!
//! Under `--self-check` a pure-QF_BV UNSAT is emitted only when AY's OWN native
//! DRAT checker verifies the single-invocation bit-blast refutation for that
//! exact solve. Before this lane existed the same query degraded to
//! `unknown (:reason-unknown incomplete)` because the eager bit-blast has no
//! Alethe proof to self-certify. The direction is sound-only: a SAT or
//! non-verifiable result must never become `unsat`, and default (no
//! `--self-check`) output must be unchanged.

use ntest::timeout;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "ay-selfcert-bvdrat-test-{}-{n}-{name}",
        std::process::id()
    ));
    let mut file = std::fs::File::create(&path).expect("create temp smt2");
    file.write_all(contents.as_bytes())
        .expect("write temp smt2");
    path
}

fn run(args: &[&str]) -> Output {
    Command::new(ay_binary())
        .args(args)
        .output()
        .expect("spawn ay")
}

fn stdout_stderr(output: &Output) -> (String, String) {
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

const BV_UNSAT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x (_ bv5 8)))
(assert (= x (_ bv7 8)))
(check-sat)
(exit)
"#;

const BV_SAT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x (_ bv1 8)) (_ bv7 8)))
(check-sat)
(exit)
"#;

/// A pure-QF_BV UNSAT that has no Alethe self-cert proof (its refutation is the
/// eager bit-blast) is emitted as `unsat` under `--self-check` — self-certified
/// by AY's native DRAT checker. The `c` diagnostic names the path.
#[test]
#[timeout(120_000)]
fn bv_unsat_self_certified_via_native_drat() {
    let input = write_temp("unsat.smt2", BV_UNSAT);
    let output = run(&["--self-check", input.to_str().unwrap()]);
    let (stdout, stderr) = stdout_stderr(&output);

    // stdout carries exactly the verdict line `unsat` (never `unknown`).
    assert!(
        stdout.lines().any(|l| l.trim() == "unsat"),
        "expected `unsat` on stdout; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !stdout.lines().any(|l| l.trim() == "unknown"),
        "must not degrade to `unknown`; stdout={stdout}; stderr={stderr}"
    );
    // The self-cert diagnostic goes to the diagnostic (stderr) channel, so
    // stdout stays a clean SMT-LIB transcript.
    assert!(
        stderr.contains("BV unsat self-certified via native DRAT check"),
        "expected native DRAT self-cert diagnostic; stderr={stderr}"
    );

    let _ = std::fs::remove_file(&input);
}

/// A pure-QF_BV SAT is unaffected: it stays `sat` and never triggers the DRAT
/// self-cert lane (the DRAT scratch is removed on SAT).
#[test]
#[timeout(120_000)]
fn bv_sat_unaffected_under_self_check() {
    let input = write_temp("sat.smt2", BV_SAT);
    let output = run(&["--self-check", input.to_str().unwrap()]);
    let (stdout, stderr) = stdout_stderr(&output);

    assert!(
        stdout.lines().any(|l| l.trim() == "sat"),
        "expected `sat`; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !stderr.contains("BV unsat self-certified"),
        "SAT must not run the UNSAT DRAT self-cert; stderr={stderr}"
    );

    let _ = std::fs::remove_file(&input);
}

/// Default mode (no `--self-check`) is byte-unchanged: the same UNSAT verdict,
/// and no self-cert diagnostic.
#[test]
#[timeout(120_000)]
fn default_mode_verdict_unchanged() {
    let input = write_temp("default.smt2", BV_UNSAT);
    let output = run(&[input.to_str().unwrap()]);
    let (stdout, stderr) = stdout_stderr(&output);

    assert!(
        stdout.lines().any(|l| l.trim() == "unsat"),
        "default mode must still report `unsat`; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !stderr.contains("BV unsat self-certified"),
        "default mode must not run the self-cert lane; stderr={stderr}"
    );

    let _ = std::fs::remove_file(&input);
}
