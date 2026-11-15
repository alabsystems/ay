// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI coverage for two 0.1.0 launch-polish additions:
//!   * CODE 11 — a bare `-` FILE on `solve` means "read from stdin".
//!   * CODE 13 — `-q`/`--quiet` suppresses AY's stderr provenance commentary
//!     without changing stdout, proof emission, or exit codes.

use std::path::PathBuf;
use std::process::Command;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

/// Write `contents` as `input.cnf` in a fresh directory of its own.
///
/// A default solve of `X.cnf` synthesizes `X.cnf.drat` and settles its
/// `X.cnf.drat.ay-status` marker even on SAT, and a later run never overwrites
/// either (449fd06aa): it warns and publishes no proof. Two runs compared
/// byte-for-byte must therefore not share an input path, or the second one's
/// stderr carries the first one's leftovers. The directory also collects every
/// sidecar, so dropping it leaves nothing behind.
fn write_isolated_cnf(contents: &str) -> (tempfile::TempDir, PathBuf) {
    let dir = tempfile::tempdir().expect("create isolated CNF directory");
    let path = dir.path().join("input.cnf");
    std::fs::write(&path, contents).expect("write isolated CNF");
    (dir, path)
}

// Trivially satisfiable one-variable CNF.
const SAT_CNF: &str = "p cnf 1 1\n1 0\n";

#[test]
fn dash_file_reads_formula_from_stdin() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("solve")
        .arg("-")
        .output_timeout_with_stdin(SAT_CNF.as_bytes(), DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay solve -");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // The old behavior treated `-` as a positional file and failed to open it.
    assert!(
        !stderr.contains("Error reading file '-'"),
        "`-` must be stdin, not a file named '-': stderr={stderr}"
    );
    assert!(
        stdout.contains("SATISFIABLE"),
        "stdin CNF should solve to SAT: stdout={stdout} stderr={stderr}"
    );
}

#[test]
fn quiet_suppresses_commentary_but_not_stdout_or_exit_code() {
    // Same formula, separate paths: each run starts from a clean default-proof
    // namespace, so the two stderrs differ only by what `-q` suppresses.
    let (_plain_dir, plain_cnf) = write_isolated_cnf(SAT_CNF);
    let (_quiet_dir, quiet_cnf) = write_isolated_cnf(SAT_CNF);
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let plain = Command::new(ay_path)
        .arg("solve")
        .arg(&plain_cnf)
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay solve FILE");

    let quiet = Command::new(ay_path)
        .arg("solve")
        .arg("-q")
        .arg(&quiet_cnf)
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay solve -q FILE");

    // stdout is the machine-parsed answer: it must be byte-identical.
    assert_eq!(
        plain.stdout,
        quiet.stdout,
        "-q must not change stdout: plain={:?} quiet={:?}",
        String::from_utf8_lossy(&plain.stdout),
        String::from_utf8_lossy(&quiet.stdout)
    );

    // Exit codes must match.
    assert_eq!(
        plain.status.code(),
        quiet.status.code(),
        "-q must not change the exit code"
    );

    let plain_err = String::from_utf8_lossy(&plain.stderr);
    let quiet_err = String::from_utf8_lossy(&quiet.stderr);

    // The default run prints the `c sat.policy` provenance preamble; `-q` removes it.
    assert!(
        plain_err.contains("c sat.policy"),
        "default solve should print the sat.policy preamble: stderr={plain_err}"
    );
    assert!(
        !quiet_err.contains("c sat.policy"),
        "-q must suppress the sat.policy preamble: stderr={quiet_err}"
    );
    assert!(
        !quiet_err.contains("c ay.session"),
        "-q must suppress session provenance markers: stderr={quiet_err}"
    );
    // Quiet stderr should be strictly smaller than the chatty default.
    assert!(
        quiet_err.len() <= plain_err.len(),
        "-q stderr should not exceed default stderr: quiet={quiet_err:?} plain={plain_err:?}"
    );
}
