// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI coverage for two 0.1.0 launch-polish additions:
//!   * CODE 11 — a bare `-` FILE on `solve` means "read from stdin".
//!   * CODE 13 — `-q`/`--quiet` suppresses AY's stderr provenance commentary
//!     without changing stdout, proof emission, or exit codes.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_cnf(contents: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_quiet_dash_{}_{}.cnf",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp CNF");
    (path.clone(), CleanupGuard(path))
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
    let (cnf_path, _guard) = write_temp_cnf(SAT_CNF);
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let plain = Command::new(ay_path)
        .arg("solve")
        .arg(&cnf_path)
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay solve FILE");

    let quiet = Command::new(ay_path)
        .arg("solve")
        .arg("-q")
        .arg(&cnf_path)
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
