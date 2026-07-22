// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FP signed-zero regressions that previously surfaced as wrong answers or
//! spurious `unknown` at the CLI boundary.

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp(contents: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_fp_signed_zero_regressions_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp smt2");
    (path.clone(), CleanupGuard(path))
}

#[test]
#[timeout(30_000)]
fn fp_min_signed_zero_negated_predicate_is_sat_on_cli() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _cleanup) = write_temp(
        "(set-logic QF_FP)\n\
         (assert (not (fp.isNegative (fp.min (_ +zero 5 11) (_ -zero 5 11)))))\n\
         (check-sat)\n\
         (exit)\n",
    );

    let output = Command::new(ay_path)
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first_line = stdout.trim().lines().next().unwrap_or("").to_string();

    assert_eq!(
        output.status.code(),
        Some(0),
        "Expected CLI signed-zero regression to exit cleanly.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        first_line, "sat",
        "Signed-zero min regression should stay satisfiable, not degrade to unknown.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stdout.contains("reason-unknown"),
        "No reason-unknown should be printed for a decidable signed-zero regression.\nstdout:\n{stdout}"
    );
    assert!(
        !stderr.contains("reason-unknown"),
        "No reason-unknown should leak to stderr for a decidable signed-zero regression.\nstderr:\n{stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn fp_max_signed_zero_negated_predicate_is_sat_on_cli() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _cleanup) = write_temp(
        "(set-logic QF_FP)\n\
         (assert (not (fp.isPositive (fp.max (_ -zero 5 11) (_ +zero 5 11)))))\n\
         (check-sat)\n\
         (exit)\n",
    );

    let output = Command::new(ay_path)
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first_line = stdout.trim().lines().next().unwrap_or("").to_string();

    assert_eq!(
        output.status.code(),
        Some(0),
        "Expected CLI signed-zero max regression to exit cleanly.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        first_line, "sat",
        "Signed-zero max regression should stay satisfiable, not degrade to unknown.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stdout.contains("reason-unknown"),
        "No reason-unknown should be printed for a decidable signed-zero regression.\nstdout:\n{stdout}"
    );
    assert!(
        !stderr.contains("reason-unknown"),
        "No reason-unknown should leak to stderr for a decidable signed-zero regression.\nstderr:\n{stderr}"
    );
}
