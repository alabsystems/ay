// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #9842: supported FP `check-sat-assuming` queries should route through the
//! regular FP solver instead of hardwiring `unknown`.

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
        "ay_fp_check_sat_assuming_9842_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp smt2");
    (path.clone(), CleanupGuard(path))
}

#[test]
#[timeout(30_000)]
fn fp_check_sat_assuming_supported_predicate_is_sat_on_cli() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _cleanup) = write_temp(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (check-sat-assuming ((fp.isNaN x)))\n\
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
        "Expected FP check-sat-assuming CLI regression to exit cleanly.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        first_line, "sat",
        "Supported FP check-sat-assuming should be satisfiable.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stdout.contains("reason-unknown"),
        "Supported FP check-sat-assuming should not print reason-unknown.\nstdout:\n{stdout}"
    );
    assert!(
        !stderr.contains("reason-unknown"),
        "Supported FP check-sat-assuming should not leak reason-unknown to stderr.\nstderr:\n{stderr}"
    );
}
