// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::io::Write;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_FILE_SEQ: AtomicU64 = AtomicU64::new(0);

fn run_ay_on_input(test_input: &str) -> std::process::Output {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp_path = {
        let pid = std::process::id();
        let temp_dir = std::env::temp_dir();
        let mut reserved = None;
        for _ in 0..32 {
            let seq = TEMP_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
            let candidate = temp_dir.join(format!("ay_arrays_row2_regression_{pid}_{seq}.smt2"));
            match std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&candidate)
            {
                Ok(mut file) => {
                    file.write_all(test_input.as_bytes())
                        .expect("write row2 regression input");
                    reserved = Some(candidate);
                    break;
                }
                Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(err) => panic!("create row2 regression temp file: {err}"),
            }
        }
        reserved.expect("reserve unique row2 regression temp file")
    };
    struct CleanupGuard(std::path::PathBuf);
    impl Drop for CleanupGuard {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let _cleanup = CleanupGuard(temp_path.clone());

    Command::new(ay_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to run ay")
}

#[test]
#[timeout(30_000)]
fn test_arrays_row2_propagation_regression() {
    let test_input = r#"(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (not (= i j)))  ; i != j

(declare-const v Int)
(declare-const A_post (Array Int Int))
(assert (= A_post (store A i v)))

(declare-const before Int)
(declare-const after Int)
(assert (= before (select A j)))
(assert (= after (select A_post j)))

; ROW2 should derive: before = after
(assert (not (= before after)))
(check-sat)
"#;

    let output = run_ay_on_input(test_input);

    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "AY exited with {:?}",
        output.status
    );
    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "unsat", "Expected 'unsat', got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn test_arrays_root_faithful_store_target_with_fresh_row2_witness_is_not_unsat_8785() {
    let test_input = r#"(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const rhs (Array Int Int))
(declare-const lhs (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const k Int)
(declare-const vk Int)
(declare-const p_root Bool)

; Keep (= a rhs) syntactically present so the disjunctive store-target checker
; can justify the root-faithful branch instead of silently skipping it.
(assert (= p_root (= a rhs)))
(assert (= rhs (store a i (select a i))))
(assert (= rhs (store a j (select a j))))
(assert (= lhs (store rhs k vk)))
(assert (distinct i j))
(assert (distinct k i))
(assert (distinct k j))
(assert (not (= (select lhs k) (select rhs k))))
(check-sat)
"#;

    let output = run_ay_on_input(test_input);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "AY exited with {:?}",
        output.status
    );
    let first_line = stdout.lines().next().unwrap_or("");
    assert_ne!(
        first_line, "unsat",
        "Soundness regression (#8785): root-faithful same-target stores plus a fresh ROW2 witness index must stay SAT/unknown, not UNSAT. Got: {stdout}"
    );
}
