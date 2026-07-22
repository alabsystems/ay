// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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

fn temp_path(extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_cli_observability_{}_{}.{}",
        std::process::id(),
        file_id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn write_temp(contents: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    let (path, cleanup) = temp_path(extension);
    std::fs::write(&path, contents).expect("write temp input");
    (path, cleanup)
}

#[test]
#[timeout(60_000)]
fn test_proof_flag_writes_alethe_for_unsat_smt() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
"#;
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");
    let (proof_path, _proof_cleanup) = temp_path("alethe");

    let output = Command::new(ay_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("unsat"),
        "expected unsat output, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof = std::fs::read_to_string(&proof_path).expect("proof file");
    assert!(!proof.is_empty(), "expected non-empty proof file");
    assert!(proof.contains("(assume "), "expected assume steps in proof");
    assert!(proof.contains("(step "), "expected step entries in proof");
}

#[test]
#[timeout(60_000)]
fn test_proof_flag_writes_drat_for_unsat_dimacs() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp(cnf, "cnf");
    let (proof_path, _proof_cleanup) = temp_path("drat");

    let output = Command::new(ay_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof = std::fs::read_to_string(&proof_path).expect("proof file");
    assert!(!proof.trim().is_empty(), "expected non-empty DRAT output");
}

#[test]
#[timeout(60_000)]
fn test_proof_flag_writes_lrat_for_unsat_dimacs() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp(cnf, "cnf");
    let (proof_path, _proof_cleanup) = temp_path("lrat");

    let output = Command::new(ay_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof = std::fs::read_to_string(&proof_path).expect("proof file");
    assert!(!proof.trim().is_empty(), "expected non-empty LRAT output");
}

#[test]
#[timeout(60_000)]
fn test_proof_format_alethe_writes_alethe_for_unsat_dimacs() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp(cnf, "cnf");
    let (proof_path, _proof_cleanup) = temp_path("proof");

    let output = Command::new(ay_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("alethe")
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof = std::fs::read_to_string(&proof_path).expect("proof file");
    assert!(!proof.is_empty(), "expected non-empty Alethe proof file");
    assert!(
        proof.contains("(assume "),
        "expected assume steps in Alethe proof"
    );
    assert!(
        proof.contains("(step "),
        "expected step entries in Alethe proof"
    );
}

#[test]
#[timeout(60_000)]
fn test_stats_flag_includes_formula_statistics_block() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"#;
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");

    let output = Command::new(ay_path)
        .arg("--stats")
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("(:statistics"),
        "expected solver stats block, got {stderr}"
    );
    assert!(
        stderr.contains("(:formula-statistics"),
        "expected formula stats block, got {stderr}"
    );
    assert!(
        stderr.contains(":terms"),
        "expected term-count key in formula stats, got {stderr}"
    );
}

// Part of EXPLAINABILITY_AUDIT.md Finding B: `--decision-trace <file>`
// previously produced no file on SMT-LIB preprocessing-only UNSAT paths,
// breaking `--replay` round-trip. A minimal valid trace (MAGIC + VERSION +
// Result::Unsat terminal event) must always be emitted so downstream
// replay tooling can at least observe the final verdict.
#[test]
#[timeout(60_000)]
fn test_decision_trace_smt_preprocessing_only_unsat_emits_terminal_event() {
    // Binary trace format constants (kept private by `ay_sat::decision_trace`).
    const MAGIC: &[u8; 8] = b"AYDTRC1\0";
    const VERSION: u8 = 1;
    const TAG_RESULT: u8 = 8;
    const OUTCOME_UNSAT: u8 = 1;

    let ay_path = env!("CARGO_BIN_EXE_ay");
    // Trivial QF_UF UNSAT that historically short-circuited at preprocessing
    // without producing a decision trace.
    let smt = "(set-logic QF_UF)\n\
               (declare-const p Bool)\n\
               (assert p)\n\
               (assert (not p))\n\
               (check-sat)\n";
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");
    let (trace_path, _trace_cleanup) = temp_path("aytrace");

    let output = Command::new(ay_path)
        .arg("--decision-trace")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("unsat"),
        "expected unsat verdict, got: {}",
        String::from_utf8_lossy(&output.stdout)
    );

    assert!(
        trace_path.exists(),
        "expected --decision-trace file at {}",
        trace_path.display()
    );
    let bytes = std::fs::read(&trace_path).expect("read decision trace");
    assert!(
        !bytes.is_empty(),
        "decision trace file must be non-empty (MAGIC+VERSION+Result event)"
    );
    assert!(
        bytes.len() >= MAGIC.len() + 1 + 2,
        "decision trace too short: {} bytes (need >= MAGIC+VERSION+Result event)",
        bytes.len()
    );
    assert_eq!(
        &bytes[..MAGIC.len()],
        MAGIC,
        "decision trace MAGIC mismatch"
    );
    assert_eq!(
        bytes[MAGIC.len()],
        VERSION,
        "decision trace VERSION mismatch"
    );

    // Terminal event must be Result::Unsat so --replay stops with the correct
    // verdict. The last two bytes are (TAG_RESULT, outcome_byte).
    let tail = &bytes[bytes.len() - 2..];
    assert_eq!(
        tail[0], TAG_RESULT,
        "expected terminal Result tag 0x{TAG_RESULT:02x}, trace tail: {tail:?}"
    );
    assert_eq!(
        tail[1], OUTCOME_UNSAT,
        "expected terminal outcome Unsat (0x{OUTCOME_UNSAT:02x}), got 0x{:02x}",
        tail[1]
    );

    // Round-trip: the emitted trace must be accepted by --replay without
    // divergence and yield the same UNSAT verdict.
    let replay = Command::new(ay_path)
        .arg("--replay")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay replay");
    assert!(
        replay.status.success(),
        "ay --replay failed: {}",
        String::from_utf8_lossy(&replay.stderr)
    );
    assert!(
        String::from_utf8_lossy(&replay.stdout).contains("unsat"),
        "expected unsat verdict on replay, got: {}",
        String::from_utf8_lossy(&replay.stdout)
    );
}

#[test]
#[timeout(60_000)]
fn test_replay_flag_activates_production_replay() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 3\n1 0\n-1 2 0\n-2 0\n";
    let (input_path, _input_cleanup) = write_temp(cnf, "cnf");
    let (trace_path, _trace_cleanup) = temp_path("aytrace");

    let first = Command::new(ay_path)
        .arg(&input_path)
        .arg("--decision-trace")
        .arg(&trace_path)
        .output()
        .expect("spawn ay for trace recording");
    assert_eq!(
        first.status.code(),
        Some(20),
        "trace recording: expected UNSAT exit code 20: {}",
        String::from_utf8_lossy(&first.stderr)
    );
    assert!(trace_path.exists(), "expected decision trace file");

    let replay = Command::new(ay_path)
        .arg("--replay")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay replay run");
    assert_eq!(
        replay.status.code(),
        Some(20),
        "replay: expected UNSAT exit code 20: {}",
        String::from_utf8_lossy(&replay.stderr)
    );
    assert!(
        String::from_utf8_lossy(&replay.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT replay result, got {}",
        String::from_utf8_lossy(&replay.stdout)
    );
}
