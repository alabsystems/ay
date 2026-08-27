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
fn test_proof_format_alethe_is_refused_for_dimacs() {
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
        Some(1),
        "DIMACS Alethe must fail closed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "refused DIMACS Alethe leaked UNSAT: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("Alethe proof output is unavailable for DIMACS input"),
        "missing retired-format diagnostic: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("original clause literals"),
        "diagnostic must explain the missing binding: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!proof_path.exists(), "refusal created a proof artifact");
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
fn test_decision_trace_preexisting_valid_trace_is_rejected_before_verdict() {
    const STALE_VALID_TRACE: &[u8] = b"AYDTRC1\0\x01\x08\x01";

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt = "(set-logic QF_UF)\n(assert false)\n(check-sat)\n";
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");
    let (trace_path, _trace_cleanup) = temp_path("aytrace");
    std::fs::write(&trace_path, STALE_VALID_TRACE).expect("plant stale valid trace");

    let output = Command::new(ay_path)
        .arg("--decision-trace")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "a pre-existing trace must fail reservation; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.lines().all(|line| !matches!(
            line.trim(),
            "sat" | "unsat" | "unknown" | "s SATISFIABLE" | "s UNSATISFIABLE" | "s UNKNOWN"
        )),
        "pre-existing trace bytes were accepted and a verdict leaked: {stdout}"
    );
    assert!(
        stderr.contains("cannot reserve --decision-trace output"),
        "missing fail-closed reservation diagnostic: {stderr}"
    );
    assert_eq!(
        std::fs::read(&trace_path).expect("read planted trace"),
        STALE_VALID_TRACE,
        "reservation failure must not overwrite the pre-existing trace"
    );
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_initialization_failure_precedes_verdict() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt = "(set-logic QF_UF)\n(assert false)\n(check-sat)\n";
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");
    let (missing_parent, _cleanup) = temp_path("missing-parent");
    let trace_path = missing_parent.join("decision.trace");

    let output = Command::new(ay_path)
        .arg("--decision-trace")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "trace initialization failure must be fatal; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.lines().all(|line| !matches!(
            line.trim(),
            "sat" | "unsat" | "unknown" | "s SATISFIABLE" | "s UNSATISFIABLE" | "s UNKNOWN"
        )),
        "trace initialization failed only after a verdict: {stdout}"
    );
    assert!(
        stderr.contains("cannot reserve --decision-trace output"),
        "missing initialization failure diagnostic: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_feature_report_exits_without_creating_artifact() {
    let (trace_path, _trace_cleanup) = temp_path("aytrace");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--decision-trace")
        .arg(&trace_path)
        .arg("--features")
        .output()
        .expect("spawn ay");

    assert!(
        output.status.success(),
        "feature report failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !trace_path.exists(),
        "a non-solver feature report must not reserve a decision trace"
    );
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_rejects_chc_before_verdict_or_artifact() {
    let horn = "(set-logic HORN)\n(declare-fun p () Bool)\n(assert p)\n(check-sat)\n";
    let (input_path, _input_cleanup) = write_temp(horn, "smt2");

    for forced in [false, true] {
        let (trace_path, _trace_cleanup) = temp_path("aytrace");
        let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
        command.arg("--decision-trace").arg(&trace_path);
        if forced {
            command.arg("--chc");
        }
        let output = command.arg(&input_path).output().expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(1),
            "CHC decision trace must be rejected; forced={forced}; stdout={stdout}; stderr={stderr}"
        );
        assert!(
            stdout.lines().all(|line| !matches!(
                line.trim(),
                "sat" | "unsat" | "unknown" | "s SATISFIABLE" | "s UNSATISFIABLE" | "s UNKNOWN"
            )),
            "CHC verdict leaked before trace rejection: {stdout}"
        );
        assert!(
            stderr.contains("--decision-trace is incompatible"),
            "missing CHC trace rejection: {stderr}"
        );
        assert!(
            !trace_path.exists(),
            "CHC trace rejection must precede artifact reservation"
        );
    }
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_rejects_parse_error_before_artifact() {
    let (input_path, _input_cleanup) = write_temp("(set-logic QF_UF\n(check-sat)\n", "smt2");
    let (trace_path, _trace_cleanup) = temp_path("aytrace");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--decision-trace")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("fully parseable single-query"),
        "missing parse preflight diagnostic: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!trace_path.exists());
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_rejects_malformed_dimacs_before_verdict_or_artifact() {
    let (input_path, _input_cleanup) = write_temp("p cnf 1 1\n2 0\n", "cnf");
    let (trace_path, _trace_cleanup) = temp_path("aytrace");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--decision-trace")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(output.status.code(), Some(1), "stderr={stderr}");
    assert!(
        stdout.lines().all(|line| !matches!(
            line.trim(),
            "sat" | "unsat" | "unknown" | "s SATISFIABLE" | "s UNSATISFIABLE" | "s UNKNOWN"
        )),
        "malformed DIMACS emitted a verdict before trace rejection: {stdout}"
    );
    assert!(
        stderr.contains("--decision-trace requires fully parseable DIMACS input"),
        "missing DIMACS preflight diagnostic: {stderr}"
    );
    assert!(!trace_path.exists());
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_rejects_parseable_dimacs_before_verdict_or_artifact() {
    let (input_path, _input_cleanup) = write_temp("p cnf 1 1\n1 0\n", "cnf");
    let (trace_path, _trace_cleanup) = temp_path("aytrace");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--decision-trace")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(output.status.code(), Some(1), "stderr={stderr}");
    assert!(
        stdout.lines().all(|line| !matches!(
            line.trim(),
            "sat" | "unsat" | "unknown" | "s SATISFIABLE" | "s UNSATISFIABLE" | "s UNKNOWN"
        )),
        "DIMACS verdict leaked before trace rejection: {stdout}"
    );
    assert!(
        stderr.contains("--decision-trace is currently unsupported for DIMACS input"),
        "missing DIMACS route rejection: {stderr}"
    );
    assert!(
        !trace_path.exists(),
        "DIMACS trace rejection must precede artifact reservation"
    );
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_rejects_multiple_queries_before_verdict_or_artifact() {
    let smt = "(set-logic QF_UF)\n(assert false)\n(check-sat)\n(check-sat)\n";
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");
    let (trace_path, _trace_cleanup) = temp_path("aytrace");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--decision-trace")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(output.status.code(), Some(1));
    assert!(
        stdout
            .lines()
            .all(|line| !matches!(line.trim(), "sat" | "unsat" | "unknown")),
        "a verdict was published before multi-query rejection: {stdout}"
    );
    assert!(
        stderr.contains("requires exactly one check-sat"),
        "missing multi-query diagnostic: {stderr}"
    );
    assert!(!trace_path.exists());
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_rejects_streaming_input_before_artifact() {
    for stream_flag in [None, Some("--stdin"), Some("--incremental")] {
        let (trace_path, _trace_cleanup) = temp_path("aytrace");
        let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
        command.arg("--decision-trace").arg(&trace_path);
        if let Some(flag) = stream_flag {
            command.arg(flag);
        }
        let output = command.output().expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert_eq!(output.status.code(), Some(1), "stderr={stderr}");
        assert!(
            stdout
                .lines()
                .all(|line| !matches!(line.trim(), "sat" | "unsat" | "unknown")),
            "a streaming verdict leaked before trace rejection: {stdout}"
        );
        assert!(
            stderr.contains("--decision-trace requires an input FILE"),
            "missing streaming-input rejection: {stderr}"
        );
        assert!(!trace_path.exists());
    }
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_disables_the_untraced_milp_fastpath() {
    const HEADER_BYTES: usize = 9;

    let smt = "(set-logic QF_LRA)\n\
               (declare-const c Real)\n\
               (assert (or (= c 0.0) (= c 1.0)))\n\
               (check-sat)\n";
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");
    let (trace_path, _trace_cleanup) = temp_path("aytrace");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["--no-proof", "--decision-trace"])
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        stdout.lines().any(|line| line.trim() == "sat"),
        "missing SAT verdict: {stdout}"
    );
    let trace = std::fs::read(&trace_path).expect("read decision trace");
    assert!(
        trace.len() > HEADER_BYTES,
        "MILP fast path left only a reserved trace header: {trace:?}"
    );
}

#[test]
#[timeout(60_000)]
fn test_decision_trace_rejects_untraced_parallel_dimacs_routes() {
    let (input_path, _input_cleanup) = write_temp("p cnf 1 1\n1 0\n", "cnf");

    for route_args in [["--parallel", "2"], ["--cube-and-conquer", "1"]] {
        let (trace_path, _trace_cleanup) = temp_path("aytrace");
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--decision-trace")
            .arg(&trace_path)
            .args(route_args)
            .arg(&input_path)
            .output()
            .expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert_eq!(output.status.code(), Some(1), "stderr={stderr}");
        assert!(
            stdout.lines().all(|line| !matches!(
                line.trim(),
                "sat" | "unsat" | "unknown" | "s SATISFIABLE" | "s UNSATISFIABLE" | "s UNKNOWN"
            )),
            "parallel DIMACS verdict leaked before trace rejection: {stdout}"
        );
        assert!(
            stderr.contains("--decision-trace is incompatible with --parallel/--cube-and-conquer"),
            "missing parallel-route rejection: {stderr}"
        );
        assert!(!trace_path.exists());
    }
}

#[test]
#[timeout(60_000)]
fn test_replay_flag_activates_production_replay() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt = "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n";
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");
    let (trace_path, _trace_cleanup) = temp_path("aytrace");

    let first = Command::new(ay_path)
        .arg(&input_path)
        .arg("--decision-trace")
        .arg(&trace_path)
        .output()
        .expect("spawn ay for trace recording");
    assert!(
        first.status.success(),
        "trace recording failed: {}",
        String::from_utf8_lossy(&first.stderr)
    );
    assert!(trace_path.exists(), "expected decision trace file");

    let replay = Command::new(ay_path)
        .arg("--replay")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay replay run");
    assert!(
        replay.status.success(),
        "replay failed: {}",
        String::from_utf8_lossy(&replay.stderr)
    );
    assert!(
        String::from_utf8_lossy(&replay.stdout)
            .lines()
            .any(|line| line.trim() == "sat"),
        "expected SAT replay result, got {}",
        String::from_utf8_lossy(&replay.stdout)
    );
}
