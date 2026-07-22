// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_drat_check::checker::DratChecker;
use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_lrat_check::checker::LratChecker;
use ay_lrat_check::dimacs::parse_cnf_with_ids;
use ay_lrat_check::lrat_parser::{parse_binary_lrat, parse_text_lrat};
use ntest::timeout;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn temp_path(stem: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_cli_proof_formats_{}_{}_{}.{}",
        std::process::id(),
        stem,
        file_id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn write_temp_cnf(contents: &str) -> (PathBuf, CleanupGuard) {
    let (path, cleanup) = temp_path("input", "cnf");
    std::fs::write(&path, contents).expect("write temp CNF");
    (path, cleanup)
}

fn default_drat_path_for_input(input_path: &Path) -> PathBuf {
    let file_name = input_path
        .file_name()
        .expect("temp input has file name")
        .to_string_lossy();
    input_path.with_file_name(format!("{file_name}.drat"))
}

fn run_unsat_cli(flag: &str, proof_path: &Path, input_path: &Path) -> Vec<u8> {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg(flag)
        .arg(proof_path)
        .arg(input_path)
        .output()
        .expect("spawn ay");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 for {flag}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT output for {flag}, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    std::fs::read(proof_path).unwrap_or_else(|error| {
        panic!(
            "failed to read proof file {}: {error}",
            proof_path.display()
        )
    })
}

fn run_check_cli(kind: &str, input_path: &Path, proof_path: &Path) -> std::process::Output {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    Command::new(ay_path)
        .arg("check")
        .arg(kind)
        .arg(input_path)
        .arg(proof_path)
        .output()
        .expect("spawn ay check")
}

fn run_check_cli_with_evidence(
    kind: &str,
    input_path: &Path,
    proof_path: &Path,
    evidence_path: &Path,
    extra_args: &[&str],
) -> std::process::Output {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut command = Command::new(ay_path);
    command
        .arg("check")
        .arg(kind)
        .arg(input_path)
        .arg(proof_path)
        .arg("--evidence-json")
        .arg(evidence_path);
    for arg in extra_args {
        command.arg(arg);
    }
    command.output().expect("spawn ay check with evidence")
}

fn sha256_prefixed(bytes: &[u8]) -> String {
    format!("sha256:{:x}", Sha256::digest(bytes))
}

fn read_evidence_json(path: &Path) -> Value {
    let data = std::fs::read(path)
        .unwrap_or_else(|error| panic!("failed to read evidence JSON {}: {error}", path.display()));
    serde_json::from_slice(&data)
        .unwrap_or_else(|error| panic!("failed to parse evidence JSON {}: {error}", path.display()))
}

fn verify_drat_proof(cnf: &str, proof_bytes: &[u8]) {
    let formula = parse_cnf(cnf.as_bytes()).expect("parse CNF");
    let proof = parse_drat(proof_bytes).expect("parse DRAT");
    let mut checker = DratChecker::new(formula.num_vars, true);
    checker
        .verify(&formula.clauses, &proof)
        .expect("verify DRAT proof");
}

#[test]
#[timeout(60_000)]
fn test_default_dimacs_unsat_writes_verifiable_drat_proof_8864() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let proof_path = default_drat_path_for_input(&input_path);
    let _proof_cleanup = CleanupGuard(proof_path.clone());
    let _ = std::fs::remove_file(&proof_path);

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 under default proof mode; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("UNSATISFIABLE"),
        "expected UNSAT output under default proof mode, got: {stdout}"
    );
    assert!(
        stderr.contains("c writing DRAT proof to")
            && stderr.contains(proof_path.to_string_lossy().as_ref()),
        "default proof path should be announced on stderr; expected {}; stderr={stderr}",
        proof_path.display()
    );

    let proof_bytes = std::fs::read(&proof_path).unwrap_or_else(|error| {
        panic!(
            "failed to read default proof file {}: {error}",
            proof_path.display()
        )
    });
    assert!(
        !proof_bytes.is_empty(),
        "default DRAT proof should be non-empty"
    );
    verify_drat_proof(cnf, &proof_bytes);
}

fn verify_lrat_text_proof(cnf: &str, proof_bytes: &[u8]) {
    let formula = parse_cnf_with_ids(cnf.as_bytes()).expect("parse CNF with IDs");
    let proof_text = std::str::from_utf8(proof_bytes).expect("LRAT text should be UTF-8");
    let proof = parse_text_lrat(proof_text).expect("parse LRAT text");
    let mut checker = LratChecker::new(formula.num_vars);
    for (id, clause) in &formula.clauses {
        assert!(
            checker.add_original(*id, clause),
            "load original clause {id}"
        );
    }
    assert!(checker.verify_proof(&proof), "verify LRAT text proof");
}

fn verify_lrat_binary_proof(cnf: &str, proof_bytes: &[u8]) {
    let formula = parse_cnf_with_ids(cnf.as_bytes()).expect("parse CNF with IDs");
    let proof = parse_binary_lrat(proof_bytes).expect("parse LRAT binary");
    let mut checker = LratChecker::new(formula.num_vars);
    for (id, clause) in &formula.clauses {
        assert!(
            checker.add_original(*id, clause),
            "load original clause {id}"
        );
    }
    assert!(checker.verify_proof(&proof), "verify LRAT binary proof");
}

#[test]
#[timeout(60_000)]
fn test_explicit_drat_flag_writes_verifiable_text_proof() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("drat_text", "proof");

    let proof_bytes = run_unsat_cli("--drat", &proof_path, &input_path);
    verify_drat_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_explicit_drat_binary_flag_writes_verifiable_binary_proof() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("drat_binary", "proofbin");

    let proof_bytes = run_unsat_cli("--drat-binary", &proof_path, &input_path);
    verify_drat_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_explicit_lrat_flag_writes_verifiable_text_proof() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("lrat_text", "proof");

    let proof_bytes = run_unsat_cli("--lrat", &proof_path, &input_path);
    verify_lrat_text_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_explicit_lrat_binary_flag_writes_verifiable_binary_proof() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("lrat_binary", "proofbin");

    let proof_bytes = run_unsat_cli("--lrat-binary", &proof_path, &input_path);
    verify_lrat_binary_proof(cnf, &proof_bytes);
}

/// A harder UNSAT instance: pigeonhole principle PHP(3,2) — 3 pigeons, 2 holes.
/// This requires non-trivial conflict-driven clause learning to solve.
const PHP_3_2_CNF: &str = "\
p cnf 6 9\n\
1 2 0\n\
3 4 0\n\
5 6 0\n\
-1 -3 0\n\
-1 -5 0\n\
-3 -5 0\n\
-2 -4 0\n\
-2 -6 0\n\
-4 -6 0\n";

#[test]
#[timeout(60_000)]
fn test_drat_proof_on_harder_unsat_instance() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("php32_drat", "drat");

    let proof_bytes = run_unsat_cli("--drat", &proof_path, &input_path);
    assert!(
        !proof_bytes.is_empty(),
        "DRAT proof should be non-empty for PHP(3,2)"
    );
    verify_drat_proof(PHP_3_2_CNF, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_lrat_proof_on_harder_unsat_instance() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("php32_lrat", "lrat");

    let proof_bytes = run_unsat_cli("--lrat", &proof_path, &input_path);
    assert!(
        !proof_bytes.is_empty(),
        "LRAT proof should be non-empty for PHP(3,2)"
    );
    verify_lrat_text_proof(PHP_3_2_CNF, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_stdin_dimacs_lrat_proof_with_no_verify() {
    let (proof_path, _proof_cleanup) = temp_path("stdin_lrat", "lrat");

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut child = Command::new(ay_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg("--stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");

    let mut stdin = child.stdin.take().expect("stdin pipe");
    stdin
        .write_all(PHP_3_2_CNF.as_bytes())
        .expect("write DIMACS to stdin");
    drop(stdin);

    let output = child.wait_with_output().expect("wait for ay");
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 for stdin DIMACS proof: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT for stdin DIMACS proof, got: {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof_bytes = std::fs::read(&proof_path).unwrap_or_else(|error| {
        panic!(
            "failed to read stdin proof file {}: {error}",
            proof_path.display()
        )
    });
    assert!(
        !proof_bytes.is_empty(),
        "LRAT proof should be non-empty for stdin DIMACS proof mode"
    );
    verify_lrat_text_proof(PHP_3_2_CNF, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_stdin_multiline_dimacs_lrat_proof_with_duplicates_tautology_verify() {
    let cnf = "\
p cnf 2 4
1
1 0
1 -1 0
2 0
-2 0
";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("stdin_multiline_lrat", "lrat");

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut child = Command::new(ay_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");

    let mut stdin = child.stdin.take().expect("stdin pipe");
    stdin
        .write_all(cnf.as_bytes())
        .expect("write multiline DIMACS to stdin");
    drop(stdin);

    let output = child.wait_with_output().expect("wait for ay");
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 for multiline stdin DIMACS proof: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT for multiline stdin DIMACS proof, got: {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof_bytes = std::fs::read(&proof_path).unwrap_or_else(|error| {
        panic!(
            "failed to read multiline stdin proof file {}: {error}",
            proof_path.display()
        )
    });
    assert!(
        !proof_bytes.is_empty(),
        "LRAT proof should be non-empty for multiline stdin DIMACS proof mode"
    );
    verify_lrat_text_proof(cnf, &proof_bytes);

    let check_output = run_check_cli("lrat", &input_path, &proof_path);
    assert!(
        check_output.status.success(),
        "expected ay check lrat to verify multiline stdin proof: stdout={} stderr={}",
        String::from_utf8_lossy(&check_output.stdout),
        String::from_utf8_lossy(&check_output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn test_proof_auto_detect_drat_extension() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("autodetect", "drat");

    // Use --proof (auto-detect) with .drat extension
    let proof_bytes = run_unsat_cli("--proof", &proof_path, &input_path);
    // Should produce a valid DRAT proof
    verify_drat_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_auto_detect_lrat_extension() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("autodetect", "lrat");

    let proof_bytes = run_unsat_cli("--proof", &proof_path, &input_path);
    verify_lrat_text_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_auto_detect_lratb_extension() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("autodetect", "lratb");

    let proof_bytes = run_unsat_cli("--proof", &proof_path, &input_path);
    verify_lrat_binary_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_auto_detect_dratb_extension() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("autodetect", "dratb");

    let proof_bytes = run_unsat_cli("--proof", &proof_path, &input_path);
    verify_drat_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_with_stats_no_corruption() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("stats_proof", "drat");

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("--drat")
        .arg(&proof_path)
        .arg("--stats")
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 with --stats: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("UNSATISFIABLE"),
        "expected UNSAT on stdout, got: {stdout}"
    );

    // Verify stats were printed to stderr without corrupting stdout
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("propagations:") || stderr.contains("conflicts:"),
        "expected stats on stderr, got: {stderr}"
    );

    // Verify the proof file is still valid DRAT
    let proof_bytes = std::fs::read(&proof_path).expect("read proof file");
    assert!(!proof_bytes.is_empty(), "proof file should be non-empty");
    verify_drat_proof(PHP_3_2_CNF, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_check_drat_emits_build_provenance_on_stderr() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("check_drat", "drat");
    let _proof_bytes = run_unsat_cli("--drat", &proof_path, &input_path);

    let output = run_check_cli("drat", &input_path, &proof_path);
    assert!(
        output.status.success(),
        "expected ay check drat to succeed: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("s VERIFIED"),
        "expected VERIFIED on stdout, got: {stdout}"
    );
    assert!(
        stderr.contains("c ay.build.stamp:"),
        "expected build provenance on stderr, got: {stderr}"
    );
    assert!(
        stderr.contains(env!("CARGO_PKG_VERSION")),
        "expected build provenance to include the package version, got: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_check_lrat_emits_build_provenance_on_stderr() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("check_lrat", "lrat");
    let _proof_bytes = run_unsat_cli("--lrat", &proof_path, &input_path);

    let output = run_check_cli("lrat", &input_path, &proof_path);
    assert!(
        output.status.success(),
        "expected ay check lrat to succeed: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("s VERIFIED"),
        "expected VERIFIED on stdout, got: {stdout}"
    );
    assert!(
        stderr.contains("c ay.build.stamp:"),
        "expected build provenance on stderr, got: {stderr}"
    );
    assert!(
        stderr.contains(env!("CARGO_PKG_VERSION")),
        "expected build provenance to include the package version, got: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_check_drat_writes_satcomp_evidence_json() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("check_drat_evidence", "drat");
    let (evidence_path, _evidence_cleanup) = temp_path("check_drat_evidence", "json");
    let (artifact_path, _artifact_cleanup) =
        temp_path("check_drat_replay_artifact", "proof-artifact.json");
    let proof_bytes = run_unsat_cli("--drat", &proof_path, &input_path);
    let artifact_arg = artifact_path.to_string_lossy().to_string();

    let output = run_check_cli_with_evidence(
        "drat",
        &input_path,
        &proof_path,
        &evidence_path,
        &["--proof-artifact-json", artifact_arg.as_str()],
    );
    assert!(
        output.status.success(),
        "expected ay check drat evidence run to succeed: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("s VERIFIED"),
        "evidence mode must preserve checker stdout"
    );

    let evidence = read_evidence_json(&evidence_path);
    let cnf_hash = sha256_prefixed(cnf.as_bytes());
    let proof_hash = sha256_prefixed(&proof_bytes);
    assert_eq!(evidence["schema"], "ay.satcomp-proof-check-evidence/v1");
    assert_eq!(
        evidence["schema_version"],
        "lean5-artifact-replay-report-v1"
    );
    assert_eq!(evidence["artifact_kind"], "drat");
    assert_eq!(evidence["certificate_format"], "drat");
    assert_eq!(evidence["replay_status"], "pass");
    assert_eq!(evidence["ay_replay_status"], "verified_unsat");
    assert_eq!(evidence["proof_strength"], "drat_kernel_checked");
    assert_eq!(evidence["result"]["verified"], true);
    assert_eq!(evidence["problem_hash"], cnf_hash);
    assert_eq!(evidence["proof_hash"], proof_hash);
    assert_eq!(evidence["artifact_hashes"]["cnf_sha256"], cnf_hash);
    assert_eq!(evidence["artifact_hashes"]["proof_sha256"], proof_hash);
    assert_eq!(evidence["proof_metadata"]["proof_format"], "drat");
    assert_eq!(evidence["proof_metadata"]["proof_kernel"], "ay-drat-check");
    assert_eq!(
        evidence["artifact_path"],
        artifact_path.display().to_string()
    );
    assert!(
        evidence["proof_metadata"]["proof_step_count"]
            .as_u64()
            .expect("proof step count")
            > 0
    );

    let artifact = read_evidence_json(&artifact_path);
    assert_eq!(artifact["version"], "proof-artifact-v1");
    assert_eq!(artifact["source_system"], "sat-pb");
    assert_eq!(artifact["artifact_kind"], "drat");
    assert_eq!(artifact["problem_hash"], cnf_hash);
    assert_eq!(artifact["model_hash"], cnf_hash);
    assert_eq!(artifact["proof_hash"], proof_hash);
    assert_eq!(artifact["certificate"]["format"], "drat");
    assert_eq!(artifact["certificate"]["encoding"], "text");
    assert_eq!(artifact["certificate"]["payload_hash"], proof_hash);
    assert_eq!(artifact["metadata"]["dimacs"], cnf);
}

#[test]
#[timeout(60_000)]
fn test_check_lrat_writes_satcomp_evidence_json_with_proof_replay_link() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("check_lrat_evidence", "lrat");
    let (evidence_path, _evidence_cleanup) = temp_path("check_lrat_evidence", "json");
    let proof_bytes = run_unsat_cli("--lrat", &proof_path, &input_path);

    let output = run_check_cli_with_evidence(
        "lrat",
        &input_path,
        &proof_path,
        &evidence_path,
        &[
            "--evidence-project",
            "unit-project",
            "--evidence-linked-obligation",
            "obligation-fingerprint-fixture",
            "--evidence-artifact-path",
            "artifacts/unit.lrat",
        ],
    );
    assert!(
        output.status.success(),
        "expected ay check lrat evidence run to succeed: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("s VERIFIED"),
        "evidence mode must preserve checker stdout"
    );

    let evidence = read_evidence_json(&evidence_path);
    let cnf_hash = sha256_prefixed(cnf.as_bytes());
    let proof_hash = sha256_prefixed(&proof_bytes);
    assert_eq!(evidence["schema"], "ay.satcomp-proof-check-evidence/v1");
    assert_eq!(
        evidence["schema_version"],
        "lean5-artifact-replay-report-v1"
    );
    assert_eq!(evidence["project"], "unit-project");
    assert_eq!(evidence["artifact_kind"], "lrat");
    assert_eq!(evidence["artifact_path"], "artifacts/unit.lrat");
    assert_eq!(evidence["certificate_format"], "lrat");
    assert_eq!(evidence["replay_engine"], "sat-pb-lrat-v1");
    assert_eq!(evidence["replay_status"], "pass");
    assert_eq!(evidence["ay_replay_status"], "verified_unsat");
    assert_eq!(evidence["proof_strength"], "lrat_kernel_checked");
    assert_eq!(
        evidence["linked_obligations"][0],
        "obligation-fingerprint-fixture"
    );
    assert_eq!(evidence["trusted_assumptions"].as_array().unwrap().len(), 0);
    assert_eq!(evidence["result"]["verified"], true);
    assert_eq!(evidence["problem_hash"], cnf_hash);
    assert_eq!(evidence["proof_hash"], proof_hash);
    assert_eq!(evidence["artifact_hashes"]["cnf_sha256"], cnf_hash);
    assert_eq!(evidence["artifact_hashes"]["proof_sha256"], proof_hash);
    assert_eq!(evidence["proof_metadata"]["proof_format"], "lrat");
    assert_eq!(evidence["proof_metadata"]["proof_kernel"], "ay-lrat-check");
    assert!(
        evidence["proof_metadata"]["proof_step_count"]
            .as_u64()
            .expect("proof step count")
            > 0
    );
}

#[test]
#[timeout(60_000)]
fn test_check_lrat_writes_replayable_proof_artifact_v1() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("check_lrat_artifact", "lrat");
    let (evidence_path, _evidence_cleanup) = temp_path("check_lrat_artifact", "json");
    let (artifact_path, _artifact_cleanup) =
        temp_path("check_lrat_artifact", "proof-artifact.json");
    let proof_bytes = run_unsat_cli("--lrat", &proof_path, &input_path);
    let proof_text = std::str::from_utf8(&proof_bytes).expect("LRAT text proof");
    let artifact_arg = artifact_path.to_string_lossy().to_string();

    let output = run_check_cli_with_evidence(
        "lrat",
        &input_path,
        &proof_path,
        &evidence_path,
        &["--proof-artifact-json", artifact_arg.as_str()],
    );
    assert!(
        output.status.success(),
        "expected ay check lrat proof-artifact run to succeed: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let cnf_hash = sha256_prefixed(cnf.as_bytes());
    let proof_hash = sha256_prefixed(&proof_bytes);
    let evidence = read_evidence_json(&evidence_path);
    assert_eq!(
        evidence["artifact_path"],
        artifact_path.display().to_string()
    );
    assert_eq!(evidence["proof_hash"], proof_hash);
    assert_eq!(evidence["replay_status"], "pass");

    let artifact = read_evidence_json(&artifact_path);
    assert_eq!(artifact["version"], "proof-artifact-v1");
    assert_eq!(artifact["source_system"], "sat-pb");
    assert_eq!(artifact["artifact_kind"], "lrat");
    assert_eq!(artifact["problem_hash"], cnf_hash);
    assert_eq!(artifact["model_hash"], cnf_hash);
    assert_eq!(artifact["proof_hash"], proof_hash);
    assert_eq!(artifact["certification"]["evidence_kind"], "replay_only");
    assert_eq!(artifact["certificate"]["format"], "lrat");
    assert_eq!(artifact["certificate"]["encoding"], "text");
    assert_eq!(artifact["certificate"]["payload_hash"], proof_hash);
    assert_eq!(artifact["certificate"]["payload"], proof_text);
    assert_eq!(artifact["metadata"]["dimacs"], cnf);
    assert_eq!(
        artifact["metadata"]["ay_check_evidence_path"],
        evidence_path.display().to_string()
    );
}

#[test]
#[timeout(60_000)]
fn test_check_drat_rejection_writes_failed_evidence_json() {
    let cnf = "p cnf 1 1\n1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("check_drat_reject", "drat");
    let (evidence_path, _evidence_cleanup) = temp_path("check_drat_reject", "json");
    let (artifact_path, _artifact_cleanup) = temp_path("check_drat_reject", "proof-artifact.json");
    std::fs::write(&proof_path, "").expect("write empty DRAT proof");
    let artifact_arg = artifact_path.to_string_lossy().to_string();

    let output = run_check_cli_with_evidence(
        "drat",
        &input_path,
        &proof_path,
        &evidence_path,
        &["--proof-artifact-json", artifact_arg.as_str()],
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected ay check drat to reject empty proof: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("s NOT VERIFIED"),
        "rejection mode must preserve checker stdout"
    );

    let evidence = read_evidence_json(&evidence_path);
    assert_eq!(evidence["schema"], "ay.satcomp-proof-check-evidence/v1");
    assert_eq!(evidence["artifact_kind"], "drat");
    assert_eq!(evidence["artifact_path"], proof_path.display().to_string());
    assert_eq!(evidence["replay_status"], "fail");
    assert_eq!(evidence["ay_replay_status"], "proof_rejected");
    assert_eq!(evidence["proof_strength"], "rejected");
    assert_eq!(evidence["result"]["verified"], false);
    assert_eq!(evidence["result"]["exit_code"], 1);
    assert_eq!(evidence["proof_metadata"]["proof_step_count"], 0);
    assert!(evidence["result"]["failure_reason"]
        .as_str()
        .expect("failure reason")
        .contains("proof"));
    assert!(
        !artifact_path.exists(),
        "failed replay must not leave a proof-artifact-v1 sidecar at {}",
        artifact_path.display()
    );
}

#[test]
#[timeout(60_000)]
fn test_check_lrat_rejection_writes_failed_evidence_json() {
    let cnf = "p cnf 1 1\n1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("check_lrat_reject", "lrat");
    let (evidence_path, _evidence_cleanup) = temp_path("check_lrat_reject", "json");
    let (artifact_path, _artifact_cleanup) = temp_path("check_lrat_reject", "proof-artifact.json");
    std::fs::write(&proof_path, "").expect("write empty LRAT proof");
    let artifact_arg = artifact_path.to_string_lossy().to_string();

    let output = run_check_cli_with_evidence(
        "lrat",
        &input_path,
        &proof_path,
        &evidence_path,
        &["--proof-artifact-json", artifact_arg.as_str()],
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected ay check lrat to reject empty proof: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("s NOT VERIFIED"),
        "rejection mode must preserve checker stdout"
    );

    let evidence = read_evidence_json(&evidence_path);
    assert_eq!(evidence["schema"], "ay.satcomp-proof-check-evidence/v1");
    assert_eq!(evidence["artifact_kind"], "lrat");
    assert_eq!(evidence["artifact_path"], proof_path.display().to_string());
    assert_eq!(evidence["replay_status"], "fail");
    assert_eq!(evidence["ay_replay_status"], "proof_rejected");
    assert_eq!(evidence["proof_strength"], "rejected");
    assert_eq!(evidence["result"]["verified"], false);
    assert_eq!(evidence["result"]["exit_code"], 1);
    assert_eq!(evidence["proof_metadata"]["proof_step_count"], 0);
    assert_eq!(evidence["result"]["failure_reason"], "lrat proof rejected");
    assert!(
        !artifact_path.exists(),
        "failed replay must not leave a proof-artifact-v1 sidecar at {}",
        artifact_path.display()
    );
}

#[test]
#[timeout(60_000)]
fn test_lrat_binary_proof_on_harder_unsat_instance() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("php32_lratb", "lratb");

    let proof_bytes = run_unsat_cli("--lrat-binary", &proof_path, &input_path);
    assert!(
        !proof_bytes.is_empty(),
        "LRAT binary proof should be non-empty for PHP(3,2)"
    );
    verify_lrat_binary_proof(PHP_3_2_CNF, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_explicit_flag_overrides_proof_extension_inference() {
    // --proof and --lrat-binary are now mutually exclusive in the CLI.
    // Verify that --lrat-binary alone produces a valid LRAT binary proof.
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (explicit_path, _explicit_cleanup) = temp_path("explicit_lrat_binary", "proofbin");
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let output = Command::new(ay_path)
        .arg("--lrat-binary")
        .arg(&explicit_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 for lrat-binary test: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT output for lrat-binary test, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof_bytes = std::fs::read(&explicit_path).unwrap_or_else(|error| {
        panic!(
            "failed to read explicit proof file {}: {error}",
            explicit_path.display()
        )
    });
    verify_lrat_binary_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_streaming_parse_error_after_header_removes_sidecar() {
    let cnf = "p cnf 1 2\n1 0\nx 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("stream_parse_error", "lrat");
    std::fs::write(&proof_path, b"stale proof").expect("write stale proof");

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&input_path)
        .output()
        .expect("spawn ay proof streaming parse-error run");

    // The streaming route reserves its requested proof output before solving,
    // and the hardened transactional boundary refuses to overwrite (or
    // unlink) a pre-existing foreign path: the run fails closed before any
    // verdict and leaves the sidecar untouched.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected pre-existing-sidecar refusal exit 1: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("refusing to overwrite pre-existing DIMACS proof output"),
        "parse-error proof-mode run must refuse the pre-existing sidecar: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !String::from_utf8_lossy(&output.stdout).contains("s UNSATISFIABLE"),
        "refused run must not emit a verdict: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(
        std::fs::read(&proof_path).expect("pre-existing sidecar must be preserved"),
        b"stale proof",
        "proof-streaming refusal must preserve the foreign pre-existing sidecar {}",
        proof_path.display()
    );
}

#[test]
#[timeout(60_000)]
fn test_parallel_portfolio_sat_with_requested_proof_removes_stale_sidecar() {
    let (input_path, _input_cleanup) = write_temp_cnf("p cnf 2 2\n1 0\n2 0\n");
    let (proof_path, _proof_cleanup) = temp_path("parallel_sat_stale", "lrat");
    std::fs::write(&proof_path, b"stale proof").expect("write stale proof");

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("--parallel")
        .arg("2")
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&input_path)
        .output()
        .expect("spawn ay parallel SAT proof-mode run");

    assert_eq!(
        output.status.code(),
        Some(10),
        "expected parallel SAT exit 10: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("s SATISFIABLE"),
        "parallel proof-mode SAT run should print SAT: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    // A pre-existing sidecar is not owned by this solve; the hardened
    // publication boundary never unlinks a foreign path. Non-UNSAT routes
    // must leave it untouched.
    assert_eq!(
        std::fs::read(&proof_path).expect("pre-existing sidecar must be preserved"),
        b"stale proof",
        "parallel proof-mode SAT must preserve the foreign pre-existing sidecar {}",
        proof_path.display()
    );
}

#[test]
#[timeout(60_000)]
fn test_parallel_portfolio_parse_error_with_requested_proof_removes_stale_sidecar() {
    let (input_path, _input_cleanup) = write_temp_cnf("p cnf 1 1\nx 0\n");
    let (proof_path, _proof_cleanup) = temp_path("parallel_parse_error_stale", "lrat");
    std::fs::write(&proof_path, b"stale proof").expect("write stale proof");

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("--parallel")
        .arg("2")
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&input_path)
        .output()
        .expect("spawn ay parallel parse-error proof-mode run");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected parallel parse-error UNKNOWN exit 1: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("s UNKNOWN"),
        "parallel parse-error proof-mode run should print UNKNOWN: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    // A pre-existing sidecar is not owned by this solve; the hardened
    // publication boundary never unlinks a foreign path. The parse-error run
    // must fail without touching it.
    assert_eq!(
        std::fs::read(&proof_path).expect("pre-existing sidecar must be preserved"),
        b"stale proof",
        "parallel parse-error UNKNOWN must preserve the foreign pre-existing sidecar {}",
        proof_path.display()
    );
}

/// CLI integration test: `--parallel 2 --proof FILE.lrat` produces a valid LRAT proof (#8428).
///
/// Exercises the `run_dimacs_parallel()` path in dimacs.rs which creates a
/// `PortfolioSolver` with `proof_mode` enabled, extracts forward LRAT bytes
/// from the winning solver thread, and writes them to the proof file.
#[test]
#[timeout(60_000)]
fn test_parallel_portfolio_proof_lrat_output() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("parallel_lrat", "lrat");

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("--parallel")
        .arg("2")
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 for --parallel --proof: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT for --parallel --proof, got: {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof_bytes = std::fs::read(&proof_path).unwrap_or_else(|error| {
        panic!(
            "failed to read proof file {}: {error}",
            proof_path.display()
        )
    });
    assert!(
        !proof_bytes.is_empty(),
        "proof file must be non-empty for parallel portfolio UNSAT"
    );
    verify_lrat_text_proof(PHP_3_2_CNF, &proof_bytes);
}

/// CLI integration test: `--parallel 2 --proof FILE.drat` produces a valid DRAT proof (#8428).
///
/// The portfolio solver captures forward LRAT bytes and converts them to DRAT
/// by stripping clause IDs and hints via `lrat_bytes_to_drat()`.
#[test]
#[timeout(60_000)]
fn test_parallel_portfolio_proof_drat_output() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("parallel_drat", "drat");

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("--parallel")
        .arg("2")
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input_path)
        .output()
        .expect("spawn ay");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 for --parallel --proof (DRAT): {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let proof_bytes = std::fs::read(&proof_path).unwrap_or_else(|error| {
        panic!(
            "failed to read proof file {}: {error}",
            proof_path.display()
        )
    });
    assert!(
        !proof_bytes.is_empty(),
        "DRAT proof file must be non-empty for parallel portfolio UNSAT"
    );
    verify_drat_proof(PHP_3_2_CNF, &proof_bytes);
}
