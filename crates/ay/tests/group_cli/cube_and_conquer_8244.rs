// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cube-and-conquer CLI readiness coverage for #8244.

use ntest::timeout;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

const ALL_THREE_VAR_ASSIGNMENTS_BLOCKED_CNF: &str = "\
p cnf 3 8
1 2 3 0
-1 2 3 0
1 -2 3 0
-1 -2 3 0
1 2 -3 0
-1 2 -3 0
1 -2 -3 0
-1 -2 -3 0
";

fn write_cnf(dir: &tempfile::TempDir, name: &str, contents: &str) -> std::path::PathBuf {
    let path = dir.path().join(name);
    std::fs::write(&path, contents).expect("write temp CNF");
    path
}

fn parse_dimacs_model(stdout: &str, num_vars: usize) -> Vec<bool> {
    let mut model = vec![None; num_vars];
    for line in stdout.lines().filter(|line| line.starts_with('v')) {
        for token in line[1..].split_whitespace() {
            let lit: i32 = token
                .parse()
                .unwrap_or_else(|error| panic!("invalid model literal {token:?}: {error}"));
            if lit == 0 {
                continue;
            }
            let var = lit.unsigned_abs() as usize;
            assert!(
                (1..=num_vars).contains(&var),
                "model literal {lit} is outside 1..={num_vars}"
            );
            let value = lit > 0;
            let slot = &mut model[var - 1];
            assert!(
                slot.replace(value).is_none(),
                "model assigns variable {var} more than once"
            );
        }
    }

    model
        .into_iter()
        .enumerate()
        .map(|(idx, value)| value.unwrap_or_else(|| panic!("model missing variable {}", idx + 1)))
        .collect()
}

fn assert_model_satisfies(model: &[bool], clauses: &[&[i32]]) {
    for clause in clauses {
        assert!(
            clause.iter().any(|&lit| {
                let var = lit.unsigned_abs() as usize;
                let value = model[var - 1];
                (lit > 0 && value) || (lit < 0 && !value)
            }),
            "model {model:?} does not satisfy clause {clause:?}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn cube_and_conquer_cli_sat_returns_sat_competition_verdict() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let input = write_cnf(&temp, "sat.cnf", "p cnf 2 2\n1 0\n2 0\n");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--cube-and-conquer")
        .arg("1")
        .arg("--parallel")
        .arg("2")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&input)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay cube-and-conquer SAT run");

    assert_eq!(
        output.status.code(),
        Some(10),
        "SAT CnC run should use SAT competition exit 10: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("s SATISFIABLE"),
        "SAT CnC run should print SAT competition verdict: {stdout}"
    );
    let model = parse_dimacs_model(&stdout, 2);
    assert_model_satisfies(&model, &[&[1], &[2]]);

    let stderr = String::from_utf8_lossy(&output.stderr);
    for expected in [
        "c cube-and-conquer: depth 1, 2 threads",
        "c cube-and-conquer:",
        "c sat.policy: cube-and-conquer",
        "c sat.policy_source: --cube-and-conquer",
        "c sat.route_profile: standard",
        "c sat.proof_active: no",
    ] {
        assert!(
            stderr.contains(expected),
            "missing cube-and-conquer evidence line {expected:?}: {stderr}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn cube_and_conquer_cli_requested_proof_sat_removes_stale_sidecar() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let input = write_cnf(&temp, "sat-proof.cnf", "p cnf 2 2\n1 0\n2 0\n");
    let proof = temp.path().join("sat-proof.lrat");
    std::fs::write(&proof, b"stale proof").expect("write stale proof");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--cube-and-conquer")
        .arg("1")
        .arg("--parallel")
        .arg("2")
        .arg("--proof")
        .arg(&proof)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&input)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay cube-and-conquer requested-proof SAT run");

    assert_eq!(
        output.status.code(),
        Some(10),
        "SAT CnC proof-mode run should use SAT competition exit 10: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("s SATISFIABLE"),
        "SAT CnC proof-mode run should print SAT competition verdict: {stdout}"
    );
    let model = parse_dimacs_model(&stdout, 2);
    assert_model_satisfies(&model, &[&[1], &[2]]);
    // A pre-existing sidecar is not owned by this solve; the hardened
    // publication boundary never unlinks a foreign path (it may be an
    // unrelated hard-linked file). Non-UNSAT routes must leave it untouched.
    assert_eq!(
        std::fs::read(&proof).expect("pre-existing sidecar must be preserved"),
        b"stale proof",
        "SAT CnC proof-mode run must preserve the foreign pre-existing sidecar at {}",
        proof.display()
    );
}

#[test]
#[timeout(60_000)]
fn cube_and_conquer_cli_requested_proof_unsat_fails_closed_without_file() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let input = write_cnf(
        &temp,
        "split-unsat.cnf",
        ALL_THREE_VAR_ASSIGNMENTS_BLOCKED_CNF,
    );
    let proof = temp.path().join("split-unsat.drat");
    std::fs::write(&proof, b"stale proof").expect("write stale proof");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--cube-and-conquer")
        .arg("1")
        .arg("--parallel")
        .arg("2")
        .arg("--proof")
        .arg(&proof)
        .arg("--proof-format")
        .arg("drat")
        .arg("--verify-proof")
        .arg(&input)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay cube-and-conquer requested-proof UNSAT run");

    assert_eq!(
        output.status.code(),
        Some(0),
        "proof-incomplete CnC UNSAT run with requested proof should fail closed: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("s UNKNOWN"),
        "proof-incomplete CnC UNSAT run should print UNKNOWN, not UNSAT: {stdout}"
    );
    assert!(
        !stdout.contains("s UNSATISFIABLE"),
        "proof-incomplete CnC must not print an UNSAT verdict: {stdout}"
    );
    // A pre-existing sidecar is not owned by this solve; the hardened
    // publication boundary never unlinks a foreign path. The incomplete-proof
    // run must fail closed without replacing or removing it.
    assert_eq!(
        std::fs::read(&proof).expect("pre-existing sidecar must be preserved"),
        b"stale proof",
        "proof-incomplete CnC must preserve the foreign pre-existing sidecar at {}",
        proof.display()
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    for expected in [
        "c sat.proof_active: yes",
        "c sat.proof_format: drat",
        "c sat.verify_proof: on",
        "without an aggregate proof; returning UNKNOWN",
    ] {
        assert!(
            stderr.contains(expected),
            "missing requested-proof fail-closed evidence line {expected:?}: {stderr}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn cube_and_conquer_cli_parse_error_with_requested_proof_removes_stale_sidecar() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let input = write_cnf(&temp, "parse-error.cnf", "p cnf 1 1\nx 0\n");
    let proof = temp.path().join("parse-error.lrat");
    std::fs::write(&proof, b"stale proof").expect("write stale proof");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--cube-and-conquer")
        .arg("1")
        .arg("--parallel")
        .arg("2")
        .arg("--proof")
        .arg(&proof)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&input)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay cube-and-conquer parse-error proof-mode run");

    assert_eq!(
        output.status.code(),
        Some(1),
        "proof-mode CnC parse error should exit 1: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("s UNKNOWN"),
        "proof-mode CnC parse error should print UNKNOWN: {stdout}"
    );
    // A pre-existing sidecar is not owned by this solve; the hardened
    // publication boundary never unlinks a foreign path. The parse-error run
    // must fail without touching it.
    assert_eq!(
        std::fs::read(&proof).expect("pre-existing sidecar must be preserved"),
        b"stale proof",
        "proof-mode CnC parse error must preserve the foreign pre-existing sidecar at {}",
        proof.display()
    );
}

#[test]
#[timeout(60_000)]
fn cube_and_conquer_cli_unsat_fails_closed_to_unknown_without_aggregate_proof() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let input = write_cnf(&temp, "unsat.cnf", "p cnf 1 2\n1 0\n-1 0\n");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--cube-and-conquer")
        .arg("1")
        .arg("--parallel")
        .arg("2")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&input)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay cube-and-conquer UNSAT run");

    assert_eq!(
        output.status.code(),
        Some(0),
        "proof-incomplete CnC UNSAT run should not claim UNSAT: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("s UNKNOWN"),
        "proof-incomplete CnC UNSAT run should fail closed to UNKNOWN: {stdout}"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    for expected in [
        "without an aggregate proof; returning UNKNOWN",
        "c reason: incomplete (cube-and-conquer could not determine satisfiability)",
    ] {
        assert!(
            stderr.contains(expected),
            "missing proof-gap evidence line {expected:?}: {stderr}"
        );
    }
}
