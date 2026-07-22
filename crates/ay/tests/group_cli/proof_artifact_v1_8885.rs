// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn temp_path(stem: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_proof_artifact_v1_{}_{}_{}.{}",
        std::process::id(),
        stem,
        id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn write_temp_file(stem: &str, extension: &str, contents: &str) -> (PathBuf, CleanupGuard) {
    let (path, guard) = temp_path(stem, extension);
    std::fs::write(&path, contents).expect("write temp input");
    (path, guard)
}

fn read_json(path: &Path) -> Value {
    let text = std::fs::read_to_string(path).expect("read artifact");
    serde_json::from_str(&text).expect("artifact is valid JSON")
}

fn assert_sha256(value: &Value) {
    let text = value.as_str().expect("hash is a string");
    assert!(text.starts_with("sha256:"), "hash must be prefixed: {text}");
    assert_eq!(text.len(), "sha256:".len() + 64, "hash length");
}

fn assert_common_envelope(artifact: &Value, proof_format: &str) {
    assert_eq!(artifact["version"], "proof-artifact-v1");
    assert_eq!(artifact["source_system"], "ay");
    assert_eq!(artifact["artifact_kind"], "ay_proof_artifact");
    assert_eq!(artifact["producer"]["name"], "ay");
    assert!(
        artifact["producer"]["commit"]
            .as_str()
            .is_some_and(|commit| !commit.is_empty()),
        "producer commit must be present"
    );
    assert_sha256(&artifact["problem_hash"]);
    assert_sha256(&artifact["model_hash"]);
    assert_sha256(&artifact["proof_hash"]);
    assert_eq!(artifact["verifier_constants"].as_array().unwrap().len(), 0);
    assert_eq!(artifact["certificate"]["encoding"], "json");
    assert_eq!(
        artifact["certificate"]["format"],
        format!("ay-{proof_format}-envelope-v1")
    );
    assert_eq!(artifact["metadata"]["proof_format"], proof_format);
    assert_eq!(
        artifact["certificate"]["payload"]["proof_format"],
        proof_format
    );
}

#[test]
#[timeout(60_000)]
fn dimacs_default_drat_can_emit_proof_artifact_v1() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input, _input_guard) = write_temp_file("input", "cnf", cnf);
    let (artifact_path, _artifact_guard) = temp_path("dimacs", "json");
    let default_proof_path = input.with_file_name(format!(
        "{}.drat",
        input.file_name().unwrap().to_string_lossy()
    ));
    let _proof_guard = CleanupGuard(default_proof_path.clone());
    let _ = std::fs::remove_file(&default_proof_path);
    let _ = std::fs::remove_file(&artifact_path);

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--proof-artifact")
        .arg(&artifact_path)
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "stdout={stdout}; stderr={stderr}"
    );
    assert!(stdout.contains("UNSATISFIABLE"), "stdout={stdout}");
    assert!(default_proof_path.exists(), "default proof should exist");

    let artifact = read_json(&artifact_path);
    assert_common_envelope(&artifact, "drat");
    assert_eq!(artifact["metadata"]["solver_mode"], "dimacs-sat");
    assert_eq!(artifact["metadata"]["logic"], "DIMACS-CNF");
    assert_eq!(artifact["metadata"]["theories"], "sat");
    assert_eq!(
        artifact["certificate"]["payload"]["problem"].as_str(),
        Some(cnf)
    );
    assert!(
        artifact["certificate"]["payload"]["proof"]["text"]
            .as_str()
            .is_some_and(|proof| proof.contains("0")),
        "DRAT proof text should be embedded"
    );
}

#[test]
#[timeout(60_000)]
fn smt_alethe_can_emit_proof_artifact_v1() {
    let smt =
        "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n";
    let (input, _input_guard) = write_temp_file("input", "smt2", smt);
    let (proof_path, _proof_guard) = temp_path("proof", "alethe");
    let (artifact_path, _artifact_guard) = temp_path("smt", "json");

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-artifact")
        .arg(&artifact_path)
        .arg("--no-verify-proof")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "stdout={stdout}; stderr={stderr}; status={:?}",
        output.status.code()
    );
    assert!(stdout.contains("unsat"), "stdout={stdout}; stderr={stderr}");

    let artifact = read_json(&artifact_path);
    assert_common_envelope(&artifact, "alethe");
    assert_eq!(artifact["metadata"]["solver_mode"], "smt-lib");
    assert_eq!(artifact["metadata"]["logic"], "QF_UF");
    assert_eq!(
        artifact["certificate"]["payload"]["theory_metadata"]["logic"],
        "QF_UF"
    );
    assert_eq!(
        artifact["certificate"]["payload"]["problem"].as_str(),
        Some(smt)
    );
    assert!(
        artifact["certificate"]["payload"]["proof"]["text"]
            .as_str()
            .is_some_and(|proof| proof.contains(":rule")),
        "Alethe proof text should be embedded"
    );
}
