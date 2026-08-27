// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the soundness-grounded `--lean-verify` route.
//!
//! Validates that:
//! 1. The CLI flag is registered on `ay solve --help` alongside
//!    `--verify-proof` (#8771).
//! 2. The flag is gated on `--proof FILE` (clap `requires = "proof"`) and
//!    `--lean-path` is gated on `--lean-verify`.
//! 3. The emitted theorem binds the original CNF and concludes `Unsat` via the
//!    verified `AySoundness.lratCheck_sound` theorem.
//! 4. Rejection path: when `--lean-path` points at a bogus binary, the
//!    verifier reports `Unavailable` and the explicit verification promise
//!    fails closed with exit 2 and no UNSAT verdict.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Trivially-UNSAT DIMACS: (x) AND (not x). Smallest possible UNSAT input
/// so the whole pipeline finishes within the default test timeout. Phase 1
/// uses DIMACS input (SAT path) because Lean4 export is already wired for
/// DIMACS in `ay-sat::lean_export` — the SMT path is Phase 2+ work.
const TRIVIAL_UNSAT: &str = "p cnf 1 2\n1 0\n-1 0\n";

struct CleanupGuard(Vec<PathBuf>);
impl Drop for CleanupGuard {
    fn drop(&mut self) {
        for p in &self.0 {
            let _ = std::fs::remove_file(p);
        }
    }
}

fn temp_paths(stem: &str) -> (PathBuf, PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let cnf = std::env::temp_dir().join(format!("ay_lean_verify_{pid}_{stem}_{id}.cnf"));
    let proof = std::env::temp_dir().join(format!("ay_lean_verify_{pid}_{stem}_{id}.lean4"));
    std::fs::write(&cnf, TRIVIAL_UNSAT).expect("write temp cnf");
    let guard = CleanupGuard(vec![cnf.clone(), proof.clone()]);
    (cnf, proof, guard)
}

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn lake_available() -> bool {
    Command::new("lake")
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

/// `--lean-verify` and `--lean-path` MUST appear in `ay solve --help` so
/// users discover the flag. Confirms clap registration.
#[test]
fn test_lean_verify_flag_in_help() {
    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--help")
        .output()
        .expect("spawn ay --help");
    let help = String::from_utf8_lossy(&output.stdout);
    assert!(
        help.contains("--lean-verify"),
        "--lean-verify must appear in ay solve --help; help={help}"
    );
    assert!(
        help.contains("--lean-path"),
        "--lean-path must appear in ay solve --help; help={help}"
    );
    assert!(
        help.contains("20 only when Lean accepts") && help.contains("never publishes UNSAT"),
        "--lean-verify help must document the fail-closed unavailable contract; help={help}"
    );
}

/// `--lean-verify` is gated on `--proof FILE` via clap `requires = "proof"`.
/// Invoking it without `--proof` MUST error out at argument parsing time,
/// not silently succeed.
#[test]
fn test_lean_verify_without_proof_flag_errors() {
    let (cnf, _, _guard) = temp_paths("requires_proof");
    let output = Command::new(ay_binary())
        .arg("--lean-verify")
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_ne!(
        output.status.code(),
        Some(20),
        "--lean-verify without --proof must NOT report UNSAT as verified; stderr={stderr}"
    );
    // clap emits "the following required arguments were not provided" or
    // similar when a `requires` gate fails. Accept either a non-zero exit
    // (preferred) or a warning that --lean-verify was ignored.
    assert!(
        output.status.code() != Some(0) && output.status.code() != Some(20),
        "expected non-success exit when --lean-verify missing --proof; exit={:?}; stderr={stderr}",
        output.status.code()
    );
}

/// `--lean-path` is gated on `--lean-verify` via clap `requires`. Invoking
/// `--lean-path` alone (without `--lean-verify`) must error at argument
/// parsing time.
#[test]
fn test_lean_path_without_lean_verify_errors() {
    let (cnf, proof, _guard) = temp_paths("lean_path_req");
    let output = Command::new(ay_binary())
        .arg("--lean-path")
        .arg("/nonexistent/lean")
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    assert_ne!(
        output.status.code(),
        Some(20),
        "--lean-path without --lean-verify must not succeed; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// End-to-end: run ay on a trivial UNSAT DIMACS with `--lean-verify` and a
/// `.lean4` proof path, pointing `--lean-path` at a definitely-missing
/// binary. The verifier MUST report `Unavailable`; because an explicitly
/// requested kernel check did not run, AY must exit 2 without publishing
/// UNSAT.
#[test]
fn test_lean_verify_unavailable_bogus_binary_fails_closed() {
    if !lake_available() {
        return;
    }
    let (cnf, proof, _guard) = temp_paths("unavailable");
    let output = Command::new(ay_binary())
        .arg("--lean-verify")
        .arg("--lean-path")
        .arg("/nonexistent/bogus-lean-binary-xyz")
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "an unavailable explicitly requested Lean check must exit 2; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !stdout.contains("s UNSATISFIABLE"),
        "unavailable Lean verification leaked UNSAT: {stdout}"
    );
    assert!(
        stderr.contains("Lean verification unavailable"),
        "expected 'Lean verification unavailable' note on stderr; stderr={stderr}"
    );
    // Unavailable is an unfulfilled verification request, not a kernel
    // rejection, so it should not be mislabeled as a soundness failure.
    assert!(
        !stderr.contains("SOUNDNESS FAILURE"),
        "Unavailable path must not claim soundness failure; stderr={stderr}"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn lean_verifier_reads_authenticated_snapshot_while_public_proof_is_swapped() {
    use std::os::unix::fs::PermissionsExt as _;

    if !lake_available() {
        return;
    }

    let temp = tempfile::tempdir().expect("temporary directory");
    let cnf = temp.path().join("input.cnf");
    let proof = temp.path().join("proof.lean4");
    let replacement = temp.path().join("replacement.lean4");
    let observed_path = temp.path().join("observed-path.txt");
    let observed_bytes = temp.path().join("observed-bytes.lean4");
    let fake_lean = temp.path().join("fake-lean.sh");
    std::fs::write(&cnf, TRIVIAL_UNSAT).expect("write CNF");
    std::fs::write(&replacement, "-- MUTABLE_PUBLIC_REPLACEMENT\n")
        .expect("write replacement proof");
    std::fs::write(
        &fake_lean,
        r#"#!/bin/sh
set -eu
snapshot=$1
saved="${AY_TEST_PUBLIC_PROOF}.saved"
restore_public() {
  rm -f "$AY_TEST_PUBLIC_PROOF"
  if [ -e "$saved" ]; then
    mv "$saved" "$AY_TEST_PUBLIC_PROOF"
  fi
}
trap restore_public EXIT HUP INT TERM
test "$snapshot" != "$AY_TEST_PUBLIC_PROOF"
mv "$AY_TEST_PUBLIC_PROOF" "$saved"
cp "$AY_TEST_REPLACEMENT" "$AY_TEST_PUBLIC_PROOF"
printf '%s\n' "$snapshot" > "$AY_TEST_OBSERVED_PATH"
cp "$snapshot" "$AY_TEST_OBSERVED_BYTES"
grep -q 'import AySoundness.Lrat' "$snapshot"
grep -q 'theorem unsat : Unsat (clauses original)' "$snapshot"
! grep -q 'native_decide' "$snapshot"
! grep -q 'MUTABLE_PUBLIC_REPLACEMENT' "$snapshot"
"#,
    )
    .expect("write fake Lean");
    let mut permissions = std::fs::metadata(&fake_lean)
        .expect("fake Lean metadata")
        .permissions();
    permissions.set_mode(0o700);
    std::fs::set_permissions(&fake_lean, permissions).expect("make fake Lean executable");

    let output = Command::new(ay_binary())
        .arg("--lean-verify")
        .arg("--lean-path")
        .arg(&fake_lean)
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .env("AY_TEST_PUBLIC_PROOF", &proof)
        .env("AY_TEST_REPLACEMENT", &replacement)
        .env("AY_TEST_OBSERVED_PATH", &observed_path)
        .env("AY_TEST_OBSERVED_BYTES", &observed_bytes)
        .output()
        .expect("spawn ay with swap-capable fake Lean");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(20),
        "authenticated snapshot verification failed: stdout={stdout}; stderr={stderr}"
    );
    let verifier_path = std::fs::read_to_string(&observed_path).expect("read verifier argv");
    assert_ne!(verifier_path.trim(), proof.to_string_lossy());
    let checked = std::fs::read_to_string(&observed_bytes).expect("read checked snapshot bytes");
    assert!(checked.contains("theorem unsat : Unsat (clauses original)"));
    assert!(!checked.contains("native_decide"));
    assert!(!checked.contains("MUTABLE_PUBLIC_REPLACEMENT"));
    let retained = std::fs::read_to_string(&proof).expect("read restored public proof");
    assert!(retained.contains("theorem proof_valid"));
    assert!(!retained.contains("MUTABLE_PUBLIC_REPLACEMENT"));
}

/// `--proof file.lean4` must emit the original clauses and a genuine UNSAT
/// theorem grounded in the verified checker, not a self-defined Boolean
/// checker whose acceptance has no proved connection to unsatisfiability.
#[test]
fn test_lean4_proof_output_contains_verified_soundness_boundary() {
    let (cnf, proof, _guard) = temp_paths("kernel_artifact");
    let output = Command::new(ay_binary())
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit 20; stdout={stdout}; stderr={stderr}"
    );

    let emitted = std::fs::read_to_string(&proof).expect("read emitted Lean4 proof");
    for marker in [
        "import AySoundness.Lrat",
        "def original : List (Cid × Clause)",
        "def proof : List (Cid × Clause × List Int)",
        "theorem proof_valid",
        "theorem unsat : Unsat (clauses original)",
        "lratCheck_sound",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 10000000",
        "(1, [1])",
        "(2, [-1])",
    ] {
        assert!(
            emitted.contains(marker),
            "Lean4 proof missing marker {marker:?}; first 800 bytes:\n{}",
            &emitted[..emitted.len().min(800)]
        );
    }
    assert!(
        !emitted.contains("native_decide") && !emitted.contains("def lratCheck "),
        "Lean4 proof must use the imported verified checker"
    );
}

/// Exercise a generated proof whose original-clause table exceeds Lean's
/// default recursion depth. The pinned project must elaborate the bound theorem
/// under the emitter's explicit resource policy before UNSAT is published.
#[test]
fn test_lean_verify_with_pinned_project_accepts_deep_bound_unsat() {
    if !lake_available() {
        return;
    }
    let (cnf, proof, _guard) = temp_paths("pinned_project");
    let repeated_units = 1_600;
    let mut deep_unsat = format!("p cnf 1 {}\n", repeated_units + 1);
    for _ in 0..repeated_units {
        deep_unsat.push_str("1 0\n");
    }
    deep_unsat.push_str("-1 0\n");
    std::fs::write(&cnf, deep_unsat).expect("write deep UNSAT CNF");
    let output = Command::new(ay_binary())
        .arg("--lean-verify")
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .output()
        .expect("spawn ay with pinned Lean project");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "pinned project did not verify bound UNSAT: stdout={stdout}; stderr={stderr}"
    );
    assert!(stdout.contains("s UNSATISFIABLE"));
    assert!(stderr.contains("Lean verification: OK"));
    let emitted = std::fs::read_to_string(&proof).expect("read deep Lean proof");
    assert!(emitted.contains("-- Original clauses: 1601"));
}

/// `--lean-verify` only runs when the emitted proof is Lean4. If the user
/// combines `--lean-verify` with a `.drat` proof path, the explicit Lean
/// verification contract cannot be fulfilled. AY must fail closed with exit 2
/// before publishing UNSAT, even though the DRAT checker accepts the file.
#[test]
fn test_lean_verify_with_drat_proof_fails_closed() {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let cnf = std::env::temp_dir().join(format!("ay_lean_verify_drat_{pid}_{id}.cnf"));
    let proof = std::env::temp_dir().join(format!("ay_lean_verify_drat_{pid}_{id}.drat"));
    std::fs::write(&cnf, TRIVIAL_UNSAT).expect("write temp cnf");
    let _guard = CleanupGuard(vec![cnf.clone(), proof.clone()]);

    let output = Command::new(ay_binary())
        .arg("--lean-verify")
        .arg("--proof")
        .arg(&proof)
        .arg(&cnf)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "non-Lean4 output cannot fulfill --lean-verify; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !stdout.contains("s UNSATISFIABLE"),
        "non-Lean4 --lean-verify leaked UNSAT: {stdout}"
    );
    assert!(
        stderr.contains("--lean-verify requires a Lean4 proof"),
        "expected format-mismatch error on stderr; stderr={stderr}"
    );
}
