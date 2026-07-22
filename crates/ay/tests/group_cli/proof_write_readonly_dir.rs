// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A default (opportunistic) Alethe proof-write failure must NOT change the
//! exit code once the verdict is already on stdout. Regression for the
//! read-only input-directory deployment blocker (nix store, docker RO mount,
//! CI cache, mounted corpus): AY used to print `unsat` and then `exit 1` when
//! it could not write `<input>.alethe` next to a read-only input, breaking
//! every such deployment. z3 exits 0. The verdict is unaffected by whether the
//! optional certificate could be written.

use ntest::timeout;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

fn readonly_unsat_input(stem: &str) -> (std::path::PathBuf, std::path::PathBuf) {
    static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "ay_ro_proof_{}_{}_{}",
        std::process::id(),
        stem,
        id
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("unsat.smt2");
    fs::write(
        &file,
        "(declare-const x Int)\n(assert (< x 0))\n(assert (> x 0))\n(check-sat)\n",
    )
    .expect("write smt2");
    fs::set_permissions(&dir, fs::Permissions::from_mode(0o555)).expect("chmod ro");
    (dir, file)
}

fn readonly_unsat_dimacs_input(stem: &str) -> (std::path::PathBuf, std::path::PathBuf) {
    static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "ay_ro_dimacs_proof_{}_{}_{}",
        std::process::id(),
        stem,
        id
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp DIMACS directory");
    let file = dir.join("unsat.cnf");
    fs::write(&file, "p cnf 1 2\n1 0\n-1 0\n").expect("write DIMACS input");
    fs::set_permissions(&dir, fs::Permissions::from_mode(0o555)).expect("chmod DIMACS dir ro");
    (dir, file)
}

fn write_safe_chc_input(directory: &std::path::Path) -> std::path::PathBuf {
    let input = directory.join("safe.smt2");
    fs::write(
        &input,
        "(set-logic HORN)\n(declare-fun Inv (Int) Bool)\n(assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))\n(check-sat)\n",
    )
    .expect("write safe CHC input");
    input
}

fn write_unsafe_chc_input(directory: &std::path::Path) -> std::path::PathBuf {
    let input = directory.join("unsafe.smt2");
    fs::write(
        &input,
        "(set-logic HORN)\n(declare-fun Inv (Int) Bool)\n(assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))\n(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))\n(check-sat)\n",
    )
    .expect("write unsafe CHC input");
    input
}

/// Make the input directory read-only. Privileged test runners can bypass
/// mode bits, so in that environment plant a directory at the default output
/// path as a deterministic fallback publication failure.
fn block_default_chc_certificate(
    directory: &std::path::Path,
    input: &std::path::Path,
) -> std::path::PathBuf {
    let certificate = std::path::PathBuf::from(format!("{}.chccert", input.display()));
    fs::set_permissions(directory, fs::Permissions::from_mode(0o555))
        .expect("chmod CHC directory read-only");

    let probe = directory.join(".ay-write-probe");
    if fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&probe)
        .is_ok()
    {
        fs::remove_file(&probe).expect("remove privileged write probe");
        fs::create_dir(&certificate).expect("block default CHC certificate target");
    }
    certificate
}

#[test]
#[timeout(30_000)]
fn default_proof_write_failure_keeps_exit_zero_on_readonly_dir() {
    let (dir, file) = readonly_unsat_input("optional");
    // Make the directory read-only so the default `<input>.alethe` write fails
    // (under a non-root test runner — the common CI case).
    fs::set_permissions(&dir, fs::Permissions::from_mode(0o555)).expect("chmod ro");

    let out = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(&file)
        .output()
        .expect("spawn ay");

    // Restore permissions so cleanup can remove the directory.
    let _ = fs::set_permissions(&dir, fs::Permissions::from_mode(0o755));
    let _ = fs::remove_dir_all(&dir);

    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stdout.lines().any(|l| l.trim() == "unsat"),
        "expected `unsat` on stdout, got:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        out.status.success(),
        "a default proof-write failure must keep exit 0 once the verdict is emitted; \
         got exit {:?}\nstderr:\n{stderr}",
        out.status.code()
    );
}

#[test]
#[timeout(30_000)]
fn strict_default_proof_write_failure_downgrades_before_unsat_publication() {
    let (dir, file) = readonly_unsat_input("strict");

    let out = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--strict-proofs")
        .arg(&file)
        .output()
        .expect("spawn ay");

    let _ = fs::set_permissions(&dir, fs::Permissions::from_mode(0o755));
    let _ = fs::remove_dir_all(&dir);

    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stdout.lines().any(|line| line.trim() == "unknown"),
        "strict failure must publish unknown: stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !stdout.lines().any(|line| line.trim() == "unsat"),
        "strict failure leaked UNSAT: {stdout}"
    );
    assert!(out.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        stderr.contains("strict proof mode rejected UNSAT"),
        "missing strict diagnostic: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn dimacs_optional_default_proof_failure_keeps_unsat_verdict() {
    let (dir, file) = readonly_unsat_dimacs_input("optional");
    let default_proof = std::path::PathBuf::from(format!("{}.drat", file.display()));

    let out = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(&file)
        .output()
        .expect("spawn ay DIMACS optional default proof regression");

    let _ = fs::set_permissions(&dir, fs::Permissions::from_mode(0o755));
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(
        out.status.code(),
        Some(20),
        "optional DIMACS proof I/O must not reject UNSAT; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "s UNSATISFIABLE"),
        "optional DIMACS proof failure lost UNSAT: {stdout}"
    );
    assert!(
        !stdout.lines().any(|line| line.trim() == "s UNKNOWN"),
        "optional DIMACS proof failure downgraded the verdict: {stdout}"
    );
    assert!(
        stderr.contains("Warning: optional synthesized DIMACS proof")
            && stderr.contains("solver verdict remains authoritative"),
        "missing optional-proof warning: {stderr}"
    );
    assert!(
        !default_proof.exists(),
        "failed optional proof publication left a default proof behind"
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
#[timeout(30_000)]
fn dimacs_explicit_proof_create_failure_is_fatal_before_unsat() {
    let (dir, file) = readonly_unsat_dimacs_input("explicit");
    let proof = dir.join("requested.drat");

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["solve", "--no-verify-proof", "--proof"])
        .arg(&proof)
        .arg(&file)
        .output()
        .expect("spawn AY with explicit DIMACS proof");

    let _ = fs::set_permissions(&dir, fs::Permissions::from_mode(0o755));
    let _ = fs::remove_dir_all(&dir);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        !stdout
            .lines()
            .any(|line| matches!(line.trim(), "s UNSATISFIABLE" | "s UNKNOWN")),
        "explicit proof failure leaked a DIMACS verdict: {stdout}"
    );
    assert!(
        stderr.contains("failed to create DIMACS proof") && stderr.contains("requested.drat"),
        "missing fatal explicit-proof diagnostic: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn dimacs_required_gate_default_proof_io_failure_downgrades_to_unknown() {
    for gate in ["--strict-proofs", "--self-check"] {
        let (dir, file) = readonly_unsat_dimacs_input(gate.trim_start_matches("--"));
        let out = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg(gate)
            .arg(&file)
            .output()
            .expect("spawn ay DIMACS required-proof gate");

        let _ = fs::set_permissions(&dir, fs::Permissions::from_mode(0o755));
        let _ = fs::remove_dir_all(&dir);

        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "{gate} certification failure must downgrade, not error; stdout={stdout}; stderr={stderr}"
        );
        assert!(
            stdout.lines().any(|line| line.trim() == "s UNKNOWN"),
            "{gate} proof I/O failure did not publish DIMACS UNKNOWN: {stdout}"
        );
        assert!(
            !stdout.lines().any(|line| line.trim() == "s UNSATISFIABLE"),
            "{gate} proof I/O failure leaked DIMACS UNSAT: {stdout}"
        );
        assert!(
            stderr.contains(gate)
                && stderr.contains("rejected UNSAT")
                && stderr.contains("failed to create DIMACS proof"),
            "{gate} failure diagnostic did not identify the certification failure: {stderr}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn chc_optional_default_certificate_failure_keeps_definitive_verdict() {
    for (case, write_input, expected) in [
        (
            "safe",
            write_safe_chc_input as fn(&std::path::Path) -> std::path::PathBuf,
            "sat",
        ),
        ("unsafe", write_unsafe_chc_input, "unsat"),
    ] {
        for (route, route_args) in [
            ("content", &[][..]),
            ("file-portfolio", &["--portfolio"][..]),
        ] {
            let temp = tempfile::tempdir().expect("temporary directory");
            let input = write_input(temp.path());
            let certificate = block_default_chc_certificate(temp.path(), &input);

            let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
            command.args(["solve", "--no-verify-proof"]);
            command.args(route_args);
            let output = command
                .arg(&input)
                .output()
                .expect("spawn AY with optional CHC certificate");

            fs::set_permissions(temp.path(), fs::Permissions::from_mode(0o755))
                .expect("restore CHC directory permissions");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            assert!(
                output.status.success(),
                "{case}/{route}: stdout={stdout}; stderr={stderr}"
            );
            assert!(
                stdout.lines().any(|line| line.trim() == expected),
                "{case}/{route}: optional certificate failure lost {expected}: {stdout}"
            );
            assert!(
                !stdout.lines().any(|line| line.trim() == "unknown"),
                "{case}/{route}: optional certificate failure downgraded the verdict: {stdout}"
            );
            assert!(
                stderr.contains("Warning: optional synthesized CHC certificate")
                    && stderr.contains("solver verdict remains authoritative"),
                "{case}/{route}: missing optional-certificate warning: {stderr}"
            );
            assert!(
                !certificate.is_file(),
                "{case}/{route}: failed default publication left a certificate file"
            );
        }
    }
}

#[test]
#[timeout(30_000)]
fn chc_required_gate_default_certificate_failure_downgrades_to_unknown() {
    for (gate, route_args, write_input) in [
        (
            "--strict-proofs",
            &[][..],
            write_safe_chc_input as fn(&std::path::Path) -> std::path::PathBuf,
        ),
        (
            "--strict-proofs",
            &["--portfolio"][..],
            write_unsafe_chc_input as fn(&std::path::Path) -> std::path::PathBuf,
        ),
        ("--self-check", &[][..], write_unsafe_chc_input),
        ("--self-check", &["--portfolio"][..], write_safe_chc_input),
    ] {
        let temp = tempfile::tempdir().expect("temporary directory");
        let input = write_input(temp.path());
        let certificate = block_default_chc_certificate(temp.path(), &input);

        let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
        command.args(["solve", "--no-verify-proof", "--stats-json", gate]);
        command.args(route_args);
        let output = command
            .arg(&input)
            .output()
            .expect("spawn AY with required CHC certificate gate");

        fs::set_permissions(temp.path(), fs::Permissions::from_mode(0o755))
            .expect("restore CHC directory permissions");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(
            output.status.success(),
            "{gate}: stdout={stdout}; stderr={stderr}"
        );
        assert!(
            stdout.lines().any(|line| line.trim() == "unknown"),
            "{gate} did not publish unknown: {stdout}"
        );
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat")),
            "{gate} leaked a definitive CHC verdict: {stdout}"
        );
        assert!(
            stderr.contains(gate)
                && stderr
                    .contains("required synthesized certificate generation/publication failed"),
            "missing required-certificate diagnostic: {stderr}"
        );
        assert!(
            stderr.contains("\"result\":\"unknown\"") || stderr.contains("\"result\": \"unknown\""),
            "gated stats did not record the public unknown result: {stderr}"
        );
        assert!(
            !stderr.contains("chc_proof_transcript") && !stderr.contains("chc_evidence_manifest"),
            "gated unknown leaked the hidden definitive proof result: {stderr}"
        );
        assert!(
            !certificate.is_file(),
            "failed required publication left a certificate file"
        );
    }
}

#[test]
#[timeout(30_000)]
fn chc_explicit_certificate_publication_failure_is_fatal() {
    for (route_args, write_input) in [
        (
            &[][..],
            write_safe_chc_input as fn(&std::path::Path) -> std::path::PathBuf,
        ),
        (
            &["--portfolio"][..],
            write_unsafe_chc_input as fn(&std::path::Path) -> std::path::PathBuf,
        ),
    ] {
        let temp = tempfile::tempdir().expect("temporary directory");
        let input = write_input(temp.path());
        let certificate = temp.path().join("requested.chccert");
        fs::create_dir(&certificate).expect("block explicit CHC certificate target");

        let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
        command.args(["solve", "--no-verify-proof", "--proof"]);
        command.arg(&certificate);
        command.args(route_args);
        let output = command
            .arg(&input)
            .output()
            .expect("spawn AY with explicit CHC certificate");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat" | "unknown")),
            "explicit certificate failure leaked a verdict: {stdout}"
        );
        assert!(
            stderr.contains("failed to publish explicitly requested CHC certificate"),
            "missing fatal explicit-certificate diagnostic: {stderr}"
        );
        assert!(certificate.is_dir(), "certificate target sentinel changed");
    }
}
