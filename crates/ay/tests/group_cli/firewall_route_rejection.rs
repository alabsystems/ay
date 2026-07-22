// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Firewall verification and Lean emission are SMT DPLL(T)-only result gates.
//! Unsupported route selection must fail before solving instead of silently
//! publishing an unchecked DIMACS/CHC/fixedpoint verdict or artifact.

use std::io::Write;
use std::process::{Command, Output, Stdio};

use tempfile::TempDir;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn assert_rejected(output: &Output, route: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "{route} must reject --verify-firewall; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.trim().is_empty(),
        "{route} must not emit a verdict before rejection; stdout={stdout}"
    );
    assert!(
        stderr.contains("--verify-firewall supports only the SMT-LIB DPLL(T) route"),
        "{route} missing qualified rejection; stderr={stderr}"
    );
    assert!(
        stderr.contains(route),
        "{route} rejection must identify the selected route; stderr={stderr}"
    );
}

fn assert_emission_rejected(output: &Output, route: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "{route} must reject --emit-firewall-lean; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.trim().is_empty(),
        "{route} must not emit a verdict before rejection; stdout={stdout}"
    );
    assert!(
        stderr.contains("--emit-firewall-lean supports only the SMT-LIB DPLL(T) route"),
        "{route} missing qualified emission rejection; stderr={stderr}"
    );
    assert!(
        stderr.contains(route),
        "{route} rejection must identify the selected route; stderr={stderr}"
    );
}

#[test]
fn firewall_gate_rejects_all_auto_detected_file_routes() {
    let temp = TempDir::new().expect("tempdir");
    for (name, content, route) in [
        ("input.cnf", "p cnf 1 2\n1 0\n-1 0\n", "DIMACS file"),
        (
            "horn.smt2",
            "(set-logic HORN)\n(assert false)\n(check-sat)\n",
            "CHC file",
        ),
        (
            "fixedpoint.smt2",
            "(declare-rel bad ())\n(rule bad)\n(query bad)\n",
            "fixedpoint file",
        ),
    ] {
        let path = temp.path().join(name);
        std::fs::write(&path, content).expect("write route input");
        let output = Command::new(ay_binary())
            .args(["solve", "--verify-firewall"])
            .arg(&path)
            .output()
            .expect("spawn ay");
        assert_rejected(&output, route);
    }
}

#[test]
fn firewall_gate_rejects_forced_chc_portfolio_before_solving() {
    let temp = TempDir::new().expect("tempdir");
    let path = temp.path().join("ordinary.smt2");
    std::fs::write(&path, "(set-logic QF_LIA)\n(check-sat)\n").expect("write input");

    for flag in ["--chc", "--portfolio"] {
        let output = Command::new(ay_binary())
            .args(["solve", "--verify-firewall", flag])
            .arg(&path)
            .output()
            .expect("spawn ay");
        assert_rejected(&output, "forced CHC/portfolio");
    }
}

#[test]
fn explicit_proof_verification_rejects_forced_chc_portfolio_before_solving() {
    let temp = TempDir::new().expect("tempdir");
    let path = temp.path().join("ordinary.smt2");
    std::fs::write(&path, "(set-logic QF_LIA)\n(check-sat)\n").expect("write input");

    for flag in ["--chc", "--portfolio"] {
        let output = Command::new(ay_binary())
            .args(["solve", "--verify-proof", flag])
            .arg(&path)
            .output()
            .expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{flag} must reject; stderr={stderr}"
        );
        assert!(
            stdout.trim().is_empty(),
            "must not emit a verdict: {stdout}"
        );
        assert!(
            stderr.contains(
                "--verify-proof cannot verify forced CHC/portfolio CHC replay certificates"
            ),
            "missing forced-route rejection; stderr={stderr}"
        );
    }
}

#[test]
fn firewall_gate_rejects_all_auto_detected_stdin_routes() {
    for (content, route) in [
        ("p cnf 1 2\n1 0\n-1 0\n", "DIMACS stdin"),
        (
            "(set-logic HORN)\n(assert false)\n(check-sat)\n",
            "CHC stdin",
        ),
        (
            "(declare-rel bad ())\n(rule bad)\n(query bad)\n",
            "fixedpoint stdin",
        ),
    ] {
        let mut child = Command::new(ay_binary())
            .args(["solve", "--verify-firewall", "--stdin"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn ay");
        child
            .stdin
            .take()
            .expect("piped stdin")
            .write_all(content.as_bytes())
            .expect("write stdin");
        let output = child.wait_with_output().expect("wait for ay");
        assert_rejected(&output, route);
    }
}

#[test]
fn firewall_emission_rejects_all_auto_detected_file_routes() {
    let temp = TempDir::new().expect("tempdir");
    let out_dir = temp.path().join("firewall");
    let proof = temp.path().join("proof.alethe");
    for (name, content, route) in [
        ("input.cnf", "p cnf 1 2\n1 0\n-1 0\n", "DIMACS file"),
        (
            "horn.smt2",
            "(set-logic HORN)\n(assert false)\n(check-sat)\n",
            "CHC file",
        ),
        (
            "fixedpoint.smt2",
            "(declare-rel bad ())\n(rule bad)\n(query bad)\n",
            "fixedpoint file",
        ),
    ] {
        let path = temp.path().join(name);
        std::fs::write(&path, content).expect("write route input");
        let output = Command::new(ay_binary())
            .args(["solve", "--emit-firewall-lean"])
            .arg(&out_dir)
            .arg("--proof")
            .arg(&proof)
            .arg(&path)
            .output()
            .expect("spawn ay");
        assert_emission_rejected(&output, route);
    }
}

#[test]
fn firewall_emission_rejects_all_auto_detected_stdin_routes() {
    let temp = TempDir::new().expect("tempdir");
    let out_dir = temp.path().join("firewall");
    let proof = temp.path().join("proof.alethe");
    for (content, route) in [
        ("p cnf 1 2\n1 0\n-1 0\n", "DIMACS stdin"),
        (
            "(set-logic HORN)\n(assert false)\n(check-sat)\n",
            "CHC stdin",
        ),
        (
            "(declare-rel bad ())\n(rule bad)\n(query bad)\n",
            "fixedpoint stdin",
        ),
    ] {
        let mut child = Command::new(ay_binary())
            .args(["solve", "--emit-firewall-lean"])
            .arg(&out_dir)
            .arg("--proof")
            .arg(&proof)
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn ay");
        child
            .stdin
            .take()
            .expect("piped stdin")
            .write_all(content.as_bytes())
            .expect("write stdin");
        let output = child.wait_with_output().expect("wait for ay");
        assert_emission_rejected(&output, route);
    }
}

#[test]
fn firewall_emission_rejects_forced_chc_portfolio_before_solving() {
    let temp = TempDir::new().expect("tempdir");
    let path = temp.path().join("ordinary.smt2");
    let out_dir = temp.path().join("firewall");
    let proof = temp.path().join("proof.alethe");
    std::fs::write(&path, "(set-logic QF_LIA)\n(check-sat)\n").expect("write input");

    for flag in ["--chc", "--portfolio"] {
        let output = Command::new(ay_binary())
            .args(["solve", "--emit-firewall-lean"])
            .arg(&out_dir)
            .arg("--proof")
            .arg(&proof)
            .arg(flag)
            .arg(&path)
            .output()
            .expect("spawn ay");
        assert_emission_rejected(&output, "forced CHC/portfolio");
    }
}

#[test]
fn firewall_emission_requires_persistent_alethe_proof_configuration() {
    let temp = TempDir::new().expect("tempdir");
    let path = temp.path().join("ordinary.smt2");
    let out_dir = temp.path().join("firewall");
    std::fs::write(&path, "(set-logic QF_LIA)\n(check-sat)\n").expect("write input");

    for suppression in ["--no-proof", "--z3-mode", "--competition"] {
        let output = Command::new(ay_binary())
            .args(["solve", "--emit-firewall-lean"])
            .arg(&out_dir)
            .arg(suppression)
            .arg(&path)
            .output()
            .expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "{suppression}: {stderr}");
        assert!(stdout.trim().is_empty(), "{suppression}: {stdout}");
        assert!(
            stderr.contains("--emit-firewall-lean requires a persistent Alethe proof"),
            "{suppression}: {stderr}"
        );
    }

    let proof = temp.path().join("proof.drat");
    let output = Command::new(ay_binary())
        .args(["solve", "--emit-firewall-lean"])
        .arg(&out_dir)
        .arg("--proof")
        .arg(&proof)
        .args(["--proof-format", "drat"])
        .arg(&path)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "non-Alethe proof: {stderr}");
    assert!(stdout.trim().is_empty(), "non-Alethe proof: {stdout}");
    assert!(
        stderr.contains("--emit-firewall-lean requires an Alethe proof"),
        "non-Alethe proof: {stderr}"
    );
}

#[test]
fn firewall_emission_io_failure_is_fatal_and_preserves_the_target() {
    let temp = TempDir::new().expect("tempdir");
    let path = temp.path().join("unsat.smt2");
    let output_path = temp.path().join("not-a-directory");
    let proof = temp.path().join("proof.alethe");
    std::fs::write(
        &path,
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (<= x 1))\n(assert (>= x 2))\n(check-sat)\n",
    )
    .expect("write input");
    std::fs::write(&output_path, "preserve me").expect("write output sentinel");

    let output = Command::new(ay_binary())
        .args(["solve", "--emit-firewall-lean"])
        .arg(&output_path)
        .arg("--proof")
        .arg(&proof)
        .arg(&path)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        !stdout.lines().any(|line| line.trim() == "unsat"),
        "failed required emission leaked UNSAT: {stdout}"
    );
    assert!(
        stderr.contains("failed to publish firewall Lean artifacts"),
        "missing fatal emission error: {stderr}"
    );
    assert_eq!(
        std::fs::read_to_string(&output_path).expect("read sentinel"),
        "preserve me"
    );
    assert_eq!(
        std::fs::read(&proof).expect("read invalidated proof publication"),
        b"",
        "a downstream firewall failure must invalidate the exact proof inode"
    );
}

#[test]
fn firewall_emission_makes_default_proof_publication_failure_fatal() {
    let temp = TempDir::new().expect("tempdir");
    let path = temp.path().join("unsat.smt2");
    let output_dir = temp.path().join("firewall");
    let default_proof = temp.path().join("unsat.smt2.alethe");
    std::fs::write(
        &path,
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (<= x 1))\n(assert (>= x 2))\n(check-sat)\n",
    )
    .expect("write input");
    std::fs::create_dir(&default_proof).expect("block the default proof file target");

    let output = Command::new(ay_binary())
        .args(["solve", "--emit-firewall-lean"])
        .arg(&output_dir)
        .arg(&path)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        !stdout.lines().any(|line| line.trim() == "unsat"),
        "failed required proof leaked UNSAT: {stdout}"
    );
    assert!(
        stderr.contains("required UNSAT publication failed"),
        "missing required-proof failure: {stderr}"
    );
    assert!(
        !output_dir.exists(),
        "firewall files must not precede their required proof"
    );
    assert!(default_proof.is_dir(), "proof target sentinel must survive");
}

#[test]
fn chc_rejects_unsupported_proof_envelope_and_binary_requests_before_verdict() {
    let temp = TempDir::new().expect("tempdir");
    let input = temp.path().join("horn.smt2");
    std::fs::write(
        &input,
        "(set-logic HORN)\n(declare-fun Inv (Int) Bool)\n(assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))\n(check-sat)\n",
    )
    .expect("write CHC input");

    for (extra_flag, expected) in [
        (
            "--proof-artifact",
            "--proof-artifact is unsupported for CHC certificates",
        ),
        (
            "--proof-binary",
            "--proof-binary is unsupported for CHC text certificates",
        ),
    ] {
        let proof = temp.path().join(format!("{extra_flag}.chccert"));
        let artifact = temp.path().join(format!("{extra_flag}.json"));
        let mut command = Command::new(ay_binary());
        command
            .args(["solve", "--chc", "--no-verify-proof", "--proof"])
            .arg(&proof)
            .arg(extra_flag);
        if extra_flag == "--proof-artifact" {
            command.arg(&artifact);
        }
        let output = command.arg(&input).output().expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat")),
            "unsupported CHC proof request leaked a verdict: {stdout}"
        );
        assert!(stderr.contains(expected), "stderr={stderr}");
        assert!(!proof.exists(), "unsupported request wrote a certificate");
        assert!(!artifact.exists(), "unsupported request wrote an envelope");
    }
}

#[test]
fn chc_required_certificate_gates_reject_suppressed_proof_output() {
    let temp = TempDir::new().expect("tempdir");
    let input = temp.path().join("horn.smt2");
    std::fs::write(
        &input,
        "(set-logic HORN)\n(declare-fun Inv (Int) Bool)\n(assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))\n(check-sat)\n",
    )
    .expect("write CHC input");

    for gate in ["--strict-proofs", "--self-check"] {
        for suppression in ["--no-proof", "--z3-mode", "--competition"] {
            let output = Command::new(ay_binary())
                .args(["solve", "--chc", "--no-verify-proof", gate, suppression])
                .arg(&input)
                .output()
                .expect("spawn ay");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                !output.status.success(),
                "{gate} {suppression}: stdout={stdout}; stderr={stderr}"
            );
            assert!(
                stdout
                    .lines()
                    .all(|line| !matches!(line.trim(), "sat" | "unsat" | "unknown")),
                "{gate} {suppression} leaked a verdict: {stdout}"
            );
            assert!(
                stderr.contains("requires a persistent native CHC certificate"),
                "{gate} {suppression}: stderr={stderr}"
            );
        }
    }
}

#[test]
fn chc_rejects_incompatible_explicit_proof_formats_before_parsing() {
    let temp = TempDir::new().expect("tempdir");
    let input = temp.path().join("malformed-horn.smt2");
    std::fs::write(&input, "(set-logic HORN)\n(assert\n").expect("write malformed CHC input");

    for (name, extension, forced_format, expected) in [
        (
            "inferred-drat",
            "drat",
            None,
            "CHC proof output uses the native ay-chc-cert text format",
        ),
        (
            "inferred-alethe",
            "alethe",
            None,
            "CHC proof output uses the native ay-chc-cert text format",
        ),
        (
            "forced-lrat",
            "chccert",
            Some("lrat"),
            "--proof-format and legacy DIMACS proof flags are incompatible with CHC certificates",
        ),
        (
            "forced-alethe",
            "chccert",
            Some("alethe"),
            "--proof-format and legacy DIMACS proof flags are incompatible with CHC certificates",
        ),
    ] {
        let proof = temp.path().join(format!("{name}.{extension}"));
        let mut command = Command::new(ay_binary());
        command
            .args(["solve", "--chc", "--no-verify-proof", "--proof"])
            .arg(&proof);
        if let Some(format) = forced_format {
            command.args(["--proof-format", format]);
        }
        let output = command.arg(&input).output().expect("spawn AY");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(
            !output.status.success(),
            "{name}: stdout={stdout}; stderr={stderr}"
        );
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat" | "unknown")),
            "{name}: incompatible format leaked a verdict: {stdout}"
        );
        assert!(stderr.contains(expected), "{name}: stderr={stderr}");
        assert!(
            !stderr.contains("parse error"),
            "{name}: CHC parsing preceded proof-format rejection: {stderr}"
        );
        assert!(
            !proof.exists(),
            "{name}: incompatible request created a proof"
        );
    }
}

#[test]
fn chc_accepts_explicit_native_certificate_request() {
    let temp = TempDir::new().expect("tempdir");
    let input = temp.path().join("horn.smt2");
    let proof = temp.path().join("proof.chccert");
    std::fs::write(
        &input,
        "(set-logic HORN)\n(declare-fun Inv (Int) Bool)\n(assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))\n(check-sat)\n",
    )
    .expect("write CHC input");

    let output = Command::new(ay_binary())
        .args(["solve", "--chc", "--no-verify-proof", "--proof"])
        .arg(&proof)
        .arg(&input)
        .output()
        .expect("spawn AY");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        stdout
            .lines()
            .any(|line| matches!(line.trim(), "sat" | "unsat")),
        "native certificate request produced no definitive verdict: {stdout}"
    );
    let certificate = std::fs::read_to_string(&proof).expect("native CHC certificate");
    assert!(
        certificate.contains("AY CHC Certificate"),
        "unexpected certificate contents: {certificate}"
    );
    assert!(
        !stderr.contains("unknown proof extension"),
        ".chccert must be recognized without a misleading warning: {stderr}"
    );
}
