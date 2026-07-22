// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed transcript results must retire every artifact from a preceding
//! raw solver result.

use std::io::Write;
use std::process::{Command, Stdio};

use tempfile::TempDir;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

#[test]
fn incomplete_check_retires_stale_queries_explanation_and_decision_trace() {
    let temp = TempDir::new().expect("temporary directory");
    let trace = temp.path().join("decision.trace");
    let input = r#"
(set-logic QF_UF)
(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)
(push 1)
(declare-const a Bool)
(declare-const b Bool)
(assert (! (or a b) :named disjunction))
(assert (! (not a) :named not-a))
(assert (! (not b) :named not-b))
(check-sat)
(assert missing-symbol)
(check-sat)
(get-proof)
(get-unsat-core)
(get-model)
(get-info :reason-unknown)
"#;

    let mut child = Command::new(ay_binary())
        .args(["solve", "--stdin", "--explain", "--decision-trace"])
        .arg(&trace)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(input.as_bytes())
        .expect("write transcript");
    let output = child.wait_with_output().expect("wait for ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stdout.contains("unsat"),
        "missing first raw result: {stdout}"
    );
    assert!(
        stdout.contains("unknown"),
        "missing fail-closed result: {stdout}"
    );
    for unavailable in [
        "proof is not available, last result was unknown",
        "unsat core is not available, last result was not unsat",
        "model is not available",
    ] {
        assert!(
            stdout.contains(unavailable),
            "stale proof/core/model query was not retired: {stdout}"
        );
    }
    assert!(
        stdout.contains("=== Explanation (UNKNOWN) ==="),
        "EOF explanation used a stale result: {stdout}"
    );
    assert!(
        !stdout.contains("=== Explanation (UNSAT) ==="),
        "stale UNSAT explanation leaked: {stdout}"
    );
    assert!(
        stdout.contains("a problem-contributing command was discarded"),
        "public reason-unknown was not preserved: {stdout}; stderr={stderr}"
    );
    assert!(
        trace.exists(),
        "same-run trace reservation should remain visible"
    );
    assert_eq!(
        std::fs::metadata(&trace)
            .expect("invalidated trace metadata")
            .len(),
        0,
        "a raw trace with a mismatched public result must be non-replayable"
    );
}

#[test]
fn unrepresentable_definition_overloads_fail_closed() {
    for input in [
        "(define-fun g () Int 1)\n(define-fun g ((x Int)) Int 2)\n(assert (= (g) 2))\n(check-sat)\n",
        "(declare-const g Int)\n(define-fun g () Bool true)\n(assert (= g 0))\n(check-sat)\n",
        "(declare-const g Int)\n(define-fun-rec g () Bool true)\n(assert (= g 0))\n(check-sat)\n",
    ] {
        let mut child = Command::new(ay_binary())
            .args(["solve", "--stdin"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn ay");
        child
            .stdin
            .take()
            .expect("piped stdin")
            .write_all(input.as_bytes())
            .expect("write transcript");
        let output = child.wait_with_output().expect("wait for ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stdout.lines().any(|line| line.trim() == "unknown"),
            "unrepresented overload must fail closed: stdout={stdout}; stderr={stderr}"
        );
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat")),
            "unrepresented overload emitted a definitive verdict: {stdout}"
        );
    }
}

#[test]
fn piped_execution_failure_exits_nonzero_without_a_verdict() {
    let temp = TempDir::new().expect("temporary directory");
    let invalid_trace_target = temp.path().join("trace-is-a-directory");
    std::fs::create_dir(&invalid_trace_target).expect("create invalid trace target");

    let mut child = Command::new(ay_binary())
        .args(["solve", "--stdin", "--decision-trace"])
        .arg(&invalid_trace_target)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(b"(assert missing-symbol)\n(check-sat)\n")
        .expect("write transcript");
    let output = child.wait_with_output().expect("wait for ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        !stdout
            .lines()
            .any(|line| matches!(line.trim(), "sat" | "unsat" | "unknown")),
        "failed artifact invalidation must not be followed by a verdict: {stdout}"
    );
    assert!(
        stderr.contains("could not be invalidated"),
        "missing failure diagnostic: {stderr}"
    );
}

#[test]
fn required_smt_proof_failure_precedes_verdict_stats_and_trace() {
    let temp = TempDir::new().expect("temporary directory");
    let proof = temp.path().join("missing-parent").join("proof.alethe");
    let trace = temp.path().join("decision.trace");
    let mut child = Command::new(ay_binary())
        .arg("--proof")
        .arg(&proof)
        .arg("--no-verify-proof")
        .arg("--stats-json")
        .arg("--decision-trace")
        .arg(&trace)
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
        .write_all(b"(set-logic QF_UF)\n(assert false)\n(check-sat)\n")
        .expect("write transcript");
    let output = child.wait_with_output().expect("wait for ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        !stdout
            .lines()
            .any(|line| matches!(line.trim(), "sat" | "unsat")),
        "required proof failure leaked a definitive verdict: {stdout}"
    );
    assert!(
        !stderr.contains("\"result\":\"unsat\""),
        "required proof failure leaked UNSAT statistics: {stderr}"
    );
    assert!(
        trace.exists(),
        "same-run trace reservation should remain visible"
    );
    assert_eq!(
        std::fs::metadata(&trace)
            .expect("invalidated trace metadata")
            .len(),
        0,
        "required proof failure left an authoritative decision trace"
    );
    assert!(
        stderr.contains("required UNSAT publication failed"),
        "missing publication diagnostic: {stderr}"
    );
}

#[test]
fn solve_output_aliases_are_rejected_before_input_mutation() {
    for output_flag in ["--proof", "--progress-json"] {
        let temp = TempDir::new().expect("temporary directory");
        let input = temp.path().join("input.smt2");
        let original = b"(set-logic QF_UF)\n(assert false)\n(check-sat)\n";
        std::fs::write(&input, original).expect("write input");

        let output = Command::new(ay_binary())
            .arg("--no-verify-proof")
            .arg(output_flag)
            .arg(&input)
            .arg(&input)
            .output()
            .expect("spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        assert_eq!(
            std::fs::read(&input).expect("read preserved input"),
            original,
            "{output_flag} mutated its aliased input"
        );
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat")),
            "alias failure leaked a verdict: {stdout}"
        );
        assert!(stderr.contains("aliases the input path"), "{stderr}");
    }
}

#[test]
fn runtime_smt_output_channel_cannot_replace_its_file_input() {
    let temp = TempDir::new().expect("temporary directory");
    let input = temp.path().join("self-channel.smt2");
    let original = format!(
        "(set-option :regular-output-channel \"{}\")\n(echo \"must stay on stdout\")\n",
        input.display()
    );
    std::fs::write(&input, &original).expect("write SMT input");

    let output = Command::new(ay_binary())
        .args(["solve", "--no-proof", "--no-verify-proof"])
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(stdout.contains("aliases another transcript channel or a solver artifact"));
    assert_eq!(
        std::fs::read_to_string(&input).expect("read preserved input"),
        original,
        "runtime regular-output-channel replaced its own input"
    );
}

#[cfg(unix)]
#[test]
fn runtime_smt_output_channel_cannot_replace_a_hardlink_to_its_input() {
    let temp = TempDir::new().expect("temporary directory");
    let input = temp.path().join("hardlink-channel.smt2");
    let alias = temp.path().join("channel.log");
    let original = format!(
        "(set-option :diagnostic-output-channel \"{}\")\n(get-info :unsupported-info)\n",
        alias.display()
    );
    std::fs::write(&input, &original).expect("write SMT input");
    std::fs::hard_link(&input, &alias).expect("hard-link channel to input");

    let output = Command::new(ay_binary())
        .args(["solve", "--no-proof", "--no-verify-proof"])
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(stdout.contains("aliases another transcript channel or a solver artifact"));
    assert_eq!(
        std::fs::read_to_string(&input).expect("read preserved input"),
        original
    );
    assert_eq!(
        std::fs::read_to_string(&alias).expect("read preserved hardlink"),
        original
    );
}

#[test]
fn solve_output_directory_cannot_enclose_the_input() {
    let temp = TempDir::new().expect("temporary directory");
    let input = temp.path().join("input.smt2");
    let original = b"(set-logic QF_UF)\n(assert false)\n(check-sat)\n";
    std::fs::write(&input, original).expect("write input");

    let output = Command::new(ay_binary())
        .arg("--emit-firewall-lean")
        .arg(temp.path())
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert_eq!(
        std::fs::read(&input).expect("read preserved input"),
        original,
        "output-directory setup mutated its enclosed input"
    );
    assert!(stdout.trim().is_empty(), "unexpected verdict: {stdout}");
    assert!(
        stderr.contains("firewall Lean output directory")
            && stderr.contains("overlaps the input path"),
        "missing directory/input alias diagnostic: {stderr}"
    );
}

#[test]
fn default_chc_certificate_alias_is_rejected_before_progress_creation() {
    let temp = TempDir::new().expect("temporary directory");
    let input = temp.path().join("input.smt2");
    let certificate = temp.path().join("input.smt2.chccert");
    std::fs::write(&input, "(set-logic HORN)\n(assert false)\n(check-sat)\n").expect("write input");

    let output = Command::new(ay_binary())
        .arg("--progress-json")
        .arg(&certificate)
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        stdout
            .lines()
            .all(|line| !matches!(line.trim(), "sat" | "unsat" | "unknown")),
        "certificate alias failure leaked a verdict: {stdout}"
    );
    assert!(
        stderr.contains("progress JSON") && stderr.contains("default CHC certificate"),
        "missing CHC alias diagnostic: {stderr}"
    );
    assert!(
        !certificate.exists(),
        "progress output was created before the CHC certificate alias check"
    );
}

#[test]
fn smt_rejects_binary_alethe_before_emitting_mislabeled_artifacts() {
    let temp = TempDir::new().expect("temporary directory");
    let input = temp.path().join("input.smt2");
    let proof = temp.path().join("proof.alethe");
    let artifact = temp.path().join("artifact.json");
    std::fs::write(&input, "(set-logic QF_UF)\n(assert false)\n(check-sat)\n")
        .expect("write input");
    let output = Command::new(ay_binary())
        .arg("--no-verify-proof")
        .arg("--proof")
        .arg(&proof)
        .arg("--proof-binary")
        .arg("--proof-artifact")
        .arg(&artifact)
        .arg(&input)
        .output()
        .expect("spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(stdout.trim().is_empty(), "unexpected output: {stdout}");
    assert!(
        stderr.contains("--proof-binary is unsupported for SMT-LIB Alethe"),
        "stderr={stderr}"
    );
    assert!(!proof.exists());
    assert!(!artifact.exists());
}

fn run_piped_with_artifacts(
    input: &str,
    proof: &std::path::Path,
    artifact: &std::path::Path,
) -> std::process::Output {
    let mut child = Command::new(ay_binary())
        .arg("--proof")
        .arg(proof)
        .arg("--proof-artifact")
        .arg(artifact)
        .arg("--no-verify-proof")
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
        .write_all(input.as_bytes())
        .expect("write transcript");
    child.wait_with_output().expect("wait for ay")
}

#[test]
fn malformed_post_decision_eof_keeps_only_the_prior_authorized_proof_epoch() {
    for remainder in ["(assert (", "(get-model"] {
        let temp = TempDir::new().expect("temporary directory");
        let proof = temp.path().join("proof.alethe");
        let artifact = temp.path().join("proof-artifact.json");
        let input = format!("(assert false)\n(check-sat)\n{remainder}");
        let output = run_piped_with_artifacts(&input, &proof, &artifact);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        assert!(stdout.contains("unsat"), "first result missing: {stdout}");
        assert!(
            stdout.contains("(error"),
            "EOF remainder was ignored: {stdout}"
        );
        assert!(proof.exists(), "authorized proof missing for {remainder}");
        let envelope: serde_json::Value = serde_json::from_slice(
            &std::fs::read(&artifact).expect("authorized proof artifact exists"),
        )
        .expect("valid proof artifact JSON");
        let problem = envelope["certificate"]["payload"]["problem"]
            .as_str()
            .expect("embedded problem text");
        assert!(problem.contains("(check-sat)"), "payload={problem}");
        assert!(
            !problem.contains(remainder),
            "authorized proof absorbed a later malformed command: {problem}"
        );
    }
}

#[test]
fn reset_starts_a_fresh_proof_artifact_source_epoch() {
    let temp = TempDir::new().expect("temporary directory");
    let proof = temp.path().join("proof.alethe");
    let artifact = temp.path().join("proof-artifact.json");
    let rejected = "pre_reset_missing_symbol";
    let input =
        format!("(assert {rejected})\n(reset)\n(set-logic QF_UF)\n(assert false)\n(check-sat)\n");
    let output = run_piped_with_artifacts(&input, &proof, &artifact);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(proof.exists(), "fresh-epoch proof missing: {stderr}");
    let envelope: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&artifact).expect("fresh-epoch artifact exists"))
            .expect("valid proof artifact JSON");
    let problem = envelope["certificate"]["payload"]["problem"]
        .as_str()
        .expect("embedded problem text");
    assert!(
        !problem.contains(rejected),
        "payload leaked rejected epoch: {problem}"
    );
    assert!(
        !problem.contains("(reset)"),
        "payload leaked reset boundary: {problem}"
    );
    assert!(problem.contains("(assert false)"), "payload={problem}");
}

#[test]
fn balanced_multi_command_parse_failure_taints_every_dropped_head() {
    let input = "(get-info :version) (include \"unsat.smt2\")\n(check-sat)\n";
    let mut child = Command::new(ay_binary())
        .args(["solve", "--stdin"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let output = child.wait_with_output().expect("wait for ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.lines().any(|line| line.trim() == "unknown"),
        "later dropped include was not tainted: stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !stdout.lines().any(|line| line.trim() == "sat"),
        "incomplete problem produced SAT: {stdout}"
    );
}

#[test]
fn piped_horn_after_leading_smt_comment_keeps_fixedpoint_polarity() {
    let input = "; leading SMT-LIB comment\n\
        (set-logic HORN)\n\
        (declare-rel Inv (Int))\n\
        (declare-var x Int)\n\
        (rule (Inv 0))\n\
        (rule (=> (and (Inv x) (< x 2)) (Inv (+ x 1))))\n\
        (query (and (Inv x) (> x 5)))\n";
    let mut child = Command::new(ay_binary())
        .arg("--stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let output = child.wait_with_output().expect("wait for ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "SAFE fixedpoint query must retain CHC's inverted polarity: {stdout}"
    );
}

#[cfg(unix)]
#[test]
fn smt_output_channel_replaces_symlink_without_touching_referent() {
    use std::os::unix::fs::symlink;

    let temp = TempDir::new().expect("temporary directory");
    let victim = temp.path().join("victim.txt");
    let channel = temp.path().join("regular.log");
    std::fs::write(&victim, "protected").unwrap();
    symlink(&victim, &channel).unwrap();
    let input = format!(
        "(set-option :regular-output-channel \"{}\")\n(echo \"hello\")\n",
        channel.display()
    );
    let mut child = Command::new(ay_binary())
        .args(["solve", "--stdin"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(std::fs::read_to_string(victim).unwrap(), "protected");
    assert_eq!(std::fs::read_to_string(channel).unwrap(), "hello\n");
}
