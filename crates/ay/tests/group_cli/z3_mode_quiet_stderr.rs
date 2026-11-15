// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Under `--z3-mode`, stderr stays as empty as z3's during a normal session.
//!
//! Verus starts its solver without redirecting stderr, and its test harness
//! fails a test on any stderr line that is not one of its JSON diagnostics
//! (`rust_verify_test/tests/common/mod.rs`). On the full upstream suite, 29
//! tests in which every answer equalled z3's failed on ay's stderr alone
//! (2026-09-28). Three kinds of line did it, none of which z3 prints: the
//! `(error ...)` of a check-sat ay has no decision procedure for, the
//! `c !! MODEL-UNCONFIRMED ...` line of a candidate model ay cannot confirm,
//! and the `[AY SOUNDNESS GATE]` banner of a model its gate refutes. Each
//! detail stays where a z3 client can ask for it: `(get-info :reason-unknown)`
//! or `(get-info :all-statistics)`. Each test also runs the same input without
//! `--z3-mode`, where the line is still printed, so an empty stderr here cannot
//! come from an input that never reaches it.

use super::z3_mode_failed_command::{DECLS, FAILING_QUERY};
use ntest::timeout;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

fn run_stdin(args: &[&str], input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay -in");
    child
        .stdin
        .as_mut()
        .expect("child stdin")
        .write_all(input.as_bytes())
        .expect("write SMT-LIB input");
    child.wait_with_output().expect("wait for ay -in")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

fn answers(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

/// The shared refused query (`z3_mode_failed_command::FAILING_QUERY`:
/// maximizing a String has no optimization order, so ay refuses the
/// `check-sat` with an execution error), then later queries that show
/// the session goes on.
fn refused_session() -> String {
    format!(
        "{DECLS}(push)\n{FAILING_QUERY}(get-info :reason-unknown)\n(pop)\n(push)\n\
         (assert false)\n(check-sat)\n(pop)\n(check-sat)\n"
    )
}

#[test]
#[timeout(120_000)]
fn a_refused_check_sat_writes_nothing_to_stderr() {
    let script = refused_session();
    let native = run_stdin(&["-q"], &script);
    assert!(
        text(&native.stderr).contains("(error \"unsupported optimization"),
        "the fixture must still be refused, or this test proves nothing: {}",
        text(&native.stderr)
    );

    // Without `-q`: `--z3-mode` alone is what a binary named `z3` gets.
    let output = run_stdin(&["--z3-mode"], &script);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert!(stderr.is_empty(), "stderr: {stderr}");
    assert_eq!(
        answers(&stdout),
        ["unknown", "unsat", "sat"],
        "stdout: {stdout}"
    );
    assert!(
        stdout.contains(
            "(:reason-unknown \"(incomplete decision-execution-error \"\"unsupported optimization"
        ),
        "the refusal is the reason of its unknown; stdout: {stdout}"
    );
    assert!(!stdout.contains("(error"), "stdout: {stdout}");
    assert_eq!(
        output.status.code(),
        Some(0),
        "z3 exits 1 only after printing an error, and none was printed; stdout: {stdout}"
    );
}

/// On this SMT-COMP file the first candidate model is rejected — by the
/// strict array oracle (`MODEL-UNCONFIRMED`) or, depending on the search
/// path the candidate took, by the soundness gate (`[AY SOUNDNESS GATE]`
/// on the array-skolem assertion) — and a re-solve publishes a validated
/// one, so the answer is `sat` while the rejected candidate is announced
/// on stderr in native mode and only in the statistics under `--z3-mode`.
#[test]
#[timeout(240_000)]
fn a_withheld_candidate_model_writes_nothing_to_stderr() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
        "../ay-dpll/tests/group_auflia/data/storecomm_invalid_t1_pp_sf_ni_00030_008.cvc.smt2",
    );
    let script =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let script = script.replace("(exit)", "");
    let input = format!("{script}\n(get-info :all-statistics)\n");

    let native = run_stdin(&["-q"], &input);
    let native_stderr = text(&native.stderr);
    let unconfirmed = native_stderr.contains("c !! MODEL-UNCONFIRMED");
    let gated = native_stderr.contains("[AY SOUNDNESS GATE]");
    assert!(
        unconfirmed || gated,
        "the fixture must still reach a rejection line, or this test proves \
         nothing: {native_stderr}"
    );

    let output = run_stdin(&["--z3-mode"], &input);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert!(stderr.is_empty(), "stderr: {stderr}");
    assert_eq!(answers(&stdout), ["sat"], "stdout: {stdout}");
    assert!(
        (unconfirmed && stdout.contains(":model-unconfirmed.last-detail"))
            || (gated && stdout.contains(":soundness-gate.last-invalid-model")),
        "the statistics carry what the line said; stdout: {stdout}"
    );
    assert_eq!(output.status.code(), Some(0), "stdout: {stdout}");
}

/// A quantified identity whose only instances come from a pattern ay does not
/// match here: the candidate model falsifies the `forall`, the gate catches it
/// and ay answers `unknown` (z3 also answers `unknown` under these options).
const GATE_REFUTED_MODEL: &str = r#"
(set-option :auto_config false)
(set-option :smt.mbqi false)
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun %I (Poly) Int)
(assert (forall ((x Int)) (! (= x (%I (I x))) :pattern ((I x)))))
(push)
(declare-const a Int)
(declare-const %%location_label%%0 Bool)
(assert (not (=> %%location_label%%0 (> (%I (I a)) 0))))
(check-sat)
(get-info :reason-unknown)
(get-info :all-statistics)
"#;

#[test]
#[timeout(120_000)]
fn a_caught_invalid_model_writes_nothing_to_stderr() {
    let native = run_stdin(&["-q"], GATE_REFUTED_MODEL);
    assert!(
        text(&native.stderr).contains("[AY SOUNDNESS GATE] caught an INVALID model"),
        "the fixture must still reach the banner, or this test proves nothing: {}",
        text(&native.stderr)
    );

    let output = run_stdin(&["--z3-mode"], GATE_REFUTED_MODEL);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert!(stderr.is_empty(), "stderr: {stderr}");
    assert_eq!(answers(&stdout), ["unknown"], "stdout: {stdout}");
    assert!(
        stdout.contains(":soundness-gate.invalid-models")
            && stdout.contains("(forall ((x_0 Int)) (= x_0 (%I (I x_0)))) falsified under model"),
        "the statistics carry what the banner said; stdout: {stdout}"
    );
    assert_eq!(output.status.code(), Some(0), "stdout: {stdout}");
}
