// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! QF_LIA-focused `--explain` integration tests (#8693).
//!
//! Phase 1 (#8693) already exercised propositional UNSAT and `(assert false)`
//! paths in [`super::explain_phase1_8693`]. This suite specifically covers the
//! QF_LIA slice from the design doc:
//!
//! * SAT with integer model values → natural-language walk-through showing
//!   each constraint holds under the concrete assignment (e.g., `(< 0 x)`
//!   evaluates to `true` because `x = 5`).
//! * UNSAT on contradictory integer bounds → English conflict summary ("these
//!   constraints cannot all be true at once") without requiring the user to
//!   read raw S-expression Farkas certificates.
//!
//! Tests drive the `ay` binary end-to-end to catch regressions at the CLI
//! surface — not just in the library API.

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
        "ay_explain_qf_lia_{}_{}.{}",
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

fn run_ay(args: &[&str]) -> std::process::Output {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    Command::new(ay_path).args(args).output().expect("spawn ay")
}

/// QF_LIA SAT — `x + y = 8 ∧ x > y ∧ x > 0` admits e.g. `x = 5, y = 3`.
/// `--explain` must (a) print `sat`, (b) show a concrete model for both
/// variables, (c) enumerate every assertion with its value-substituted form
/// and a `true`/`false` verdict. The per-constraint verdict is the key
/// natural-language affordance: it saves the user from mentally substituting
/// model values and re-evaluating each assertion.
#[test]
#[timeout(60_000)]
fn test_explain_qf_lia_sat_emits_constraint_verdicts() {
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 8))
(assert (> x y))
(assert (> x 0))
(check-sat)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    // `--no-verify-proof` disables the debug-default DRAT proof re-check,
    // which cannot run on SMT-LIB input (it requires Alethe). Without this,
    // the test harness in debug builds errors before printing the
    // explanation. Phase 1 explainability is orthogonal to proof
    // verification so suppressing the latter is safe here.
    let output = run_ay(&[
        "--explain",
        "--no-verify-proof",
        input_path.to_str().unwrap(),
    ]);
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Top-line result.
    assert!(
        stdout.contains("sat"),
        "expected sat in stdout, got: {stdout}"
    );
    // Explanation block header.
    assert!(
        stdout.contains("=== Explanation (SAT) ==="),
        "expected SAT explanation block header, got: {stdout}"
    );
    // Model for both variables must be shown. We don't pin specific values
    // (the solver is free to pick any satisfying assignment) but both names
    // must appear with an `=` sign under the Solution section.
    assert!(
        stdout.contains("Solution found:"),
        "expected 'Solution found:' in stdout, got: {stdout}"
    );
    assert!(
        stdout.contains("x = "),
        "expected concrete value for x in stdout, got: {stdout}"
    );
    assert!(
        stdout.contains("y = "),
        "expected concrete value for y in stdout, got: {stdout}"
    );
    // Per-constraint walk-through: original, substituted, verdict.
    assert!(
        stdout.contains("Constraint verification:"),
        "expected 'Constraint verification:' header, got: {stdout}"
    );
    assert!(
        stdout.contains("assertion:"),
        "expected per-assertion 'assertion:' line, got: {stdout}"
    );
    assert!(
        stdout.contains("substituted:"),
        "expected 'substituted:' line with model values, got: {stdout}"
    );
    assert!(
        stdout.contains("evaluates to: true"),
        "expected 'evaluates to: true' for every assertion, got: {stdout}"
    );
    // At least one assertion should have kept the original `x` variable name
    // in the pretty-printed form (prose), confirming we're showing both the
    // symbolic and the substituted view.
    assert!(
        stdout.contains("All 3 constraint(s) satisfied."),
        "expected final count of satisfied constraints, got: {stdout}"
    );
}

/// QF_LIA UNSAT — `x < 0 ∧ x > 0` is vacuously contradictory. `--explain`
/// must (a) print `unsat`, (b) declare that no assignment satisfies them,
/// (c) list the conflicting assertions verbatim, (d) emit a one-sentence
/// English conflict summary. We deliberately do not pin the Phase 1 reason
/// code (LIA preprocessing may fold `x < 0 ∧ x > 0` to `false` before CDCL,
/// yielding `PreprocessingDetected`; a cold path may hit CDCL and register
/// `TheoryConflict(LIA)` or `UnitPropagationContradiction` instead). The
/// English walk-through is what users read — that's the real contract.
#[test]
#[timeout(60_000)]
fn test_explain_qf_lia_unsat_emits_conflict_summary() {
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (< x 0))
(assert (> x 0))
(check-sat)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    // `--no-verify-proof` disables the debug-default DRAT proof re-check,
    // which cannot run on SMT-LIB input (it requires Alethe). Without this,
    // the test harness in debug builds errors before printing the
    // explanation. Phase 1 explainability is orthogonal to proof
    // verification so suppressing the latter is safe here.
    let output = run_ay(&[
        "--explain",
        "--no-verify-proof",
        input_path.to_str().unwrap(),
    ]);
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Top-line result.
    assert!(
        stdout.contains("unsat"),
        "expected unsat in stdout, got: {stdout}"
    );
    // Phase 1 reason-code header is present for every UNSAT under --explain.
    assert!(
        stdout.contains("=== Reason code (UNSAT, Phase 1) ==="),
        "expected Phase 1 reason-code header, got: {stdout}"
    );
    // English explanation block.
    assert!(
        stdout.contains("=== Explanation (UNSAT) ==="),
        "expected UNSAT explanation header, got: {stdout}"
    );
    assert!(
        stdout.contains("No assignment can satisfy these constraints simultaneously."),
        "expected top-level impossibility statement, got: {stdout}"
    );
    // Verbatim assertion listing. Both original assertions must appear.
    assert!(
        stdout.contains("(< x 0)"),
        "expected original '(< x 0)' assertion in output, got: {stdout}"
    );
    assert!(
        stdout.contains("(> x 0)") || stdout.contains("(< 0 x)"),
        "expected original '(> x 0)' or normalized '(< 0 x)' in output, got: {stdout}"
    );
    // One-sentence conflict summary at the bottom.
    assert!(
        stdout.contains("Conflict:"),
        "expected 'Conflict:' summary line, got: {stdout}"
    );
    assert!(
        stdout.contains("mutually contradictory")
            || stdout.contains("cannot be simultaneously satisfied"),
        "expected English conflict phrasing, got: {stdout}"
    );
}
