// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Packet 1 helper surface for the SMT soundness gate.
//!
//! These helpers compose `ay_frontend::parse`, `Executor`, `validate_model()`,
//! and `ay_proof::check_proof` into reusable assertion patterns.

use std::{fs, path::Path};

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::check_proof;

/// Proof expectation level for UNSAT tests.
pub(crate) enum ProofExpectation {
    /// Run `check_proof()` on the internal proof object.
    InternalChecked,
    /// Require non-empty proof text and a populated proof object,
    /// but do not run the internal checker (for BV/AX where theory
    /// proof completeness is not yet Packet 1 scope).
    TextOnly,
}

/// Parse and execute an SMT-LIB script, returning the executor and raw outputs.
pub(crate) fn execute_script(smt: &str) -> (Executor, Vec<String>) {
    let commands =
        parse(smt).unwrap_or_else(|err| panic!("soundness gate: parse failed: {err}\n{smt}"));
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("soundness gate: execution failed: {err}\n{smt}"));
    (exec, outputs)
}

fn load_workspace_script(relative_path: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative_path);
    fs::read_to_string(&path).unwrap_or_else(|err| {
        panic!(
            "soundness gate: failed to read benchmark file {}: {err}",
            path.display()
        )
    })
}

/// Assert that an SMT script returns SAT and the model validates.
///
/// Calls `validate_model()` and asserts `checked > 0`.
pub(crate) fn assert_sat_validates(smt: &str) {
    let (exec, outputs) = execute_script(smt);
    let first = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| panic!("soundness gate: no sat/unsat/unknown in output: {outputs:?}"));
    assert_eq!(
        first.trim(),
        "sat",
        "soundness gate: expected SAT\noutputs: {outputs:?}\nSMT:\n{smt}"
    );

    let stats = exec.validate_model().unwrap_or_else(|err| {
        panic!("soundness gate: model validation failed: {err}\nSMT:\n{smt}")
    });
    assert!(
        stats.checked > 0,
        "soundness gate: validate_model checked 0 assertions (stats={stats:?})\nSMT:\n{smt}"
    );
}

/// Assert that a workspace benchmark file returns SAT and the model validates.
pub(crate) fn assert_sat_validates_file(relative_path: &str) {
    let smt = load_workspace_script(relative_path);
    assert_sat_validates(&smt);
}

/// Assert that an SMT script does NOT return `unsat` (soundness guard).
///
/// For `:status sat` benchmarks where the solver may return `unknown` due
/// to completeness limitations (e.g., complex UF+arithmetic interactions,
/// expression splits). The key soundness property is that `unsat` must never
/// be returned on a satisfiable formula.
///
/// If the solver returns `sat`, model validation is also performed.
pub(crate) fn assert_not_unsat(smt: &str) {
    let (exec, outputs) = execute_script(smt);
    let first = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| panic!("soundness gate: no sat/unsat/unknown in output: {outputs:?}"));
    assert_ne!(
        first.trim(),
        "unsat",
        "soundness gate: must NOT return unsat on sat benchmark\noutputs: {outputs:?}\nSMT:\n{smt}"
    );
    if first.trim() == "sat" {
        let stats = exec.validate_model().unwrap_or_else(|err| {
            panic!("soundness gate: model validation failed: {err}\nSMT:\n{smt}")
        });
        assert!(
            stats.checked > 0,
            "soundness gate: validate_model checked 0 assertions (stats={stats:?})\nSMT:\n{smt}"
        );
    }
}

/// Assert that a workspace benchmark file does not return `unsat`.
pub(crate) fn assert_not_unsat_file(relative_path: &str) {
    let smt = load_workspace_script(relative_path);
    assert_not_unsat(&smt);
}

/// Assert that an SMT script does NOT return `sat` (soundness guard for
/// `:status unsat` benchmarks).
///
/// For benchmarks where the solver may return `unknown` due to completeness
/// limitations (e.g., QF_AUFLIA model-equality divergence #6846). The key
/// soundness property is that `sat` must never be returned on an unsatisfiable
/// formula. Both `unsat` and `unknown` are acceptable.
pub(crate) fn assert_not_sat(smt: &str) {
    let (_exec, outputs) = execute_script(smt);
    let first = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| panic!("soundness gate: no sat/unsat/unknown in output: {outputs:?}"));
    assert_ne!(
        first.trim(),
        "sat",
        "soundness gate: must NOT return sat on unsat benchmark\noutputs: {outputs:?}\nSMT:\n{smt}"
    );
}

/// Assert that a workspace benchmark file does not return `sat`.
pub(crate) fn assert_not_sat_file(relative_path: &str) {
    let smt = load_workspace_script(relative_path);
    assert_not_sat(&smt);
}

/// Verdict-only soundness guard: assert the script does NOT return `unsat`
/// (i.e. `sat` or `unknown`), WITHOUT requiring model-validation coverage.
///
/// Unlike [`assert_not_unsat`], this does not call `validate_model()`. It is for
/// quantifier-only `:status sat` benchmarks where the sole assertion is a
/// quantifier that model validation legitimately skips (so `checked` is 0):
/// the soundness property under test is purely the verdict — `unsat` on a
/// satisfiable formula is forbidden; `sat`/`unknown` are both acceptable.
pub(crate) fn assert_verdict_not_unsat(smt: &str) {
    let (_exec, outputs) = execute_script(smt);
    let first = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| panic!("soundness gate: no sat/unsat/unknown in output: {outputs:?}"));
    assert_ne!(
        first.trim(),
        "unsat",
        "soundness gate: must NOT return unsat on sat benchmark\noutputs: {outputs:?}\nSMT:\n{smt}"
    );
}

/// Verdict-only soundness guard: assert the script does NOT return `sat`
/// (i.e. `unsat` or `unknown`), WITHOUT requiring proof coverage. The mirror of
/// [`assert_verdict_not_unsat`] for `:status unsat` quantifier-only benchmarks.
pub(crate) fn assert_verdict_not_sat(smt: &str) {
    let (_exec, outputs) = execute_script(smt);
    let first = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| panic!("soundness gate: no sat/unsat/unknown in output: {outputs:?}"));
    assert_ne!(
        first.trim(),
        "sat",
        "soundness gate: must NOT return sat on unsat benchmark\noutputs: {outputs:?}\nSMT:\n{smt}"
    );
}

/// Assert that an SMT script returns UNSAT with a valid proof envelope.
///
/// The script must include `(set-option :produce-proofs true)`, `(check-sat)`,
/// and `(get-proof)`. The proof expectation controls how deeply the proof is
/// validated.
pub(crate) fn assert_unsat_with_proof(smt: &str, expectation: ProofExpectation) {
    let (exec, outputs) = execute_script(smt);

    // Expect exactly 2 outputs: check-sat result + get-proof text
    assert!(
        outputs.len() >= 2,
        "soundness gate: expected at least 2 outputs (check-sat + get-proof), got {}\noutputs: {outputs:?}\nSMT:\n{smt}",
        outputs.len()
    );
    assert_eq!(
        outputs[0].trim(),
        "unsat",
        "soundness gate: expected UNSAT\noutputs: {outputs:?}\nSMT:\n{smt}"
    );

    let proof_text = &outputs[1];
    assert!(
        !proof_text.trim().is_empty(),
        "soundness gate: proof text is empty\nSMT:\n{smt}"
    );

    let proof = exec.last_proof().unwrap_or_else(|| {
        panic!("soundness gate: get_last_proof() returned None after UNSAT\nSMT:\n{smt}")
    });

    match expectation {
        ProofExpectation::InternalChecked => {
            check_proof(proof, exec.terms()).unwrap_or_else(|err| {
                panic!(
                    "soundness gate: internal proof checker rejected proof: {err}\nproof:\n{proof_text}\nSMT:\n{smt}"
                )
            });
        }
        ProofExpectation::TextOnly => {
            // Require the proof object has steps but don't run the checker
            assert!(
                !proof.steps.is_empty(),
                "soundness gate: proof object has no steps\nSMT:\n{smt}"
            );
        }
    }
}

/// Assert that a script does not return SAT; if it returns UNSAT, also validate
/// the proof envelope. This is for sound-but-incomplete mixed-theory gates where
/// `unknown` is acceptable but a successful UNSAT answer must still carry proof
/// evidence.
pub(crate) fn assert_not_sat_with_optional_proof(smt: &str, expectation: ProofExpectation) {
    let (exec, outputs) = execute_script(smt);

    let first = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| panic!("soundness gate: no sat/unsat/unknown in output: {outputs:?}"));
    assert_ne!(
        first.trim(),
        "sat",
        "soundness gate: must NOT return sat on unsat benchmark\noutputs: {outputs:?}\nSMT:\n{smt}"
    );

    if first.trim() != "unsat" {
        return;
    }

    assert!(
        outputs.len() >= 2,
        "soundness gate: expected proof output after UNSAT, got {}\noutputs: {outputs:?}\nSMT:\n{smt}",
        outputs.len()
    );
    let proof_text = &outputs[1];
    assert!(
        !proof_text.trim().is_empty(),
        "soundness gate: proof text is empty\nSMT:\n{smt}"
    );
    let proof = exec.last_proof().unwrap_or_else(|| {
        panic!("soundness gate: get_last_proof() returned None after UNSAT\nSMT:\n{smt}")
    });

    match expectation {
        ProofExpectation::InternalChecked => {
            check_proof(proof, exec.terms()).unwrap_or_else(|err| {
                panic!(
                    "soundness gate: internal proof checker rejected proof: {err}\nproof:\n{proof_text}\nSMT:\n{smt}"
                )
            });
        }
        ProofExpectation::TextOnly => {
            assert!(
                !proof.steps.is_empty(),
                "soundness gate: proof object has no steps\nSMT:\n{smt}"
            );
        }
    }
}

/// Assert that a multi-check-sat script produces the expected result sequence.
///
/// `expected` should be an ordered slice of `"sat"`, `"unsat"`, or `"unknown"`.
pub(crate) fn assert_scope_results(smt: &str, expected: &[&str]) {
    let (_exec, outputs) = execute_script(smt);
    let results: Vec<&str> = outputs
        .iter()
        .map(|s| s.trim())
        .filter(|s| matches!(*s, "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(
        results, expected,
        "soundness gate: scope result mismatch\nexpected: {expected:?}\ngot: {results:?}\nall outputs: {outputs:?}\nSMT:\n{smt}"
    );
}
