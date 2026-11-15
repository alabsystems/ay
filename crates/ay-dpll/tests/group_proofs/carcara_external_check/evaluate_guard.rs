// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// A Carcara verdict that rests on an `evaluate` step pinned Carcara computes
// wrongly is not evidence
// ============================================================================
//
// The scan itself, `evaluate_steps_pinned_carcara_misjudges`, lives in
// `ay_core::pinned_carcara::evaluate` with the defect it answers, so every
// Carcara runner in the workspace (these corpus helpers, the bespoke test
// runners, `ay z3-audit`, the z3-parity UNSAT proof gate, `ay check
// carcara-guard`) shares one implementation. What stays here is the negative
// control that pins the defect against the REAL checker.

/// Pinned Carcara's verdict with no gate policy applied: the control below
/// must see the checker's own answer, not the guarded one.
#[cfg(test)]
fn unguarded_carcara_verdict(carcara: &Path, problem: &str, proof: &str) -> CarcaraVerdict {
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write control problem");
    std::fs::write(&proof_path, proof).expect("write control proof");
    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--expand-let-bindings")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara check (control)");
    carcara_stdout_verdict(
        output.status.success(),
        &String::from_utf8_lossy(&output.stdout),
    )
}

/// `run` must refuse its pair as not evidence: fail with the pinned-Carcara
/// refusal (`refuse_pinned_carcara_misjudgments`), never return a verdict,
/// whether `Valid` or the `Invalid` a tamper test would pass on.
#[cfg(test)]
fn assert_refused_as_not_evidence(label: &str, run: impl FnOnce() + std::panic::UnwindSafe) {
    let refusal = std::panic::catch_unwind(run).err().unwrap_or_else(|| {
        panic!("{label}: the helper returned a verdict on a pair pinned Carcara misjudges")
    });
    let message = refusal
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| refusal.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(message.contains("is not evidence"), "{label}: {message}");
}

/// The negative control behind the guard, end to end against the REAL
/// checker: `(bvsge #xf #xe)` is TRUE (-1 >= -2; z3 answers `sat`), yet
/// pinned Carcara prints `valid` for this `evaluate` refutation of it. Both
/// shared verdict helpers must refuse it before the checker runs: neither a
/// `valid` assertion nor a tamper test's not-`valid` may pass on it.
///
/// The pair is `ay_core::pinned_carcara::FALSE_VALID_CONTROL_*`, the one every
/// other runner's negative control feeds, so this test is what keeps those
/// controls honest: if pinned Carcara stops printing `valid` here, they no
/// longer demonstrate anything and must be re-measured.
#[test]
#[timeout(60_000)]
fn a_valid_verdict_resting_on_a_misjudged_evaluate_is_not_evidence() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let problem = ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM;
    let proof = ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF;
    assert_eq!(
        unguarded_carcara_verdict(&carcara, problem, proof),
        CarcaraVerdict::Valid,
        "pinned carcara no longer accepts this refutation of a satisfiable problem; \
         re-measure EVALUATE_OPERATORS_PINNED_CARCARA_MISJUDGES against the new checker"
    );
    assert_refused_as_not_evidence("no-allowance helper", || {
        carcara_verdict_without_allowances(&carcara, "misjudged_evaluate_control", problem, proof);
    });
    assert_refused_as_not_evidence("exact-verdict helper", || {
        exact_carcara_verdict(&carcara, problem, proof);
    });
}

/// The same control with a U+00A0 space after `bvsge`: pinned Carcara skips
/// every `char::is_whitespace` character, so it still reads `(bvsge #xf #xe)`
/// and still prints `valid` on the SATISFIABLE problem. A guard that split
/// atoms only at ASCII spaces read one atom `bvsge\u{a0}#xf` there and let the
/// pair through; the shared lexer splits where Carcara does, so both helpers
/// refuse it.
#[test]
#[timeout(60_000)]
fn a_valid_verdict_on_a_misjudged_evaluate_spelled_with_a_non_ascii_space_is_not_evidence() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let problem = ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM;
    let proof = ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF
        .replace("(= (bvsge #xf", "(= (bvsge\u{a0}#xf");
    assert_eq!(
        unguarded_carcara_verdict(&carcara, problem, &proof),
        CarcaraVerdict::Valid,
        "pinned carcara no longer accepts the U+00A0-spaced refutation; re-measure the \
         shared lexer's separators"
    );
    assert_refused_as_not_evidence("no-allowance helper", || {
        carcara_verdict_without_allowances(&carcara, "misjudged_evaluate_nbsp", problem, &proof);
    });
    assert_refused_as_not_evidence("exact-verdict helper", || {
        exact_carcara_verdict(&carcara, problem, &proof);
    });
}
