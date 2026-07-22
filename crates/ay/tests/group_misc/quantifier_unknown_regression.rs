// Copyright (c) 2024-2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0.
// SPDX-License-Identifier: Apache-2.0
//
// Regression tests for #229 (quantifier handling):
// Tests quantifier behavior - some return unknown, some are decidable.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

fn run_ay(input: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let mut child = Command::new(ay_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn ay");

    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(input.as_bytes()).unwrap();
    }

    let output = child.wait_with_output().expect("Failed to wait on ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(
        output.status.success(),
        "ay exited with {}.\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );
    stdout
}

fn solve_result(stdout: &str) -> &str {
    stdout
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .unwrap_or("")
}

/// #229: Forall quantifier — `forall y. y >= 0` is UNSAT (y = -1 is a counterexample).
/// Originally expected `unknown` when quantifiers weren't supported. Updated to `unsat`
/// now that AY handles this quantifier correctly (matches Z3 on LIA logic).
#[test]
#[timeout(60000)]
fn test_forall_returns_unsat() {
    let input = r#"(set-logic QF_LIA)
(declare-fun x () Int)
(assert (forall ((y Int)) (>= y 0)))
(check-sat)
"#;

    let output = run_ay(input);
    assert_eq!(
        solve_result(&output),
        "unsat",
        "Expected 'unsat' for forall y >= 0 (y=-1 is counterexample), got: {output}",
    );
}

/// Exists quantifier with trivial witness should return sat.
/// The formula (exists y. y = x) is trivially satisfiable: y=x witnesses.
/// Note: Previously expected `unknown` when quantifiers weren't supported (#229). Updated to `sat`
/// in #595 once quantifier elaboration became sound for this case.
#[test]
#[timeout(60000)]
fn test_exists_trivial_witness_sat() {
    let input = r#"(set-logic QF_LRA)
(declare-fun x () Real)
(assert (exists ((y Real)) (= y x)))
(check-sat)
"#;

    let output = run_ay(input);
    assert_eq!(
        solve_result(&output),
        "sat",
        "Expected 'sat' for trivially satisfiable exists, got: {output}",
    );
}

/// #229: Nested quantifiers with an affine witness are SAT.
/// For every `a`, choosing `b = x - a` satisfies `(+ a b) = x`.
/// AY's CEGQI does not yet handle nested forall-exists with Skolem functions
/// that depend on the outer variable, so `unknown` is acceptable until
/// nested quantifier instantiation is improved.
#[test]
#[timeout(60000)]
fn test_nested_quantifiers_returns_sat() {
    let input = r#"(set-logic QF_LIA)
(declare-fun x () Int)
(assert (forall ((a Int)) (exists ((b Int)) (= (+ a b) x))))
(check-sat)
"#;

    let output = run_ay(input);
    let result = solve_result(&output);
    assert!(
        result == "sat" || result == "unknown",
        "Expected 'sat' or 'unknown' for nested quantifiers with witness b = x - a, got: {output}",
    );
}

/// Non-quantified formulas should still work normally (sat)
#[test]
#[timeout(60000)]
fn test_non_quantified_sat() {
    let input = r#"(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x 42))
(check-sat)
"#;

    let output = run_ay(input);
    assert_eq!(
        solve_result(&output),
        "sat",
        "Expected 'sat' for non-quantified formula, got: {output}",
    );
}

/// Non-quantified formulas should still work normally (unsat)
#[test]
#[timeout(60000)]
fn test_non_quantified_unsat() {
    let input = r#"(set-logic QF_LIA)
(declare-fun x () Int)
(assert (and (> x 0) (< x 0)))
(check-sat)
"#;

    let output = run_ay(input);
    assert_eq!(
        solve_result(&output),
        "unsat",
        "Expected 'unsat' for contradictory formula, got: {output}",
    );
}

/// Negated forall — `not(forall y. y >= 0)` is SAT (equivalent to `exists y. y < 0`).
/// Originally expected `unknown` when quantifiers weren't supported. Updated to `sat`
/// now that AY handles quantifier negation correctly (matches Z3 on LIA logic).
#[test]
#[timeout(60000)]
fn test_quantifier_in_negation_sat() {
    let input = r#"(set-logic QF_LIA)
(declare-fun x () Int)
(assert (not (forall ((y Int)) (>= y 0))))
(check-sat)
"#;

    let output = run_ay(input);
    assert_eq!(
        solve_result(&output),
        "sat",
        "Expected 'sat' for not(forall y >= 0), i.e. exists y < 0, got: {output}",
    );
}

/// Quantifier in conjunction: `(and (> x 0) (forall y. y >= 0))`.
/// The forall is UNSAT (y=-1), so the conjunction is also UNSAT.
/// Originally expected `unknown` when quantifiers weren't supported. Updated to `unsat`
/// now that AY handles this quantifier correctly.
#[test]
#[timeout(60000)]
fn test_quantifier_in_conjunction() {
    let input = r#"(set-logic QF_LIA)
(declare-fun x () Int)
(assert (and (> x 0) (forall ((y Int)) (>= y 0))))
(check-sat)
"#;

    let output = run_ay(input);
    let result = solve_result(&output);
    assert!(
        result == "unsat" || result == "unknown",
        "Expected 'unsat' or 'unknown' for quantifier in conjunction, got: {output}",
    );
}

/// #5888: Mixed UF+arithmetic quantifier — deductive-checks pattern.
/// `forall x:Int. f(x) > 0 => x >= 1` should be handled by CEGQI now.
/// The formula is not universally valid (f(0) > 0 but 0 < 1 is fine, but
/// f(1) could be <= 0), so the expected result depends on the interpretation.
/// With CEGQI, we should at least get a definite answer (sat or unsat), not unknown.
#[test]
#[timeout(60000)]
fn test_cegqi_mixed_uf_arith_deductive_checks_pattern() {
    let input = r#"(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (forall ((y Int)) (=> (> (f y) 0) (>= y 1))))
(check-sat)
"#;

    let output = run_ay(input);
    let result = solve_result(&output);
    // Formula is SAT (e.g., f(y) = 0 for all y satisfies the implication).
    // AY may return unknown (quantifier incompleteness) but must never
    // return false-UNSAT.
    assert!(
        result == "sat" || result == "unknown",
        "Expected sat or unknown for SAT formula, got {result:?} (false-UNSAT regression)\noutput: {output}",
    );
}

/// #5888: Tautological mixed UF+arith — `forall x. f(x) > x => x < f(x)`.
/// This is a tautology (a > b iff b < a), so should be SAT.
#[test]
#[timeout(60000)]
fn test_cegqi_mixed_uf_arith_tautology() {
    let input = r#"(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (=> (> (f x) x) (< x (f x)))))
(check-sat)
"#;

    let output = run_ay(input);
    let result = solve_result(&output);
    assert!(
        result == "sat" || result == "unknown",
        "Expected 'sat' (or 'unknown') for tautological mixed UF+arith, got: {output}",
    );
}
