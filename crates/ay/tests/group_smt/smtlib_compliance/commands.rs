// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `smtlib_compliance.rs` to preserve test FQNs.

// ===========================================================================
// Part 2: SMT-LIB command compliance tests
// ===========================================================================

// ---- check-sat returns exactly "sat", "unsat", or "unknown" --------------

#[test]
fn test_compliance_command_check_sat_format_sat() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let fl = first_line(&out);
    assert_eq!(fl, "sat", "check-sat must return exactly 'sat', got '{fl}'");
}

#[test]
fn test_compliance_command_check_sat_format_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let fl = first_line(&out);
    assert_eq!(
        fl, "unsat",
        "check-sat must return exactly 'unsat', got '{fl}'"
    );
}

// ---- get-model returns a valid s-expression after SAT --------------------

#[test]
fn test_compliance_command_get_model() {
    let out = run_ay_stdin(
        "(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
(get-model)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert!(
        out.stdout.contains("sat"),
        "should contain 'sat' before model"
    );
    // Model must contain (define-fun or (model or opening parenthesis
    assert!(
        out.stdout.contains("define-fun") || out.stdout.contains("(model"),
        "get-model should return a model s-expression, got:\n{}",
        out.stdout
    );
    // Must mention x somewhere in the model
    assert!(
        out.stdout.contains(" x "),
        "model should define variable x, got:\n{}",
        out.stdout
    );
}

// ---- get-unsat-core returns a valid s-expression after UNSAT -------------

#[test]
fn test_compliance_command_get_unsat_core() {
    let out = run_ay_stdin(
        "(set-option :produce-unsat-cores true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (! (> x 10) :named a1))
(assert (! (< x 5) :named a2))
(check-sat)
(get-unsat-core)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert!(
        out.stdout.contains("unsat"),
        "should be unsat before core extraction"
    );
    // The unsat core must be an s-expression (starts with open paren)
    // and should mention at least one of the named assertions.
    let core_line = out
        .stdout
        .lines()
        .find(|l| l.trim().starts_with('(') && (l.contains("a1") || l.contains("a2")));
    assert!(
        core_line.is_some(),
        "get-unsat-core should return an s-expr mentioning named assertions, got:\n{}",
        out.stdout
    );
}

// ---- push/pop work correctly ---------------------------------------------

#[test]
fn test_compliance_command_push_pop() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got {:?}\nstdout:\n{}",
        results,
        out.stdout
    );
    assert_eq!(
        results[0], "unsat",
        "after push+contradiction: expected unsat, got {}",
        results[0]
    );
    assert_eq!(
        results[1], "sat",
        "after pop: expected sat, got {}",
        results[1]
    );
}

// ---- reset and reset-assertions work -------------------------------------

#[test]
fn test_compliance_command_reset_assertions() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(reset-assertions)
(declare-const y Int)
(assert (= y 1))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got {:?}\nstdout:\n{}",
        results,
        out.stdout
    );
    assert_eq!(results[0], "unsat", "before reset: expected unsat");
    assert_eq!(results[1], "sat", "after reset-assertions: expected sat");
}

#[test]
fn test_compliance_command_reset() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(reset)
(set-logic QF_LIA)
(declare-const y Int)
(assert (= y 1))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results after reset, got {:?}\nstdout:\n{}",
        results,
        out.stdout
    );
    assert_eq!(results[0], "unsat", "before reset: expected unsat");
    assert_eq!(results[1], "sat", "after reset: expected sat");
}

// ---- echo command --------------------------------------------------------

#[test]
fn test_compliance_command_echo() {
    let out = run_ay_stdin(
        "(echo \"hello world\")
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert!(
        out.stdout.contains("hello world"),
        "echo should output the string, got:\n{}",
        out.stdout
    );
}

// ---- exit terminates cleanly ---------------------------------------------

#[test]
fn test_compliance_command_exit() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(exit)
",
    );
    assert!(out.success, "ay should exit cleanly on (exit)");
}

// ---- get-info :name and :version -----------------------------------------

#[test]
fn test_compliance_command_get_info_name() {
    let out = run_ay_stdin(
        "(get-info :name)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    // Response should be an s-expression like (:name "AY")
    assert!(
        out.stdout.contains(":name") || out.stdout.contains("ay") || out.stdout.contains("AY"),
        "get-info :name should return solver name, got:\n{}",
        out.stdout
    );
}

#[test]
fn test_compliance_command_get_info_version() {
    let out = run_ay_stdin(
        "(get-info :version)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    // Response should be an s-expression containing :version
    assert!(
        out.stdout.contains(":version"),
        "get-info :version should return version info, got:\n{}",
        out.stdout
    );
}

// ---- set-option :produce-models is accepted ------------------------------

#[test]
fn test_compliance_command_set_option_produce_models() {
    let out = run_ay_stdin(
        "(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should accept :produce-models true");
    assert_eq!(
        first_line(&out),
        "sat",
        "should still solve correctly after set-option"
    );
}
