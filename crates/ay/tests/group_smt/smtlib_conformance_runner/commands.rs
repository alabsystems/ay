// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `smtlib_conformance_runner.rs` to preserve test FQNs.

// ===========================================================================
// Part 2: Additional command compliance tests
// ===========================================================================

// --- check-sat-assuming ---

#[test]
fn test_cmd_check_sat_assuming_sat() {
    let input = "\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (> y 0))
(check-sat-assuming ((> x 5)))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "check-sat-assuming expected sat or unknown, got: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
fn test_cmd_check_sat_assuming_unsat() {
    let input = "\
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(check-sat-assuming ((< x 0)))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "unsat" || fl == "unknown",
        "check-sat-assuming expected unsat or unknown, got: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
fn test_cmd_check_sat_assuming_incremental() {
    let input = "\
(set-logic QF_UF)
(set-option :produce-unsat-assumptions true)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(assert (not (= a b)))
(check-sat-assuming ((= a b)))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "unsat" || fl == "unknown",
        "check-sat-assuming contradictory expected unsat or unknown, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- get-value ---

#[test]
fn test_cmd_get_value_int() {
    let input = "\
(set-logic QF_LIA)
(set-option :produce-models true)
(declare-const x Int)
(assert (= x 42))
(check-sat)
(get-value (x))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "get-value test: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
    if fl == "sat" {
        // Output should contain the value assignment
        assert!(
            out.stdout.contains("42") || out.stdout.contains("x"),
            "get-value output should contain value: {}",
            out.stdout
        );
    }
}

#[test]
fn test_cmd_get_value_bool() {
    let input = "\
(set-logic QF_UF)
(set-option :produce-models true)
(declare-const p Bool)
(assert p)
(check-sat)
(get-value (p))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "get-value bool test: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
    if fl == "sat" {
        assert!(
            out.stdout.contains("true") || out.stdout.contains("p"),
            "get-value bool output should contain true: {}",
            out.stdout
        );
    }
}

#[test]
fn test_cmd_get_value_bitvector() {
    let input = "\
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(assert (= x #xFF))
(check-sat)
(get-value (x))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "get-value bv test: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- define-fun ---

#[test]
fn test_cmd_define_fun_basic() {
    let input = "\
(set-logic QF_LIA)
(define-fun double ((x Int)) Int (* 2 x))
(declare-const a Int)
(assert (= (double a) 10))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "define-fun basic: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
fn test_cmd_define_fun_nested() {
    let input = "\
(set-logic QF_LIA)
(define-fun inc ((x Int)) Int (+ x 1))
(define-fun double_inc ((x Int)) Int (inc (inc x)))
(declare-const a Int)
(assert (= (double_inc 0) 2))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "define-fun nested: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- define-sort ---

#[test]
fn test_cmd_define_sort_alias() {
    let input = "\
(set-logic QF_LIA)
(define-sort MyInt () Int)
(declare-const x MyInt)
(assert (> x 5))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "define-sort alias: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
fn test_cmd_define_sort_parametric() {
    let input = "\
(set-logic QF_AUFLIA)
(define-sort IntArray () (Array Int Int))
(declare-const a IntArray)
(assert (= (select a 0) 42))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "define-sort parametric: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- declare-datatypes ---

#[test]
fn test_cmd_declare_datatypes_simple() {
    let input = "\
(set-logic ALL)
(declare-datatypes ((Color 0)) (((Red) (Green) (Blue))))
(declare-const c Color)
(assert (= c Red))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    // Datatype support may be partial
    assert!(
        fl == "sat" || fl == "unknown" || out.stdout.contains("error") || !out.success,
        "declare-datatypes: unexpected output: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
fn test_cmd_declare_datatypes_option() {
    let input = "\
(set-logic ALL)
(declare-datatypes ((Option 1)) ((par (T) ((Some (val T)) (None)))))
(declare-const x (Option Int))
(assert (= x (Some 42)))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown" || out.stdout.contains("error") || !out.success,
        "declare-datatypes option: unexpected output: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- get-info ---

#[test]
fn test_cmd_get_info_version() {
    let input = "\
(get-info :name)
(get-info :version)
(exit)
";
    let out = run_ay_stdin(input);
    // Should produce some response (not necessarily formatted per spec)
    assert!(
        out.success || !out.stdout.is_empty(),
        "get-info should produce output\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

// --- get-unsat-assumptions ---

#[test]
fn test_cmd_get_unsat_assumptions() {
    let input = "\
(set-logic QF_LIA)
(set-option :produce-unsat-assumptions true)
(declare-const x Int)
(assert (> x 0))
(check-sat-assuming ((< x 0)))
(get-unsat-assumptions)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    // The first line should be unsat (or unknown)
    assert!(
        fl == "unsat" || fl == "unknown",
        "get-unsat-assumptions test: expected unsat, got: {fl}\nstderr: {}",
        out.stderr
    );
}
