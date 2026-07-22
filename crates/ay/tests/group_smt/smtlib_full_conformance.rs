// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB 2.6 full conformance test suite (#8343).
//!
//! Complements smtlib_compliance.rs and smtlib_conformance_runner.rs with:
//! - Sort operation tests (BitVec construction, Array parameterization, Int/Real coercion)
//! - Command coverage gaps (set-info, get-assertions, get-assignment, get-option,
//!   simplify, declare-sort, define-fun-rec)
//! - Error handling for malformed input
//! - Let bindings and nested term expressions
//! - Quantifier tests (forall, exists)
//! - Sequential check-sat without push/pop
//! - Boolean connective completeness
//! - Numeral and decimal literal formats
//! - Named assertions and annotation handling

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

// ---------------------------------------------------------------------------
// Helper: run AY with SMT-LIB input on stdin
// ---------------------------------------------------------------------------

struct AYOutput {
    stdout: String,
    stderr: String,
    success: bool,
}

fn run_ay_stdin(input: &str) -> AYOutput {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let mut child = Command::new(ay_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn ay");

    {
        let stdin = child.stdin.as_mut().expect("stdin must be piped");
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write to ay stdin");
    }

    let output = child.wait_with_output().expect("failed to wait on ay");
    AYOutput {
        stdout: String::from_utf8_lossy(&output.stdout).to_string(),
        stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        success: output.status.success(),
    }
}

fn first_line(out: &AYOutput) -> &str {
    out.stdout.lines().next().unwrap_or("").trim()
}

fn check_sat_results(out: &AYOutput) -> Vec<String> {
    out.stdout
        .lines()
        .filter(|l| {
            let t = l.trim();
            t == "sat" || t == "unsat" || t == "unknown"
        })
        .map(|l| l.trim().to_string())
        .collect()
}

/// Assert the first check-sat result is exactly `expected`, or "unknown" if `allow_unknown`.
fn assert_result(out: &AYOutput, expected: &str, allow_unknown: bool, context: &str) {
    let fl = first_line(out);
    if allow_unknown && fl == "unknown" {
        return;
    }
    assert!(
        out.success,
        "{context}: ay exited with failure\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert_eq!(
        fl, expected,
        "{context}: expected '{expected}', got '{fl}'\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
}

// ===========================================================================
// Part 1: Sort operations
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_sort_bitvec_various_widths() {
    // Test BitVec sorts of various widths: 1, 8, 16, 32, 64
    for width in &[1, 8, 16, 32, 64] {
        let input = format!(
            "(set-logic QF_BV)
(declare-const x (_ BitVec {width}))
(check-sat)
(exit)
"
        );
        let out = run_ay_stdin(&input);
        assert!(
            out.success,
            "BitVec width {width}: ay should not crash\nstderr: {}",
            out.stderr
        );
        let fl = first_line(&out);
        assert!(
            fl == "sat" || fl == "unknown",
            "BitVec width {width}: expected sat, got '{fl}'"
        );
    }
}

#[test]
#[timeout(30_000)]
fn test_sort_array_int_int() {
    let out = run_ay_stdin(
        "(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select (store a i 42) i) 42))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "Array Int Int store/select");
}

#[test]
#[timeout(30_000)]
fn test_sort_array_nested() {
    // Array of arrays: (Array Int (Array Int Int))
    let out = run_ay_stdin(
        "(set-logic QF_AUFLIA)
(declare-const a (Array Int (Array Int Int)))
(declare-const i Int)
(declare-const j Int)
(assert (= (select (select a i) j) 99))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "nested Array sort");
}

#[test]
#[timeout(30_000)]
fn test_sort_bool_as_first_class() {
    // Bool is a first-class sort in SMT-LIB
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (and p (not q)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "Bool first-class sort");
}

#[test]
#[timeout(30_000)]
fn test_sort_to_real_to_int_coercion() {
    let out = run_ay_stdin(
        "(set-logic QF_LIRA)
(declare-const x Int)
(declare-const y Real)
(assert (= y (to_real x)))
(assert (= x 5))
(assert (= y 5.0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "to_real coercion");
}

// ===========================================================================
// Part 2: Command coverage gaps
// ===========================================================================

// ---- set-info ---

#[test]
#[timeout(30_000)]
fn test_cmd_set_info_source() {
    let out = run_ay_stdin(
        "(set-info :source \"test suite\")
(set-info :category \"crafted\")
(set-info :status sat)
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(check-sat)
(exit)
",
    );
    assert!(
        out.success,
        "set-info should be accepted\nstderr: {}",
        out.stderr
    );
    assert_eq!(
        first_line(&out),
        "sat",
        "set-info should not affect solving"
    );
}

#[test]
#[timeout(30_000)]
fn test_cmd_set_info_status_unsat() {
    let out = run_ay_stdin(
        "(set-info :status unsat)
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(exit)
",
    );
    assert!(
        out.success,
        "set-info :status should be accepted\nstderr: {}",
        out.stderr
    );
    assert_eq!(first_line(&out), "unsat");
}

// ---- get-assertions ---

#[test]
#[timeout(30_000)]
fn test_cmd_get_assertions() {
    let out = run_ay_stdin(
        "(set-option :interactive-mode true)
(set-option :produce-assertions true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 10))
(get-assertions)
(check-sat)
(exit)
",
    );
    // get-assertions should return an s-expression list
    // Even if the response format varies, it should not crash
    assert!(
        out.success,
        "get-assertions should not crash\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_cmd_get_assertions_via_produce_assertions_only() {
    // z3 enables (get-assertions) via the SMT-LIB 2.6 `:produce-assertions`
    // option (not the deprecated 2.5 `:interactive-mode`). AY must accept it too,
    // or every z3-driver that sets `:produce-assertions` gets an error instead of
    // its assertion list.
    let out = run_ay_stdin(
        "(set-option :produce-assertions true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(get-assertions)
(exit)
",
    );
    assert!(
        !out.stdout
            .to_lowercase()
            .contains("only available in interactive"),
        "`:produce-assertions true` must enable get-assertions (z3 parity)\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
    // The assertion must appear in the returned list (AY may normalize `(> x 0)`
    // to `(< 0 x)`; accept either spelling).
    assert!(
        out.stdout.contains("x 0") || out.stdout.contains("0 x"),
        "get-assertions must return the asserted constraint\nstdout: {}",
        out.stdout
    );
}

// ---- get-assignment ---

#[test]
#[timeout(30_000)]
fn test_cmd_get_assignment() {
    let out = run_ay_stdin(
        "(set-option :produce-assignments true)
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (! p :named a1))
(assert (! (not q) :named a2))
(check-sat)
(get-assignment)
(exit)
",
    );
    // get-assignment should not crash; output format may vary
    assert!(
        out.success,
        "get-assignment should not crash\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
}

// ---- get-option ---

#[test]
#[timeout(30_000)]
fn test_cmd_get_option() {
    let out = run_ay_stdin(
        "(set-option :produce-models true)
(get-option :produce-models)
(exit)
",
    );
    // Should return "true" or (:produce-models true) or similar
    assert!(
        out.success,
        "get-option should not crash\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("true"),
        "get-option :produce-models should return true, got: {}",
        out.stdout
    );
}

// ---- simplify ---

#[test]
#[timeout(30_000)]
fn test_cmd_simplify() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(simplify (+ 1 2))
(exit)
",
    );
    // Simplify should return simplified expression (e.g., "3")
    assert!(
        out.success,
        "simplify should not crash\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains('3'),
        "simplify (+ 1 2) should return 3, got: {}",
        out.stdout
    );
}

#[test]
#[timeout(30_000)]
fn test_cmd_simplify_bool() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(simplify (and true false))
(exit)
",
    );
    assert!(
        out.success,
        "simplify bool should not crash\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("false"),
        "simplify (and true false) should return false, got: {}",
        out.stdout
    );
}

// ---- declare-sort ---

#[test]
#[timeout(30_000)]
fn test_cmd_declare_sort_arity_zero() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-sort T 0)
(declare-const a T)
(declare-const b T)
(assert (not (= a b)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "declare-sort arity 0");
}

#[test]
#[timeout(30_000)]
fn test_cmd_declare_sort_used_in_function() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const a U)
(declare-const b U)
(assert (= (f a) b))
(assert (= (f b) a))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "declare-sort used in function");
}

// ---- define-fun-rec ---

#[test]
#[timeout(30_000)]
fn test_cmd_define_fun_rec() {
    // Use a simple non-recursive definition to test parsing of define-fun-rec.
    // Actual recursive evaluation may time out on complex cases.
    let out = run_ay_stdin(
        "(set-logic ALL)
(define-fun-rec id ((n Int)) Int n)
(declare-const x Int)
(assert (= (id 5) 5))
(check-sat)
(exit)
",
    );
    // define-fun-rec may not be fully supported; just verify no crash
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unsat" || fl == "unknown" || !out.success,
        "define-fun-rec should not crash unexpectedly, got: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_cmd_define_fun_rec_genuine_recursion_evaluates() {
    // Regression (Phase 1 CLI drop-in): a terminating recursive function applied
    // to a concrete argument must EVALUATE, not blow the expansion-depth limit.
    // Previously `(fact 5)` errored with "recursion depth limit exceeded" because
    // the ite else-branch (holding the recursive call) was elaborated even when
    // the guard was decidably true. Now the ite short-circuits on a constant
    // guard, so the recursion terminates.
    let out = run_ay_stdin(
        "(set-logic ALL)
(define-fun-rec fact ((n Int)) Int (ite (<= n 0) 1 (* n (fact (- n 1)))))
(declare-const r Int)
(assert (= r (fact 5)))
(check-sat)
(get-value (r))
(exit)
",
    );
    assert_eq!(
        first_line(&out),
        "sat",
        "fact(5) should be sat; stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stdout.contains("(r 120)"),
        "fact(5) must evaluate to 120, got: {}",
        out.stdout
    );

    // Tree recursion (two recursive calls per step) must also terminate.
    let fib = run_ay_stdin(
        "(set-logic ALL)
(define-fun-rec fib ((n Int)) Int (ite (<= n 1) n (+ (fib (- n 1)) (fib (- n 2)))))
(declare-const r Int)
(assert (= r (fib 7)))
(check-sat)
(get-value (r))
(exit)
",
    );
    assert_eq!(
        first_line(&fib),
        "sat",
        "fib(7) should be sat; stdout={} stderr={}",
        fib.stdout,
        fib.stderr
    );
    assert!(
        fib.stdout.contains("(r 13)"),
        "fib(7) must evaluate to 13, got: {}",
        fib.stdout
    );
}

// ===========================================================================
// Part 3: Let bindings and nested term expressions
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_let_binding_simple() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (let ((y (+ x 1))) (> y 5)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "let binding simple");
}

#[test]
#[timeout(30_000)]
fn test_let_binding_nested() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert
  (let ((y (+ x 1)))
    (let ((z (* y 2)))
      (= z 10))))
(check-sat)
(exit)
",
    );
    // (x+1)*2 = 10 => x = 4, should be sat
    assert_result(&out, "sat", false, "let binding nested");
}

#[test]
#[timeout(30_000)]
fn test_let_binding_multiple_vars() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(assert
  (let ((x (+ a b)) (y (- a b)))
    (and (= x 10) (= y 2))))
(check-sat)
(exit)
",
    );
    // a+b=10, a-b=2 => a=6, b=4, should be sat
    assert_result(&out, "sat", false, "let binding multiple vars");
}

// ===========================================================================
// Part 4: Quantifier tests
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_quantifier_forall_trivial_sat() {
    let out = run_ay_stdin(
        "(set-logic LIA)
(assert (forall ((x Int)) (= x x)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "forall trivial sat");
}

#[test]
#[timeout(30_000)]
fn test_quantifier_forall_trivial_unsat() {
    let out = run_ay_stdin(
        "(set-logic LIA)
(assert (forall ((x Int)) (> x x)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", true, "forall trivial unsat");
}

#[test]
#[timeout(30_000)]
fn test_quantifier_exists_sat() {
    let out = run_ay_stdin(
        "(set-logic LIA)
(assert (exists ((x Int)) (= (* x x) 4)))
(check-sat)
(exit)
",
    );
    // x=2 satisfies x*x=4
    assert_result(&out, "sat", true, "exists sat");
}

#[test]
#[timeout(30_000)]
fn test_quantifier_forall_exists_combination() {
    let out = run_ay_stdin(
        "(set-logic LIA)
(assert (forall ((x Int)) (exists ((y Int)) (= (+ x y) 0))))
(check-sat)
(exit)
",
    );
    // For all x, y = -x makes x+y=0
    assert_result(&out, "sat", true, "forall-exists combination");
}

// ===========================================================================
// Part 5: Sequential check-sat without push/pop
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_sequential_check_sat_accumulating() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 0))
(check-sat)
(assert (<= x 10))
(check-sat)
(assert (= x 5))
(check-sat)
(exit)
",
    );
    assert!(
        out.success,
        "sequential check-sat should not crash\nstderr: {}",
        out.stderr
    );
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        3,
        "expected 3 check-sat results, got {:?}\nstdout:\n{}",
        results,
        out.stdout
    );
    // All assertions are satisfiable together
    assert_eq!(results[0], "sat", "x >= 0: sat");
    assert_eq!(results[1], "sat", "x >= 0 and x <= 10: sat");
    assert_eq!(results[2], "sat", "x >= 0 and x <= 10 and x = 5: sat");
}

#[test]
#[timeout(30_000)]
fn test_sequential_check_sat_becomes_unsat() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
(assert (< x 3))
(check-sat)
(exit)
",
    );
    assert!(
        out.success,
        "sequential check-sat becoming unsat should not crash\nstderr: {}",
        out.stderr
    );
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got {results:?}"
    );
    assert_eq!(results[0], "sat", "x > 5: sat");
    assert_eq!(results[1], "unsat", "x > 5 and x < 3: unsat");
}

// ===========================================================================
// Part 6: Boolean connective completeness
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_bool_and() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (and p q))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "bool and");
}

#[test]
#[timeout(30_000)]
fn test_bool_or() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(assert (not p))
(assert (not q))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", false, "bool or unsat");
}

#[test]
#[timeout(30_000)]
fn test_bool_xor() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (xor p q))
(assert (= p q))
(check-sat)
(exit)
",
    );
    // xor(p,q) and p=q is contradictory
    assert_result(&out, "unsat", false, "bool xor unsat");
}

#[test]
#[timeout(30_000)]
fn test_bool_implies() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (=> p q))
(assert p)
(assert (not q))
(check-sat)
(exit)
",
    );
    // p => q, p, not q is contradictory
    assert_result(&out, "unsat", false, "bool implies unsat");
}

#[test]
#[timeout(30_000)]
fn test_bool_ite() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const p Bool)
(declare-const x Int)
(assert (= x (ite p 1 2)))
(assert (= x 1))
(check-sat)
(exit)
",
    );
    // x = ite(p, 1, 2), x = 1 => p must be true, satisfiable
    assert_result(&out, "sat", false, "bool ite");
}

#[test]
#[timeout(30_000)]
fn test_bool_distinct() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(assert (distinct a b c))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "distinct 3 values");
}

#[test]
#[timeout(30_000)]
fn test_bool_distinct_contradicts_equal() {
    let out = run_ay_stdin(
        "(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(assert (distinct a b))
(assert (= a b))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", false, "distinct contradicts equal");
}

// ===========================================================================
// Part 7: Numeral and decimal literal formats
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_literal_int_zero() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "int literal zero");
}

#[test]
#[timeout(30_000)]
fn test_literal_int_negative() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x (- 42)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "int literal negative");
}

#[test]
#[timeout(30_000)]
fn test_literal_real_decimal() {
    let out = run_ay_stdin(
        "(set-logic QF_LRA)
(declare-const x Real)
(assert (= x 3.14))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "real decimal literal");
}

#[test]
#[timeout(30_000)]
fn test_literal_real_fraction() {
    let out = run_ay_stdin(
        "(set-logic QF_LRA)
(declare-const x Real)
(assert (= x (/ 1 3)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "real fraction literal");
}

#[test]
#[timeout(30_000)]
fn test_literal_bv_hex() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #xAB))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "bv hex literal");
}

#[test]
#[timeout(30_000)]
fn test_literal_bv_binary() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #b1010))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "bv binary literal");
}

// ===========================================================================
// Part 8: Named assertions and annotations
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_named_assertion() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (! (> x 0) :named pos))
(assert (! (< x 10) :named bound))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "named assertion");
}

#[test]
#[timeout(30_000)]
fn test_named_assertion_with_pattern() {
    // :pattern is used in quantified formulas
    let out = run_ay_stdin(
        "(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (>= (f x) 0) :pattern ((f x)))))
(declare-const a Int)
(assert (< (f a) 0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", true, "named assertion with pattern");
}

// ===========================================================================
// Part 9: Error handling for malformed input
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_error_unknown_command() {
    let out = run_ay_stdin(
        "(nonexistent-command)
(exit)
",
    );
    // Should produce an error message (on stderr or stdout), not crash
    assert!(
        out.stderr.contains("error")
            || out.stderr.contains("Error")
            || out.stdout.contains("error")
            || !out.success,
        "unknown command should produce error\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_error_missing_check_sat_args() {
    // declare-const without sort should error
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const)
(exit)
",
    );
    assert!(
        out.stderr.contains("error")
            || out.stderr.contains("Error")
            || out.stdout.contains("error")
            || !out.success,
        "missing args should produce error\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_error_type_mismatch() {
    // Comparing Int and Bool should error
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(declare-const p Bool)
(assert (= x p))
(check-sat)
(exit)
",
    );
    // Either errors at elaboration or at check-sat; should not panic
    assert!(
        out.stderr.contains("error")
            || out.stderr.contains("Error")
            || out.stdout.contains("error")
            || out.stdout.contains("sat")
            || out.stdout.contains("unsat")
            || out.stdout.contains("unknown")
            || !out.success,
        "type mismatch should produce error or handle gracefully\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_error_unbalanced_parens() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int))
(check-sat)
(exit)
",
    );
    // Extra closing paren should be handled
    assert!(
        out.stderr.contains("error")
            || out.stderr.contains("Error")
            || !out.success
            || out.stdout.contains("error"),
        "unbalanced parens should produce error\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_error_pop_underflow() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(pop 1)
(exit)
",
    );
    // Pop without push should produce an error
    assert!(
        out.stderr.contains("error")
            || out.stderr.contains("Error")
            || !out.success
            || out.stdout.contains("error"),
        "pop underflow should produce error\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_error_undeclared_symbol() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(assert (> y 0))
(check-sat)
(exit)
",
    );
    // Using undeclared variable y should error
    assert!(
        out.stderr.contains("error")
            || out.stderr.contains("Error")
            || !out.success
            || out.stdout.contains("error"),
        "undeclared symbol should produce error\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

// ===========================================================================
// Part 10: Arithmetic operations completeness
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_arith_int_abs() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x (- 5)))
(assert (= (abs x) 5))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "int abs");
}

#[test]
#[timeout(30_000)]
fn test_arith_int_div_mod() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= x 7))
(assert (= y 3))
(assert (= (div x y) 2))
(assert (= (mod x y) 1))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "int div mod");
}

#[test]
#[timeout(30_000)]
fn test_arith_real_division() {
    let out = run_ay_stdin(
        "(set-logic QF_LRA)
(declare-const x Real)
(assert (= (* x 3.0) 6.0))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "real division via multiplication");
}

// ===========================================================================
// Part 11: BitVector operation completeness
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_bv_extract_concat() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #xAB))
(assert (= ((_ extract 7 4) x) #xA))
(assert (= ((_ extract 3 0) x) #xB))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "bv extract");
}

#[test]
#[timeout(30_000)]
fn test_bv_concat() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (= x #xA))
(assert (= y #xB))
(assert (= (concat x y) #xAB))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "bv concat");
}

#[test]
#[timeout(30_000)]
fn test_bv_arithmetic() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= x #x03))
(assert (= y #x05))
(assert (= (bvadd x y) #x08))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "bv arithmetic");
}

#[test]
#[timeout(30_000)]
fn test_bv_shift() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x01))
(assert (= (bvshl x #x02) #x04))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "bv shift left");
}

#[test]
#[timeout(30_000)]
fn test_bv_sign_extend() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #xF))
(assert (= ((_ sign_extend 4) x) #xFF))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "bv sign_extend");
}

#[test]
#[timeout(30_000)]
fn test_bv_zero_extend() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #xF))
(assert (= ((_ zero_extend 4) x) #x0F))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "bv zero_extend");
}

// ===========================================================================
// Part 12: Multiple logics in sequence (after reset)
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_logic_switching_via_reset() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
(reset)
(set-logic QF_BV)
(declare-const y (_ BitVec 8))
(assert (= y #xFF))
(check-sat)
(exit)
",
    );
    assert!(
        out.success,
        "logic switching via reset should work\nstderr: {}",
        out.stderr
    );
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got {results:?}"
    );
    assert_eq!(results[0], "sat", "QF_LIA: sat");
    assert_eq!(results[1], "sat", "QF_BV after reset: sat");
}

// ===========================================================================
// Part 13: String theory operations
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_string_concat() {
    let out = run_ay_stdin(
        "(set-logic QF_S)
(declare-const s1 String)
(declare-const s2 String)
(assert (= (str.++ s1 s2) \"hello\"))
(assert (= s1 \"hel\"))
(assert (= s2 \"lo\"))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "string concat");
}

#[test]
#[timeout(30_000)]
fn test_string_contains() {
    let out = run_ay_stdin(
        "(set-logic QF_S)
(declare-const s String)
(assert (= s \"hello world\"))
(assert (str.contains s \"world\"))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "string contains");
}

#[test]
#[timeout(30_000)]
fn test_string_length_constraint() {
    let out = run_ay_stdin(
        "(set-logic QF_SLIA)
(declare-const s String)
(assert (= (str.len s) 3))
(assert (str.prefixof \"ab\" s))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", true, "string length + prefix");
}

// ===========================================================================
// Part 14: check-sat-assuming with unsat-core extraction
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_check_sat_assuming_with_core() {
    let out = run_ay_stdin(
        "(set-option :produce-unsat-cores true)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const p Bool)
(declare-const q Bool)
(assert (=> p (> x 10)))
(assert (=> q (< x 5)))
(check-sat-assuming (p q))
(exit)
",
    );
    let fl = first_line(&out);
    assert!(
        fl == "unsat" || fl == "unknown",
        "check-sat-assuming contradictory assumptions: expected unsat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// ===========================================================================
// Part 15: Empty formula / trivial cases
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_trivial_check_sat_no_assertions() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "trivial check-sat no assertions");
}

#[test]
#[timeout(30_000)]
fn test_trivial_assert_true() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(assert true)
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "assert true");
}

#[test]
#[timeout(30_000)]
fn test_trivial_assert_false() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(assert false)
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", false, "assert false");
}

// ===========================================================================
// Part 16: Multiple declarations of same sort
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_multiple_consts_same_sort() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)
(assert (distinct a b c d e))
(assert (>= a 1))
(assert (<= e 5))
(assert (and (>= b 1) (<= b 5)))
(assert (and (>= c 1) (<= c 5)))
(assert (and (>= d 1) (<= d 5)))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "multiple consts same sort");
}

// ===========================================================================
// Part 17: define-sort with parameterized sorts
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_define_sort_bitvec_alias() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(define-sort Word () (_ BitVec 32))
(declare-const x Word)
(assert (= x #x00000042))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "define-sort bv alias");
}

#[test]
#[timeout(30_000)]
fn test_define_sort_parameterized_alias() {
    // A parameterized synonym `(define-sort Pair (T) (Array Int T))` must
    // substitute the type parameter and solve like z3 (previously AY errored
    // "unsupported: parameterized sort" with no verdict).
    let out = run_ay_stdin(
        "(set-logic ALL)
(define-sort Pair (T) (Array Int T))
(declare-const p (Pair Int))
(assert (= (select p 0) 5))
(check-sat)
(exit)
",
    );
    assert_result(&out, "sat", false, "parameterized define-sort");
}

#[test]
#[timeout(30_000)]
fn test_define_sort_parameterized_alias_unsat() {
    // Soundness: a contradiction expressed through the synonym must be `unsat`,
    // never a dropped-constraint `sat`. Nested synonyms + multi-param too.
    let out = run_ay_stdin(
        "(set-logic ALL)
(define-sort IArr (T) (Array Int T))
(define-sort Matrix (T) (IArr (IArr T)))
(declare-const m (Matrix Int))
(assert (= (select (select m 0) 1) 5))
(assert (= (select (select m 0) 1) 6))
(check-sat)
(exit)
",
    );
    assert_result(&out, "unsat", false, "parameterized define-sort unsat");
}

#[test]
#[timeout(30_000)]
fn test_define_sort_recursive_terminates() {
    // A self-recursive parameterized synonym is malformed (z3 rejects it as an
    // unknown sort). AY's lazy expansion must NOT infinite-loop — the recursion
    // guard rejects the re-entry so the run terminates (the 30s test timeout is
    // the hang detector). Behaviour matches z3 exactly: both error on the bad
    // sort and then report `sat` for the resulting empty (constraint-free)
    // problem. The meaningful assertion is that the guard fired (an error is
    // surfaced) rather than looping forever.
    let out = run_ay_stdin(
        "(set-logic ALL)
(define-sort Loop (T) (Loop T))
(declare-const x (Loop Int))
(check-sat)
(exit)
",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("recursive sort synonym"),
        "the recursion guard must fire (proving no infinite expansion)\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_qf_bvfp_model_not_corrupted_by_minimization() {
    // A BV var used only under `(_ to_fp …)` must keep its FP-pinned value in
    // the model — the counterexample minimizer used to shrink it to 0, producing
    // an invalid model while the verdict stayed sat. `to_fp(d) == to_fp(1.0)`
    // forces d = 0x3f800000; a corrupted model prints #x00000000.
    let out = run_ay_stdin(
        "(set-logic QF_BVFP)
(declare-fun d () (_ BitVec 32))
(assert (fp.eq ((_ to_fp 8 24) d) ((_ to_fp 8 24) (_ bv1065353216 32))))
(assert (not (fp.isNaN ((_ to_fp 8 24) d))))
(check-sat)
(get-model)
(exit)
",
    );
    assert_eq!(first_line(&out), "sat", "stderr: {}", out.stderr);
    assert!(
        out.stdout.contains("#x3f800000"),
        "FP-pinned BV var must keep its value (not be minimized to 0)\nstdout: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("#x00000000"),
        "model must not print the corrupted (minimized-to-0) value\nstdout: {}",
        out.stdout
    );
}

#[test]
#[timeout(30_000)]
fn test_string_backslash_is_literal_smtlib26() {
    // SMT-LIB 2.6: `\` is a LITERAL character (no C-style escapes), so
    // `"a\\b"` has FOUR characters. AY used to decode `\\` -> `\` (three
    // chars), flipping str.len-sensitive verdicts vs z3 — a soundness bug.
    // `(str.len "a\\b") = 4` must be sat (matches z3); `= 3` must be unsat.
    let sat = run_ay_stdin(
        "(set-logic QF_S)\n(assert (= (str.len \"a\\\\b\") 4))\n(check-sat)\n(exit)\n",
    );
    assert_eq!(
        first_line(&sat),
        "sat",
        "str.len(\"a\\\\b\") must be 4 (backslash literal); stderr: {}",
        sat.stderr
    );
    let unsat = run_ay_stdin(
        "(set-logic QF_S)\n(assert (= (str.len \"a\\\\b\") 3))\n(check-sat)\n(exit)\n",
    );
    assert_eq!(
        first_line(&unsat),
        "unsat",
        "str.len(\"a\\\\b\") is not 3; stderr: {}",
        unsat.stderr
    );
}

// ===========================================================================
// Part 18: Comments handling
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_comments_semicolon() {
    let out = run_ay_stdin(
        "; This is a comment
(set-logic QF_LIA) ; inline comment
; Another comment
(declare-const x Int)
(assert (> x 0)) ; x is positive
(check-sat)
; Final comment
(exit)
",
    );
    assert_result(&out, "sat", false, "comments handling");
}

// ===========================================================================
// Part 19: get-info keywords
// ===========================================================================

#[test]
#[timeout(30_000)]
fn test_get_info_all_standard_keywords() {
    // Test several standard SMT-LIB get-info keywords
    for keyword in &[":name", ":version", ":authors"] {
        let input = format!("(get-info {keyword})\n(exit)\n");
        let out = run_ay_stdin(&input);
        // Should not crash; output format may vary
        assert!(
            out.success || !out.stdout.is_empty(),
            "get-info {keyword} should not crash\nstdout: {}\nstderr: {}",
            out.stdout,
            out.stderr
        );
    }
}

// ===========================================================================
// Part 20: Conformance summary covering all test categories
// ===========================================================================

#[test]
#[timeout(120_000)]
fn test_conformance_category_summary() {
    // Quick summary across categories: sorts, commands, incremental, error handling
    let categories: Vec<(&str, Vec<(&str, &str)>)> = vec![
        (
            "Basic Sorts",
            vec![
                (
                    "sat",
                    "(set-logic QF_LIA)(declare-const x Int)(assert (= x 1))(check-sat)(exit)",
                ),
                (
                    "sat",
                    "(set-logic QF_LRA)(declare-const x Real)(assert (= x 1.0))(check-sat)(exit)",
                ),
                (
                    "sat",
                    "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (= x #xFF))(check-sat)(exit)",
                ),
                (
                    "sat",
                    "(set-logic QF_UF)(declare-const p Bool)(assert p)(check-sat)(exit)",
                ),
            ],
        ),
        (
            "Array Sorts",
            vec![
                (
                    "sat",
                    "(set-logic QF_AUFLIA)(declare-const a (Array Int Int))(assert (= (select a 0) 1))(check-sat)(exit)",
                ),
                (
                    "unsat",
                    "(set-logic QF_AUFLIA)(declare-const a (Array Int Int))(assert (= (select (store a 0 1) 0) 2))(check-sat)(exit)",
                ),
            ],
        ),
        (
            "Commands",
            vec![
                (
                    "sat",
                    "(set-info :status sat)(set-logic QF_LIA)(declare-const x Int)(assert (= x 1))(check-sat)(exit)",
                ),
                (
                    "sat",
                    "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(push 1)(assert (< x 0))(check-sat)(pop 1)(check-sat)(exit)",
                ),
            ],
        ),
        (
            "Let Bindings",
            vec![(
                "sat",
                "(set-logic QF_LIA)(declare-const x Int)(assert (let ((y (+ x 1))) (> y 0)))(check-sat)(exit)",
            )],
        ),
        (
            "Boolean Ops",
            vec![
                (
                    "unsat",
                    "(set-logic QF_UF)(declare-const p Bool)(assert (and p (not p)))(check-sat)(exit)",
                ),
                (
                    "unsat",
                    "(set-logic QF_UF)(declare-const p Bool)(declare-const q Bool)(assert (xor p q))(assert (= p q))(check-sat)(exit)",
                ),
            ],
        ),
    ];

    let mut grand_total = 0;
    let mut grand_pass = 0;

    eprintln!("\n=== SMT-LIB 2.6 Full Conformance Category Summary ===");
    eprintln!(
        "{:<20} {:>5} {:>5} {:>8}",
        "Category", "Total", "Pass", "Rate"
    );
    eprintln!("{}", "-".repeat(42));

    for (category, tests) in &categories {
        let mut total = 0;
        let mut pass = 0;

        for (expected, input) in tests {
            let out = run_ay_stdin(input);
            total += 1;
            grand_total += 1;

            // For incremental tests with multiple check-sats, check the last result
            let results = check_sat_results(&out);
            let last = results.last().map(String::as_str).unwrap_or("");

            if last == *expected || last == "unknown" {
                pass += 1;
                grand_pass += 1;
            } else {
                eprintln!(
                    "  {category}: expected {expected}, got '{last}' for: {}",
                    &input[..input.len().min(60)]
                );
            }
        }

        let rate = if total > 0 {
            format!("{:.0}%", (f64::from(pass) / f64::from(total)) * 100.0)
        } else {
            "N/A".to_string()
        };
        eprintln!("{category:<20} {total:>5} {pass:>5} {rate:>8}");
    }

    eprintln!("{}", "-".repeat(42));
    let grand_rate = if grand_total > 0 {
        format!(
            "{:.0}%",
            (f64::from(grand_pass) / f64::from(grand_total)) * 100.0
        )
    } else {
        "N/A".to_string()
    };
    eprintln!(
        "{:<20} {:>5} {:>5} {:>8}",
        "TOTAL", grand_total, grand_pass, grand_rate
    );

    assert!(
        grand_pass > 0,
        "At least some conformance tests should pass"
    );
}

// ===========================================================================
// Part N: HORN predicate-free tautology must be SAT (soundness regression)
// ===========================================================================

/// A HORN assertion with no uninterpreted predicate is a plain constraint, not
/// a reachability query. A *valid* one (`true`, `(and true true)`, a `forall`
/// whose matrix is `true`) must be `sat` — it constrains nothing. The old
/// frontend routed every non-predicate assertion through determine_head(),
/// which maps it to a `true => false` query ⇒ unconditional `unsat`, a wrong
/// verdict vs z3 (`sat`). `(assert false)` must STILL be `unsat`.
#[test]
#[timeout(30_000)]
fn test_horn_predicate_free_tautology_is_sat() {
    for body in &["true", "(and true true)", "(forall ((x Int)) true)"] {
        let input = format!("(set-logic HORN)\n(assert {body})\n(check-sat)\n");
        let out = run_ay_stdin(&input);
        assert_result(
            &out,
            "sat",
            false,
            &format!("HORN tautology (assert {body})"),
        );
    }
    // Guard: a genuine contradiction stays unsat (must not be over-relaxed).
    let out = run_ay_stdin("(set-logic HORN)\n(assert false)\n(check-sat)\n");
    assert_result(&out, "unsat", false, "HORN (assert false)");
}

// ===========================================================================
// Part N+1: get-model head symbol in --z3-mode (drop-in transcript parity)
// ===========================================================================

/// z3 4.15.4 and SMT-LIB 2.6 print `(get-model)` as a bare `( <define-fun>* )`.
/// AY's native form prepends a legacy `model` head symbol that a strict 2.6
/// reader rejects. `--z3-mode` (byte-compatible transcripts) must drop the head;
/// default mode keeps AY's native form (its own model parsers consume it).
#[test]
#[timeout(30_000)]
fn test_get_model_z3_mode_drops_model_head() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt = "(declare-fun x () Int)\n(assert (= x 5))\n(check-sat)\n(get-model)\n";

    let run = |args: &[&str]| -> String {
        let mut child = Command::new(ay_path)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("failed to spawn ay");
        child
            .stdin
            .as_mut()
            .expect("stdin")
            .write_all(smt.as_bytes())
            .expect("write");
        let o = child.wait_with_output().expect("wait");
        String::from_utf8_lossy(&o.stdout).to_string()
    };

    // --z3-mode: the model block opens with a bare `(` on its own line, never
    // `(model`. Filter `c ...` provenance comments the harness prints to stderr
    // (they never reach stdout, but be defensive).
    let z3 = run(&["--z3-mode"]);
    let z3_model_line = z3
        .lines()
        .find(|l| l.trim_start().starts_with('('))
        .unwrap_or("");
    assert_eq!(
        z3_model_line.trim(),
        "(",
        "--z3-mode get-model must open with a bare '(' (z3/SMT-LIB 2.6), got:\n{z3}"
    );
    assert!(
        !z3.contains("(model"),
        "--z3-mode must not emit the legacy `(model` head:\n{z3}"
    );
    // The body must still round-trip the value.
    assert!(
        z3.contains("(define-fun x () Int 5)"),
        "model body must be preserved in --z3-mode:\n{z3}"
    );

    // Default mode retains AY's native `(model ...)` form.
    let native = run(&[]);
    assert!(
        native.contains("(model"),
        "default mode should keep AY's native `(model` head:\n{native}"
    );
}

// ===========================================================================
// Part N+2: mixed Int+Real disjoint-split pre-pass (#mixed-int-real)
// ===========================================================================

/// A mixed Int+Real problem whose Int atoms and Real atoms share no variable
/// (and have no to_real/to_int bridge) is decided by the fail-safe disjoint
/// split: each pure component is solved by its complete pure solver and the
/// results combine (UNSAT via a subset; SAT via a model re-validated against the
/// full formula). These previously returned `unknown` (no Int/Real Nelson-Oppen
/// combination). z3 decides all of them.
#[test]
#[timeout(30_000)]
fn test_mixed_int_real_disjoint_split() {
    // Disjoint SAT — the P0 headline (single `(assert (and ...))`), the
    // two-assertion form, and a 2-Int + 2-Real spread.
    for f in &[
        "(declare-fun x () Int)\n(declare-fun p () Real)\n(assert (and (> x 5) (> p 5.0)))\n(check-sat)\n",
        "(declare-fun x () Int)\n(declare-fun p () Real)\n(assert (> x 5))\n(assert (> p 5.0))\n(check-sat)\n",
        "(declare-fun a () Int)(declare-fun b () Int)(declare-fun p () Real)(declare-fun q () Real)\n(assert (and (> a 5) (< b 0) (> p 1.5) (< q 0.0)))\n(check-sat)\n",
    ] {
        let out = run_ay_stdin(f);
        assert_result(&out, "sat", false, "disjoint mixed Int/Real must be sat");
    }

    // UNSAT via a subset partition (the Int side alone is unsat ⇒ whole unsat).
    let out = run_ay_stdin(
        "(declare-fun x () Int)\n(declare-fun p () Real)\n(assert (and (< x 0) (> x 10) (> p 5.0)))\n(check-sat)\n",
    );
    assert_result(
        &out,
        "unsat",
        false,
        "disjoint mixed Int/Real unsat via subset",
    );

    // The sat verdict must come with a usable model (get-value succeeds).
    let m = run_ay_stdin(
        "(declare-fun x () Int)\n(declare-fun p () Real)\n(assert (and (> x 5) (< p 3.0)))\n(check-sat)\n(get-value (x p))\n",
    );
    assert_eq!(
        first_line(&m),
        "sat",
        "disjoint mixed Int/Real get-value case must be sat\nstdout:\n{}",
        m.stdout
    );

    // A to_real-bridged formula shares a variable across sorts, so the split
    // must NOT fire; the result must still be correct (sat here).
    let br = run_ay_stdin(
        "(declare-fun x () Int)\n(declare-fun p () Real)\n(assert (> (to_real x) p))\n(check-sat)\n",
    );
    assert_result(&br, "sat", true, "to_real-bridged formula stays correct");
}

// ===========================================================================
// Part N+3: (reset) clears the fail-closed error poison
// ===========================================================================

/// A recoverable error drops a problem-contributing command and (soundly)
/// latches later `check-sat` to `unknown`. `(reset)` returns the solver to its
/// initial state per SMT-LIB 2.6, so it MUST clear that poison: a fresh,
/// fully-valid problem built after `(reset)` must decide normally (sat + model),
/// not stay stuck on `unknown` forever. Regression for the "reset does not clear
/// session poison" divergence (z3 answers sat here).
#[test]
#[timeout(30_000)]
fn test_reset_clears_error_poison() {
    let input = "(assert (> nonexistent_symbol 0))\n(check-sat)\n(reset)\n\
                 (declare-const a Int)\n(assert (= a 5))\n(check-sat)\n(get-value (a))\n";
    let out = run_ay_stdin(input);
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected two check-sat results\nstdout:\n{}",
        out.stdout
    );
    // results[0] is the poisoned check-sat (`unknown`) — sound, AY dropped the
    // erroring command and fails closed. results[1] is AFTER `(reset)` and must
    // decide the fresh valid problem.
    assert_eq!(
        results[1], "sat",
        "post-(reset) fresh problem must be `sat`, not latched to `unknown`\nstdout:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("(a 5)"),
        "post-(reset) model must be available (get-value)\nstdout:\n{}",
        out.stdout
    );
}

// ===========================================================================
// Part N+4: str.prefixof/str.suffixof ⟹ str.contains relational lemmas
// ===========================================================================

/// A prefix or suffix is a substring, so `(str.prefixof p x) ⟹ (str.contains
/// x p)` and `(str.suffixof s x) ⟹ (str.contains x s)` are valid theorems. AY
/// now emits them as axioms, so `prefixof p x ∧ ¬contains x p` (and the suffix
/// analogue) refute to `unsat` = z3, where AY previously returned `unknown`
/// (#string-predicate-propagation). The lemmas must NOT over-constrain: a lone
/// prefixof is still `sat`.
#[test]
#[timeout(30_000)]
fn test_string_prefix_suffix_imply_contains() {
    // The gaps that now close (unsat, matching z3).
    for f in &[
        "(declare-const x String)\n(assert (str.prefixof \"ab\" x))\n(assert (not (str.contains x \"ab\")))\n(check-sat)\n",
        "(declare-const x String)\n(assert (str.suffixof \"yz\" x))\n(assert (not (str.contains x \"yz\")))\n(check-sat)\n",
        "(declare-const x String)\n(declare-const p String)\n(assert (str.prefixof p x))\n(assert (not (str.contains x p)))\n(check-sat)\n",
    ] {
        let out = run_ay_stdin(f);
        assert_result(&out, "unsat", false, "prefix/suffix implies contains refutation");
    }
    // Regression: a lone prefixof/suffixof stays sat (the lemma adds a valid
    // implication; it must not force contains false or over-constrain).
    for f in &[
        "(declare-const x String)\n(assert (str.prefixof \"ab\" x))\n(check-sat)\n",
        "(declare-const x String)\n(assert (str.suffixof \"z\" x))\n(check-sat)\n",
        "(declare-const x String)\n(assert (str.prefixof \"ab\" x))\n(assert (str.contains x \"ab\"))\n(check-sat)\n",
    ] {
        let out = run_ay_stdin(f);
        assert_result(&out, "sat", false, "lone prefix/suffix stays sat");
    }
    // QF_SLIA routing: an Int constraint (`str.len`) routes the instance through
    // the string+LIA combined path, which also gets these lemmas. Still `unsat`.
    let out = run_ay_stdin(
        "(declare-const x String)\n(assert (str.prefixof \"ab\" x))\n(assert (not (str.contains x \"ab\")))\n(assert (>= (str.len x) 0))\n(check-sat)\n",
    );
    assert_result(
        &out,
        "unsat",
        false,
        "prefix ⟹ contains fires in the QF_SLIA path too",
    );
}

/// Replace idempotence: `¬(str.contains x s) ⟹ (str.replace x s t) = x` is a
/// valid theorem (replacing a non-occurring needle is a no-op). AY now emits it,
/// so `¬contains x s ∧ replace x s t ≠ x` refutes to `unsat` = z3 (was
/// `unknown`). A replace that genuinely changes the string stays `sat`.
#[test]
#[timeout(30_000)]
fn test_to_real_integrality_bridge() {
    // to_real-integrality rewrites (#to-real-bridge): atoms over the builtin
    // to_real tighten to pure-Int atoms (equivalences), closing the mixed
    // Int/Real N-O gaps AY previously left unknown.
    let d = "(declare-const n Int)\n";
    for (body, expected, why) in [
        (
            "(assert (not (is_int (to_real n))))",
            "unsat",
            "is_int(to_real n) is valid",
        ),
        (
            "(assert (= (to_real n) 2.5))",
            "unsat",
            "to_real image is integral",
        ),
        (
            "(assert (< (to_real n) 5.5))(assert (> (to_real n) 5.0))",
            "unsat",
            "no integer strictly between 5.0 and 5.5",
        ),
        (
            "(assert (<= (to_real n) 5.5))(assert (>= (to_real n) 5.0))",
            "sat",
            "n=5 fits [5.0, 5.5] (boundary twin must stay sat)",
        ),
        (
            "(assert (= (to_real n) 3.0))",
            "sat",
            "integral constant stays sat",
        ),
        (
            "(assert (not (= (to_int (to_real n)) n)))",
            "unsat",
            "to_int(to_real n) = n round-trip",
        ),
        (
            "(assert (< (to_real n) (- 5.0)))(assert (> (to_real n) (- 5.5)))",
            "unsat",
            "negative-range boundary math",
        ),
    ] {
        let out = run_ay_stdin(&format!("{d}{body}\n(check-sat)\n"));
        assert_result(&out, expected, false, why);
    }
    // A user-declared `to_real` shadows the builtin: rewrites must stand down
    // (fail-closed unknown acceptable; a definitive unsat would fabricate
    // semantics for a free function).
    let out = run_ay_stdin(
        "(set-logic ALL)\n(declare-fun to_real (Int) Real)\n(declare-const n Int)\n(assert (= (to_real n) 2.5))\n(check-sat)\n",
    );
    assert_ne!(
        first_line(&out),
        "unsat",
        "shadowed to_real must not be rewritten\nstdout:\n{}",
        out.stdout
    );
}

#[test]
fn test_recursive_functions_over_datatypes() {
    // define-fun-rec over a datatype terminates during macro expansion and
    // DECIDES (was: recursion-depth-1000 error -> unknown). Requires the
    // tester-over-constructor fold incl. nullary constructors (which elaborate
    // to Vars, matched TermId-exactly) so the recursion's ite guard folds and
    // the short-circuit stops the expansion. (#rec-dt-expansion)
    let dt = "(declare-datatypes ((L 0)) (((nil)(cons (hd Int)(tl L)))))\n";
    let len = "(define-fun-rec len ((l L)) Int (ite ((_ is nil) l) 0 (+ 1 (len (tl l)))))\n";
    let out = run_ay_stdin(&format!(
        "{dt}{len}(assert (= (len (cons 1 (cons 2 nil))) 2))\n(check-sat)\n"
    ));
    assert_result(&out, "sat", false, "ite-based rec len over DT decides");
    let out = run_ay_stdin(&format!(
        "{dt}{len}(assert (= (len (cons 1 (cons 2 nil))) 3))\n(check-sat)\n"
    ));
    assert_result(&out, "unsat", false, "wrong len value must be unsat");
    // match-based recursion: needs the match dead-case short-circuit too.
    let mlen =
        "(define-fun-rec mlen ((l L)) Int (match l ((nil 0) ((cons h t) (+ 1 (mlen t))))))\n";
    let out = run_ay_stdin(&format!(
        "{dt}{mlen}(assert (= (mlen (cons 1 (cons 2 nil))) 2))\n(check-sat)\n"
    ));
    assert_result(&out, "sat", false, "match-based rec len over DT decides");
    // Tester over a nullary constructor folds correctly in both polarities.
    let out = run_ay_stdin(&format!(
        "{dt}(assert (not ((_ is nil) nil)))\n(check-sat)\n"
    ));
    assert_result(&out, "unsat", false, "not(is-nil nil) is unsat");
    // Shadowing a constructor name with a binder must NOT fold (TermId-exact
    // guard); fail-closed unknown is acceptable, a wrong sat is not.
    let out = run_ay_stdin(&format!(
        "{dt}(assert (forall ((nil L)) ((_ is nil) nil)))\n(check-sat)\n"
    ));
    assert_ne!(
        first_line(&out),
        "sat",
        "shadowed-constructor tester must never fold to sat\nstdout:\n{}",
        out.stdout
    );
}

#[test]
fn test_string_replace_idempotence() {
    // Gap closes (unsat, matching z3).
    let out = run_ay_stdin(
        "(declare-const x String)\n(assert (not (str.contains x \"a\")))\n(assert (not (= (str.replace x \"a\" \"b\") x)))\n(check-sat)\n",
    );
    assert_result(&out, "unsat", false, "no-occurrence replace is a no-op");
    // Regression: a replace over a haystack that DOES contain the needle can
    // change the string, so this must stay sat (the lemma is vacuous here).
    let out = run_ay_stdin(
        "(declare-const x String)\n(assert (str.contains x \"a\"))\n(assert (not (= (str.replace x \"a\" \"b\") x)))\n(check-sat)\n",
    );
    assert_result(&out, "sat", false, "occurring-needle replace can change x");
}
