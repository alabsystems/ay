// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB 2.6 compliance test suite (#8343).
//!
//! Systematic coverage of every supported logic with SAT/UNSAT formulas,
//! plus command-response format compliance and incremental solving tests.
//! Each test is self-contained with an inline SMT-LIB string.

use crate::smt::{assert_result, check_sat_results, first_line, run_ay_stdin, UnknownPolicy};

include!("smtlib_compliance/core_logics.rs");

include!("smtlib_compliance/theories_and_arrays.rs");

include!("smtlib_compliance/commands.rs");

// ===========================================================================
// Part 3: Incremental solving tests
// ===========================================================================

#[test]
fn test_compliance_incremental_push_pop_result_changes() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 0))
(assert (<= x 10))
(check-sat)
(push 1)
(assert (> x 20))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (= x 5))
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
        5,
        "expected 5 check-sat results, got {:?}\nstdout:\n{}",
        results,
        out.stdout
    );
    // Initial: 0 <= x <= 10 -> sat
    assert_eq!(results[0], "sat", "initial constraints: sat");
    // After push + x > 20 contradicts x <= 10 -> unsat
    assert_eq!(results[1], "unsat", "after push + contradiction: unsat");
    // After pop: back to 0 <= x <= 10 -> sat
    assert_eq!(results[2], "sat", "after pop: sat");
    // After push + x = 5 (consistent with 0 <= x <= 10) -> sat
    assert_eq!(results[3], "sat", "after push + x=5: sat");
    // After pop: back to 0 <= x <= 10 -> sat
    assert_eq!(results[4], "sat", "after second pop: sat");
}

#[test]
fn test_compliance_incremental_nested_push_pop() {
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0))
(push 1)
(assert (= x 5))
(push 1)
(assert (= y 10))
(assert (> x y))
(check-sat)
(pop 1)
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
        3,
        "expected 3 check-sat results, got {results:?}"
    );
    // x=5, y=10, x>y -> unsat
    assert_eq!(results[0], "unsat", "x=5 and x>10: unsat");
    // After inner pop: x=5 -> sat
    assert_eq!(results[1], "sat", "after inner pop (x=5): sat");
    // After outer pop: x>=0 -> sat
    assert_eq!(results[2], "sat", "after outer pop (x>=0): sat");
}

#[test]
fn test_compliance_incremental_push_n_pop_n() {
    // Test push/pop with N > 1 (batch push/pop).
    let out = run_ay_stdin(
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 0))
(push 2)
(assert (= x 5))
(push 1)
(assert (< x 0))
(check-sat)
(pop 3)
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got {results:?}"
    );
    // x >= 0 and x = 5 and x < 0 -> unsat
    assert_eq!(results[0], "unsat", "all pushed: unsat");
    // After pop 3: back to just x >= 0 -> sat
    assert_eq!(results[1], "sat", "after pop 3: sat");
}

// ---- Incremental with BV logic -------------------------------------------

#[test]
fn test_compliance_incremental_bv_push_pop() {
    let out = run_ay_stdin(
        "(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvuge x #x10))
(check-sat)
(push 1)
(assert (bvult x #x10))
(check-sat)
(pop 1)
(check-sat)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    let results = check_sat_results(&out);
    assert_eq!(results.len(), 3, "expected 3 results, got {results:?}");
    assert_eq!(results[0], "sat", "x >= 0x10: sat");
    assert_eq!(results[1], "unsat", "x >= 0x10 and x < 0x10: unsat");
    assert_eq!(results[2], "sat", "after pop (x >= 0x10): sat");
}

// ===========================================================================
// Part 4: Multi-check-sat and model extraction per logic
// ===========================================================================

#[test]
fn test_compliance_qf_lia_get_model() {
    let out = run_ay_stdin(
        "(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 10))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
(get-model)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert_eq!(first_line(&out), "sat", "expected sat");
    assert!(
        out.stdout.contains("define-fun"),
        "model should contain define-fun, got:\n{}",
        out.stdout
    );
}

#[test]
fn test_compliance_qf_bv_get_model() {
    let out = run_ay_stdin(
        "(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #xAB))
(check-sat)
(get-model)
(exit)
",
    );
    assert!(out.success, "ay should exit successfully");
    assert_eq!(first_line(&out), "sat", "expected sat");
    assert!(
        out.stdout.contains("define-fun"),
        "model should contain define-fun, got:\n{}",
        out.stdout
    );
}

// ===========================================================================
// Part 5: Logic acceptance (logic string is recognized, no parse error)
// ===========================================================================

/// Test that all documented logic strings are accepted without error.
/// We do not require a specific SAT/UNSAT result here -- just that the
/// solver does not reject the logic.
#[test]
fn test_compliance_all_logic_strings_accepted() {
    let logics = [
        "QF_UF",
        "QF_LIA",
        "QF_LRA",
        "QF_LIRA",
        "QF_BV",
        "QF_ABV",
        "QF_AUFBV",
        "QF_AUFBVLIA",
        "QF_UFBV",
        "QF_UFBVLIA",
        "QF_UFLIA",
        "QF_UFLRA",
        "QF_AUFLRA",
        "QF_AUFLIA",
        "QF_NIA",
        "QF_NRA",
        "QF_FP",
        "QF_BVFP",
        "QF_S",
        "QF_SLIA",
        "QF_DT",
        "QF_UFDT",
        "QF_AX",
        "QF_ALIA",
        "QF_NIRA",
        "QF_AUFLIRA",
        "QF_UFNIA",
        "QF_UFNRA",
        "QF_UFNIRA",
        "QF_SNIA",
        "QF_SEQ",
        "QF_SEQLIA",
        "ALL",
    ];

    for logic in &logics {
        let input = format!("(set-logic {logic})\n(check-sat)\n(exit)\n");
        let out = run_ay_stdin(&input);
        assert!(
            out.success,
            "ay should accept logic '{logic}' without crashing\nstdout:\n{}\nstderr:\n{}",
            out.stdout, out.stderr
        );
        let fl = first_line(&out);
        assert!(
            fl == "sat" || fl == "unsat" || fl == "unknown",
            "logic '{logic}': check-sat should return sat/unsat/unknown, got '{fl}'\nstderr:\n{}",
            out.stderr
        );
    }
}

/// Test that quantified logic strings are also accepted.
#[test]
fn test_compliance_quantified_logic_strings_accepted() {
    let logics = [
        "LIA", "LRA", "NIA", "NRA", "NIRA", "UF", "UFLIA", "UFLRA", "UFNIA", "UFNRA", "UFNIRA",
        "BV", "UFBV", "AUFLIA", "AUFLRA", "LIRA", "AUFLIRA", "UFDT", "UFDTLIA", "UFDTNIA",
    ];

    for logic in &logics {
        let input = format!("(set-logic {logic})\n(check-sat)\n(exit)\n");
        let out = run_ay_stdin(&input);
        assert!(
            out.success,
            "ay should accept quantified logic '{logic}' without crashing\nstdout:\n{}\nstderr:\n{}",
            out.stdout, out.stderr
        );
        let fl = first_line(&out);
        assert!(
            fl == "sat" || fl == "unsat" || fl == "unknown",
            "logic '{logic}': check-sat should return sat/unsat/unknown, got '{fl}'\nstderr:\n{}",
            out.stderr
        );
    }
}
