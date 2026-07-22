// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Round-trip parser tests for ay-bindings (#1840).
//!
//! Validates that SMT-LIB2 and CHC programs emitted by ay-bindings can be
//! parsed by AY's own parsers. This catches drift between emitters and parsers.

use ay_bindings::{AYProgram, Expr, Sort};
use ntest::timeout;

// ============================================================================
// SMT-LIB2 round-trip tests (via ay-frontend)
// ============================================================================

/// Basic SMT program: set-logic, declare-const, assert, check-sat.
#[test]
#[timeout(5000)]
fn test_smt_roundtrip_basic_qf_lia() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");

    let x = program.declare_const("x", Sort::int());
    let y = program.declare_const("y", Sort::int());

    // x + y > 0
    let sum = x.int_add(y);
    let zero = Expr::int_const(0);
    program.assert(sum.int_gt(zero));

    program.check_sat();

    let smt_text = program.to_string();

    // Parse with ay-frontend
    let commands = ay_frontend::parse(&smt_text).expect("ay-frontend should parse emitted SMT");

    // Basic structure checks
    assert!(
        commands.len() >= 4,
        "Expected at least 4 commands (set-logic, 2 declare-const, assert, check-sat)"
    );

    // Find set-logic command
    let has_set_logic = commands
        .iter()
        .any(|cmd| matches!(cmd, ay_frontend::Command::SetLogic(logic) if logic == "QF_LIA"));
    assert!(has_set_logic, "Expected SetLogic(QF_LIA) command");

    // Find check-sat command
    let has_check_sat = commands
        .iter()
        .any(|cmd| matches!(cmd, ay_frontend::Command::CheckSat));
    assert!(has_check_sat, "Expected CheckSat command");
}

/// SMT program with bitvectors.
#[test]
#[timeout(5000)]
fn test_smt_roundtrip_qf_bv() {
    let mut program = AYProgram::qf_bv();
    program.produce_models();

    let x = program.declare_const("x", Sort::bv32());
    let y = program.declare_const("y", Sort::bv32());

    // x + y == 100
    let sum = x.bvadd(y);
    let hundred = Expr::bitvec_const(100i32, 32);
    program.assert(sum.eq(hundred));

    program.check_sat();
    program.get_model();

    let smt_text = program.to_string();

    // Parse with ay-frontend
    let commands = ay_frontend::parse(&smt_text).expect("ay-frontend should parse QF_BV program");

    // Verify structure
    assert!(!commands.is_empty(), "Should have parsed commands");

    // Check for QF_BV logic
    let has_qf_bv = commands
        .iter()
        .any(|cmd| matches!(cmd, ay_frontend::Command::SetLogic(logic) if logic == "QF_BV"));
    assert!(has_qf_bv, "Expected SetLogic(QF_BV)");
}

/// SMT program with arrays.
#[test]
#[timeout(5000)]
fn test_smt_roundtrip_qf_aufbv() {
    let mut program = AYProgram::qf_aufbv();

    // Array from Int to Bool
    let arr = program.declare_const("arr", Sort::array(Sort::int(), Sort::bool()));

    // select(arr, 0)
    let zero = Expr::int_const(0);
    let sel = arr.select(zero);
    program.assert(sel);

    program.check_sat();

    let smt_text = program.to_string();

    // Parse with ay-frontend
    let commands =
        ay_frontend::parse(&smt_text).expect("ay-frontend should parse QF_AUFBV program");
    assert!(!commands.is_empty(), "Should have parsed commands");
}

/// SMT program with special symbol names that need quoting.
#[test]
#[timeout(5000)]
fn test_smt_roundtrip_quoted_symbols() {
    let mut program = AYProgram::qf_bv();

    // Variable with :: in name (needs quoting)
    let x = program.declare_const("test_func::local_0", Sort::bv32());
    let y = program.declare_const("another::symbol", Sort::bv32());

    program.assert(x.eq(y));
    program.check_sat();

    let smt_text = program.to_string();

    // Verify symbols are quoted
    assert!(
        smt_text.contains("|test_func::local_0|"),
        "Symbol with :: should be quoted"
    );
    assert!(
        smt_text.contains("|another::symbol|"),
        "Symbol with :: should be quoted"
    );

    // Parse with ay-frontend
    let commands = ay_frontend::parse(&smt_text).expect("ay-frontend should parse quoted symbols");
    assert!(!commands.is_empty(), "Should have parsed commands");
}

// ============================================================================
// CHC round-trip tests (via ay-chc)
// ============================================================================

/// Basic CHC program: declare-rel, rule, query.
#[test]
#[timeout(5000)]
fn test_chc_roundtrip_basic() {
    let mut program = AYProgram::horn();

    // Declare predicate Inv : Int -> Bool
    program.declare_rel("Inv", vec![Sort::int()]);

    // For CHC, we need to emit using the CHC-specific format
    // ay-bindings emits HORN logic programs that can be parsed by ay-chc

    let output = program.to_string();

    // Verify it has HORN logic
    assert!(
        output.contains("(set-logic HORN)"),
        "CHC program should have HORN logic"
    );
    assert!(
        output.contains("(declare-rel Inv (Int))"),
        "Should declare Inv predicate"
    );

    // Parse with ay-chc parser
    let result = ay_chc::ChcParser::parse(&output);
    assert!(
        result.is_ok(),
        "ay-chc should parse emitted CHC: {:?}",
        result.err()
    );

    let problem = result.unwrap();
    assert!(
        problem.predicates().iter().any(|p| p.name == "Inv"),
        "Should have Inv predicate"
    );
}

/// CHC parser test with rules and query.
///
/// NOTE: This is a parser-only test, not a true round-trip test.
/// ay-bindings' rule() and query() methods emit simplified constraints
/// that differ from the standard CHC format. We use raw SMT-LIB text
/// to test ay-chc's parser on complete CHC programs.
#[test]
#[timeout(5000)]
fn test_chc_roundtrip_with_rules() {
    let chc_text = r#"
(set-logic HORN)
(declare-rel Inv (Int))
(declare-var x Int)
(rule (=> (= x 0) (Inv x)))
(rule (=> (and (Inv x) (< x 10)) (Inv (+ x 1))))
(query (and (Inv x) (< x 0)))
"#;

    // Parse with ay-chc parser
    let result = ay_chc::ChcParser::parse(chc_text);
    assert!(
        result.is_ok(),
        "ay-chc should parse CHC program: {:?}",
        result.err()
    );

    let problem = result.unwrap();
    assert_eq!(problem.predicates().len(), 1, "Should have 1 predicate");
    assert!(
        problem.clauses().len() >= 2,
        "Should have at least 2 clauses"
    );
}

/// CHC parser test with multiple predicates.
///
/// NOTE: Parser-only test (see test_chc_roundtrip_with_rules comment).
#[test]
#[timeout(5000)]
fn test_chc_roundtrip_multiple_predicates() {
    let chc_text = r#"
(set-logic HORN)
(declare-rel P (Int))
(declare-rel Q (Int Int))
(declare-var x Int)
(declare-var y Int)
(rule (=> (= x 0) (P x)))
(rule (=> (P x) (Q x x)))
(query (and (Q x y) (not (= x y))))
"#;

    let result = ay_chc::ChcParser::parse(chc_text);
    assert!(
        result.is_ok(),
        "ay-chc should parse multi-predicate CHC: {:?}",
        result.err()
    );

    let problem = result.unwrap();
    assert_eq!(
        problem.predicates().len(),
        2,
        "Should have 2 predicates (P and Q)"
    );
}

// ============================================================================
// Edge cases and error handling
// ============================================================================

/// Empty program should be parseable.
///
/// AYProgram::new() produces an empty program with no commands.
/// This validates that the parser handles empty input correctly.
#[test]
#[timeout(5000)]
fn test_smt_roundtrip_empty_program() {
    let program = AYProgram::new();
    let smt_text = program.to_string();

    // Empty program is valid SMT-LIB (no commands)
    let commands = ay_frontend::parse(&smt_text).expect("Empty program should parse");
    // AYProgram::new() produces truly empty output (no set-logic, no set-option)
    assert!(
        commands.is_empty(),
        "Empty program should produce no commands, got: {commands:?}"
    );
}

/// Program with only check-sat.
#[test]
#[timeout(5000)]
fn test_smt_roundtrip_only_check_sat() {
    let mut program = AYProgram::qf_bv();
    program.check_sat();

    let smt_text = program.to_string();
    let commands = ay_frontend::parse(&smt_text).expect("check-sat only program should parse");
    assert!(commands
        .iter()
        .any(|c| matches!(c, ay_frontend::Command::CheckSat)));
}

/// SMT program with Real sort (QF_LRA logic).
///
/// Self-audit finding: Original tests only covered Int and BitVec sorts.
/// This test adds coverage for Real arithmetic.
#[test]
#[timeout(5000)]
fn test_smt_roundtrip_qf_lra() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");

    let x = program.declare_const("x", Sort::real());
    let y = program.declare_const("y", Sort::real());

    // x + y > 0
    let sum = x.real_add(y);
    let zero = Expr::real_const(0);
    program.assert(sum.real_gt(zero));

    program.check_sat();

    let smt_text = program.to_string();

    // Parse with ay-frontend
    let commands = ay_frontend::parse(&smt_text).expect("ay-frontend should parse QF_LRA program");

    // Verify structure
    assert!(!commands.is_empty(), "Should have parsed commands");

    // Check for QF_LRA logic
    let has_qf_lra = commands
        .iter()
        .any(|cmd| matches!(cmd, ay_frontend::Command::SetLogic(logic) if logic == "QF_LRA"));
    assert!(has_qf_lra, "Expected SetLogic(QF_LRA)");
}
