// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Tests for additional global constraint encodings (global_cardinality,
// increasing/decreasing, member, nvalue, lex, bin_packing, subcircuit,
// disjunctive). Split from tests_globals.rs for file-size compliance.

use super::*;

fn translate_fzn(input: &str) -> TranslationResult {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect("translate failed")
}

fn translate_fzn_err(input: &str) -> TranslateError {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect_err("translation should fail")
}

fn solve_fzn_verdict(input: &str) -> String {
    let result = translate_fzn(input);
    let commands = ay_frontend::parse(&result.smtlib).expect("SMT-LIB should parse");
    let mut executor = ay_dpll::Executor::new();
    for command in &commands {
        match executor.execute(command) {
            Ok(Some(output)) if matches!(output.trim(), "sat" | "unsat" | "unknown") => {
                return output.trim().to_string();
            }
            Ok(_) => {}
            Err(error) => panic!("SMT execution failed before a verdict: {error}"),
        }
    }
    panic!("translated model produced no solver verdict")
}

// --- Global: global_cardinality ---

#[test]
fn test_global_cardinality() {
    let r = translate_fzn(
        "array [1..3] of var 1..3: x;\n\
         array [1..2] of var 0..3: c;\n\
         constraint fzn_global_cardinality(x, [1, 2], c);\n\
         solve satisfy;\n",
    );
    // Count of value 1 in x = c_1
    assert!(r.smtlib.contains("(ite (= x_1 1) 1 0)"));
    assert!(r.smtlib.contains("(ite (= x_2 1) 1 0)"));
    assert!(r.smtlib.contains("(ite (= x_3 1) 1 0)"));
    assert!(r.smtlib.contains("(assert (= c_1"));
    // Count of value 2 in x = c_2
    assert!(r.smtlib.contains("(ite (= x_1 2) 1 0)"));
    assert!(r.smtlib.contains("(assert (= c_2"));
}

#[test]
fn test_global_cardinality_closed() {
    let r = translate_fzn(
        "array [1..2] of var 1..3: x;\n\
         array [1..2] of var 0..2: c;\n\
         constraint fzn_global_cardinality_closed(x, [1, 2], c);\n\
         solve satisfy;\n",
    );
    // Closed: x values must be in {1, 2}
    assert!(r.smtlib.contains("(assert (or (= x_1 1) (= x_1 2)))"));
    assert!(r.smtlib.contains("(assert (or (= x_2 1) (= x_2 2)))"));
}

#[test]
fn test_global_cardinality_rejects_cover_count_length_mismatch() {
    let err = translate_fzn_err(
        "var 1..2: x;\n\
         var 0..1: c;\n\
         constraint fzn_global_cardinality([x], [1, 2], [c]);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref msg)
            if msg.contains("cover and counts length mismatch")),
        "expected cover/count length mismatch, got: {err}"
    );
}

// --- Global: increasing_int ---

#[test]
fn test_increasing_int() {
    let r = translate_fzn(
        "array [1..3] of var 1..10: x;\n\
         constraint fzn_increasing_int(x);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (<= x_1 x_2))"));
    assert!(r.smtlib.contains("(assert (<= x_2 x_3))"));
}

// --- Global: decreasing_int ---

#[test]
fn test_decreasing_int() {
    let r = translate_fzn(
        "array [1..3] of var 1..10: x;\n\
         constraint fzn_decreasing_int(x);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (>= x_1 x_2))"));
    assert!(r.smtlib.contains("(assert (>= x_2 x_3))"));
}

// --- Global: member_int ---

#[test]
fn test_member_int() {
    let r = translate_fzn(
        "array [1..3] of var 1..5: x;\n\
         var 1..5: y;\n\
         constraint fzn_member_int(x, y);\n\
         solve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (or (= x_1 y) (= x_2 y) (= x_3 y)))"));
}

#[test]
fn test_member_int_empty_array() {
    let r = translate_fzn(
        "array [1..0] of var 1..5: x;\n\
         var 1..5: y;\n\
         constraint member_int(x, y);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert false)"));
}

// --- Global: member_bool (proof_coverage: previously untested) ---

#[test]
fn test_member_bool() {
    let r = translate_fzn(
        "array [1..2] of var bool: x;\n\
         var bool: y;\n\
         constraint member_bool(x, y);\n\
         solve satisfy;\n",
    );
    // member_bool delegates to member_int, should produce or-of-equalities
    assert!(r.smtlib.contains("(assert (or (= x_1 y) (= x_2 y)))"));
}

// --- Global: nvalue ---

#[test]
fn test_nvalue() {
    let r = translate_fzn(
        "var 0..3: n;\n\
         array [1..3] of var 1..5: x;\n\
         constraint fzn_nvalue(n, x);\n\
         solve satisfy;\n",
    );
    // Should declare indicator booleans
    assert!(r.smtlib.contains("(declare-const _nv"));
    // First indicator is always true
    assert!(r.smtlib.contains("(assert _nv0_0)"));
    // n = sum of indicators
    assert!(r.smtlib.contains("(assert (= n"));
}

#[test]
fn test_nvalue_empty_array_is_zero() {
    let r = translate_fzn(
        "var 0..1: n;\n\
         constraint fzn_nvalue(n, []);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= n 0))"));
}

// --- Global: lex_less_int ---

#[test]
fn test_lex_less_int() {
    let r = translate_fzn(
        "array [1..2] of var 1..3: x;\n\
         array [1..2] of var 1..3: y;\n\
         constraint fzn_lex_less_int(x, y);\n\
         solve satisfy;\n",
    );
    // x[1] < y[1] or (x[1] = y[1] and x[2] < y[2])
    assert!(r.smtlib.contains("(< x_1 y_1)"));
    assert!(r.smtlib.contains("(and (= x_1 y_1) (< x_2 y_2))"));
}

// --- Global: lex_lesseq_int ---

#[test]
fn test_lex_lesseq_int() {
    let r = translate_fzn(
        "array [1..2] of var 1..3: x;\n\
         array [1..2] of var 1..3: y;\n\
         constraint fzn_lex_lesseq_int(x, y);\n\
         solve satisfy;\n",
    );
    // Same as lex_less but also allows all-equal
    assert!(r.smtlib.contains("(< x_1 y_1)"));
    assert!(r.smtlib.contains("(and (= x_1 y_1) (< x_2 y_2))"));
    assert!(r.smtlib.contains("(and (= x_1 y_1) (= x_2 y_2))"));
}

#[test]
fn test_lex_less_equal_prefix_uses_array_length() {
    let shorter = translate_fzn(
        "array [1..2] of var int: x;\n\
         array [1..3] of var int: y;\n\
         constraint fzn_lex_less_int(x, y);\n\
         solve satisfy;\n",
    );
    assert!(shorter.smtlib.contains("(and (= x_1 y_1) (= x_2 y_2))"));

    let longer = translate_fzn(
        "array [1..3] of var int: x;\n\
         array [1..2] of var int: y;\n\
         constraint fzn_lex_lesseq_int(x, y);\n\
         solve satisfy;\n",
    );
    assert!(!longer.smtlib.contains("(and (= x_1 y_1) (= x_2 y_2))"));
}

#[test]
fn test_lex_less_empty_prefix_length_semantics() {
    assert_eq!(
        solve_fzn_verdict("constraint fzn_lex_less_int([], [1]);\nsolve satisfy;\n"),
        "sat"
    );
    assert_eq!(
        solve_fzn_verdict("constraint fzn_lex_lesseq_int([1], []);\nsolve satisfy;\n"),
        "unsat"
    );
}

// --- Global: bin_packing_load ---

#[test]
fn test_bin_packing_load() {
    let r = translate_fzn(
        "array [1..2] of var 0..10: load;\n\
         array [1..3] of var 1..2: bin;\n\
         array [1..3] of int: size = [3, 5, 2];\n\
         constraint fzn_bin_packing_load(load, bin, size);\n\
         solve satisfy;\n",
    );
    // load[1] = sum of size[i] where bin[i] = 1
    assert!(r.smtlib.contains("(ite (= bin_1 1) 3 0)"));
    assert!(r.smtlib.contains("(ite (= bin_2 1) 5 0)"));
    assert!(r.smtlib.contains("(ite (= bin_3 1) 2 0)"));
    assert!(r.smtlib.contains("(assert (= load_1"));
    // load[2] = sum of size[i] where bin[i] = 2
    assert!(r.smtlib.contains("(ite (= bin_1 2) 3 0)"));
    assert!(r.smtlib.contains("(assert (= load_2"));
}

#[test]
fn test_bin_packing_load_uses_declared_load_indices_and_guards_bins() {
    let r = translate_fzn(
        "array [4..5] of var int: load;\n\
         array [1..2] of var int: bin;\n\
         array [1..2] of int: size = [3, 5];\n\
         constraint fzn_bin_packing_load(load, bin, size);\n\
         solve satisfy;\n",
    );

    assert!(r
        .smtlib
        .contains("(assert (and (>= bin_1 4) (<= bin_1 5)))"));
    assert!(r
        .smtlib
        .contains("(assert (and (>= bin_2 4) (<= bin_2 5)))"));
    assert!(r.smtlib.contains("(ite (= bin_1 4) 3 0)"));
    assert!(r.smtlib.contains("(ite (= bin_1 5) 3 0)"));
}

#[test]
fn test_bin_packing_load_rejects_out_of_range_bin_assignment() {
    assert_eq!(
        solve_fzn_verdict(
            "array [4..5] of var int: load;\n\
             var int: bin;\n\
             constraint fzn_bin_packing_load(load, [bin], [2]);\n\
             constraint int_eq(bin, 3);\n\
             solve satisfy;\n"
        ),
        "unsat"
    );
}

// --- Global: subcircuit ---

#[test]
fn test_subcircuit() {
    let r = translate_fzn(
        "array [1..3] of var 1..3: succ;\n\
         constraint fzn_subcircuit(succ);\n\
         solve satisfy;\n",
    );
    // All-different pairwise
    assert!(r.smtlib.contains("(assert (not (= succ_1 succ_2)))"));
    // Active tracking: succ[i] != i means active
    assert!(r.smtlib.contains("(declare-const _sc_act"));
    assert!(r.smtlib.contains("(not (= succ_1 1))"));
    // Selected-root rank variables
    assert!(r.smtlib.contains("(declare-const _sc_root"));
    assert!(r.smtlib.contains("(declare-const _sc_ord"));
}

#[test]
fn test_subcircuit_uses_declared_indices_and_ordinal_auxiliary_names() {
    let r = translate_fzn(
        "array [-1..1] of var int: succ;\n\
         constraint fzn_subcircuit(succ);\n\
         solve satisfy;\n",
    );

    assert!(r
        .smtlib
        .contains("(assert (and (>= succ_-1 (- 1)) (<= succ_-1 1)))"));
    assert!(r.smtlib.contains("(not (= succ_-1 (- 1)))"));
    assert!(r.smtlib.contains("(declare-const _sc_act0_0 Bool)"));
    assert!(!r.smtlib.contains("_sc_act0_-1"));
}

#[test]
fn test_subcircuit_accepts_cycle_excluding_first_declared_node() {
    assert_eq!(
        solve_fzn_verdict(
            "array [4..6] of var 4..6: succ;\n\
             constraint int_eq(succ[4], 4);\n\
             constraint int_eq(succ[5], 6);\n\
             constraint int_eq(succ[6], 5);\n\
             constraint fzn_subcircuit(succ);\n\
             solve satisfy;\n"
        ),
        "sat"
    );
}

#[test]
fn test_subcircuit_rejects_out_of_range_successor_and_multiple_cycles() {
    assert_eq!(
        solve_fzn_verdict(
            "array [4..6] of var int: succ;\n\
             constraint int_eq(succ[4], 3);\n\
             constraint fzn_subcircuit(succ);\n\
             solve satisfy;\n"
        ),
        "unsat"
    );
    assert_eq!(
        solve_fzn_verdict(
            "array [4..7] of var 4..7: succ;\n\
             constraint int_eq(succ[4], 5);\n\
             constraint int_eq(succ[5], 4);\n\
             constraint int_eq(succ[6], 7);\n\
             constraint int_eq(succ[7], 6);\n\
             constraint fzn_subcircuit(succ);\n\
             solve satisfy;\n"
        ),
        "unsat"
    );
}

// --- Global: disjunctive ---

#[test]
fn test_disjunctive() {
    let r = translate_fzn(
        "array [1..2] of var 0..10: s;\n\
         array [1..2] of int: d = [3, 5];\n\
         constraint fzn_disjunctive(s, d);\n\
         solve satisfy;\n",
    );
    // s[1]+d[1] <= s[2] or s[2]+d[2] <= s[1]
    assert!(r.smtlib.contains("(<= (+ s_1 3) s_2)"));
    assert!(r.smtlib.contains("(<= (+ s_2 5) s_1)"));
}

#[test]
fn test_disjunctive_zero_duration_differs_from_strict() {
    let declarations = "array [1..2] of var 0..10: starts = [5, 0];\n\
                        array [1..2] of var 0..10: durations = [0, 10];\n";
    assert_eq!(
        solve_fzn_verdict(&format!(
            "{declarations}constraint disjunctive(starts, durations);\nsolve satisfy;\n"
        )),
        "sat"
    );
    assert_eq!(
        solve_fzn_verdict(&format!(
            "{declarations}constraint disjunctive_strict(starts, durations);\nsolve satisfy;\n"
        )),
        "unsat"
    );
}

#[test]
fn test_global_dispatch_rejects_bad_unary_arity() {
    for constraint in [
        "increasing_int()",
        "increasing_int([], [])",
        "subcircuit()",
        "subcircuit([], [])",
    ] {
        let err = translate_fzn_err(&format!("constraint {constraint};\nsolve satisfy;\n"));
        assert!(
            matches!(err, TranslateError::WrongArgCount { expected: 1, .. }),
            "unexpected error for {constraint}: {err}"
        );
    }
}

// --- Global: count variants ---

fn count_x_eq_2_sum() -> &'static str {
    "(+ (ite (= x_1 2) 1 0) (ite (= x_2 2) 1 0) (ite (= x_3 2) 1 0))"
}

#[test]
fn test_count_neq() {
    let r = translate_fzn(
        "array [1..3] of var 1..5: x;\nvar int: c;\n\
         constraint count_neq(x, 2, c);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (distinct"));
    assert!(r.smtlib.contains("(ite (= x_1 2) 1 0)"));
}

#[test]
fn test_count_leq() {
    let r = translate_fzn(
        "array [1..3] of var 1..5: x;\nvar int: c;\n\
         constraint count_leq(x, 2, c);\nsolve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains(&format!("(assert (<= c {}))", count_x_eq_2_sum())));
    assert!(r.smtlib.contains("(ite (= x_2 2) 1 0)"));
}

#[test]
fn test_count_geq() {
    let r = translate_fzn(
        "array [1..3] of var 1..5: x;\nvar int: c;\n\
         constraint count_geq(x, 2, c);\nsolve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains(&format!("(assert (>= c {}))", count_x_eq_2_sum())));
}

#[test]
fn test_count_lt() {
    let r = translate_fzn(
        "array [1..3] of var 1..5: x;\nvar int: c;\n\
         constraint count_lt(x, 2, c);\nsolve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains(&format!("(assert (< c {}))", count_x_eq_2_sum())));
}

#[test]
fn test_count_gt() {
    let r = translate_fzn(
        "array [1..3] of var 1..5: x;\nvar int: c;\n\
         constraint count_gt(x, 2, c);\nsolve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains(&format!("(assert (> c {}))", count_x_eq_2_sum())));
}

// --- Global: among ---

#[test]
fn test_among() {
    let r = translate_fzn(
        "var int: n;\narray [1..3] of var 1..5: x;\n\
         constraint among(n, x, {2, 4});\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= n"));
    assert!(r.smtlib.contains("(or (= x_1 2) (= x_1 4))"));
}

#[test]
fn test_among_single_value() {
    let r = translate_fzn(
        "var int: n;\narray [1..2] of var 1..5: x;\n\
         constraint among(n, x, {3});\nsolve satisfy;\n",
    );
    // Single value in set should use direct equality
    assert!(r.smtlib.contains("(ite (= x_1 3) 1 0)"));
}

// --- Global: value_precede_int ---

#[test]
fn test_value_precede_int() {
    let r = translate_fzn(
        "array [1..3] of var 1..4: x;\n\
         constraint value_precede_int(1, 3, x);\nsolve satisfy;\n",
    );
    // Should declare seen-s tracking variables
    assert!(r.smtlib.contains("(declare-const _vp_s"));
    // First occurrence of t (=3) must be preceded by s (=1)
    assert!(r.smtlib.contains("(assert (not (= x_1 3)))"));
    assert!(r.smtlib.contains("(=> (= x_2 3) _vp_s0_0)"));
    assert!(r.smtlib.contains("(=> (= x_3 3) _vp_s0_1)"));
}

#[test]
fn test_value_precede_chain_encodes_each_adjacent_cover_pair() {
    let r = translate_fzn(
        "array [1..3] of var 1..3: x;\n\
         constraint value_precede_chain_int([1, 2, 3], x);\n\
         solve satisfy;\n",
    );

    assert!(r.smtlib.contains("(assert (not (= x_1 2)))"));
    assert!(r.smtlib.contains("(assert (not (= x_1 3)))"));
    assert!(r.smtlib.contains("(=> (= x_2 2) _vp_s0_0)"));
    assert!(r.smtlib.contains("(=> (= x_2 3) _vp_s1_0)"));
    assert_eq!(r.smtlib.matches("(declare-const _vp_s").count(), 6);
}

#[test]
fn test_value_precede_chain_rejects_missing_predecessor() {
    assert_eq!(
        solve_fzn_verdict(
            "array [1..2] of var 1..3: x = [1, 3];\n\
             constraint value_precede_chain_int([1, 2, 3], x);\n\
             solve satisfy;\n"
        ),
        "unsat"
    );
    assert_eq!(
        solve_fzn_verdict(
            "array [1..3] of var 1..3: x = [1, 2, 3];\n\
             constraint value_precede_chain_int([1, 2, 3], x);\n\
             solve satisfy;\n"
        ),
        "sat"
    );
}

#[test]
fn test_value_precede_requires_a_strictly_earlier_equal_value() {
    assert_eq!(
        solve_fzn_verdict(
            "var 1..2: x = 2;\n\
             constraint value_precede_int(2, 2, [x]);\n\
             solve satisfy;\n"
        ),
        "unsat"
    );
    assert_eq!(
        solve_fzn_verdict(
            "var 1..2: x = 1;\n\
             constraint value_precede_int(2, 2, [x]);\n\
             solve satisfy;\n"
        ),
        "sat"
    );
}

#[test]
fn test_value_precede_chain_duplicate_cover_is_not_tautological() {
    assert_eq!(
        solve_fzn_verdict(
            "var 1..2: x = 1;\n\
             constraint value_precede_chain_int([1, 1], [x]);\n\
             solve satisfy;\n"
        ),
        "unsat"
    );
}
