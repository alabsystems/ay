// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Tests for global constraint encodings (table, count, circuit, cumulative,
// inverse, diffn, regular) and integration-level translation tests.
// Extracted from tests.rs to stay under 1000-line limit.

use super::*;

fn translate_fzn(input: &str) -> TranslationResult {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect("translate failed")
}

fn translate_fzn_err(input: &str) -> TranslateError {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect_err("translation should fail")
}

// --- Global: table_int ---

#[test]
fn test_table_int() {
    let r = translate_fzn(
        "array [1..2] of var 1..3: x;\n\
         constraint table_int(x, [1, 2, 2, 3, 3, 1]);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (or"));
    assert!(r.smtlib.contains("(and (= x_1 1) (= x_2 2))"));
    assert!(r.smtlib.contains("(and (= x_1 2) (= x_2 3))"));
    assert!(r.smtlib.contains("(and (= x_1 3) (= x_2 1))"));
}

#[test]
fn test_table_int_single_tuple() {
    let r = translate_fzn(
        "array [1..2] of var 1..3: x;\n\
         constraint table_int(x, [1, 2]);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (and (= x_1 1) (= x_2 2)))"));
}

#[test]
fn test_table_int_with_param() {
    let r = translate_fzn(
        "array [1..4] of int: tuples = [1, 2, 3, 4];\n\
         array [1..2] of var 1..4: x;\n\
         constraint table_int(x, tuples);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(and (= x_1 1) (= x_2 2))"));
    assert!(r.smtlib.contains("(and (= x_1 3) (= x_2 4))"));
}

#[test]
fn test_table_int_rejects_tuple_length_mismatch() {
    let err = translate_fzn_err(
        "var 1..3: x;\n\
         var 1..3: y;\n\
         constraint table_int([x, y], [1, 2, 3]);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref msg)
            if msg.contains("tuple array length 3 not divisible by arity 2")),
        "expected table_int tuple length mismatch, got: {err}"
    );
}

// --- Global: count_eq ---

#[test]
fn test_count_eq() {
    let r = translate_fzn(
        "array [1..3] of var 1..5: x;\n\
         var 0..3: c;\n\
         constraint fzn_count_eq(x, 2, c);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= (+"));
    assert!(r.smtlib.contains("(ite (= x_1 2) 1 0)"));
    assert!(r.smtlib.contains("(ite (= x_2 2) 1 0)"));
    assert!(r.smtlib.contains("(ite (= x_3 2) 1 0)"));
}

#[test]
fn test_count_eq_with_var_value() {
    let r = translate_fzn(
        "array [1..2] of var 1..3: x;\n\
         var 1..3: v;\n\
         var 0..2: c;\n\
         constraint count_eq(x, v, c);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(ite (= x_1 v) 1 0)"));
    assert!(r.smtlib.contains("(ite (= x_2 v) 1 0)"));
}

#[test]
fn test_alldifferent_int_alias() {
    let r = translate_fzn(
        "var 1..2: x;\n\
         var 1..2: y;\n\
         constraint alldifferent_int([x, y]);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= x y)))"));
}

// --- Global: circuit ---

#[test]
fn test_circuit() {
    let r = translate_fzn(
        "array [1..3] of var 1..3: succ;\n\
         constraint fzn_circuit(succ);\n\
         solve satisfy;\n",
    );
    // All-different pairwise
    assert!(r.smtlib.contains("(assert (not (= succ_1 succ_2)))"));
    assert!(r.smtlib.contains("(assert (not (= succ_1 succ_3)))"));
    assert!(r.smtlib.contains("(assert (not (= succ_2 succ_3)))"));
    // No self-loops
    assert!(r.smtlib.contains("(assert (not (= succ_1 1)))"));
    assert!(r.smtlib.contains("(assert (not (= succ_2 2)))"));
    assert!(r.smtlib.contains("(assert (not (= succ_3 3)))"));
    // MTZ auxiliary variables
    assert!(r.smtlib.contains("(declare-const _circ0_2 Int)"));
    assert!(r.smtlib.contains("(declare-const _circ0_3 Int)"));
    // MTZ bounds (split assertions to work around ay combined-bounds bug)
    assert!(r.smtlib.contains("(assert (>= _circ0_2 2))"));
    assert!(r.smtlib.contains("(assert (<= _circ0_2 3))"));
    // MTZ implication
    assert!(r
        .smtlib
        .contains("(assert (=> (= succ_1 2) (>= _circ0_2 (+ 1 1))))"));
}

#[test]
fn test_circuit_adds_successor_range_guards_for_unbounded_vars() {
    let r = translate_fzn(
        "var int: s1;\n\
         var int: s2;\n\
         var int: s3;\n\
         constraint fzn_circuit([s1, s2, s3]);\n\
         solve satisfy;\n",
    );

    assert!(r.smtlib.contains("(assert (and (>= s1 1) (<= s1 3)))"));
    assert!(r.smtlib.contains("(assert (and (>= s2 1) (<= s2 3)))"));
    assert!(r.smtlib.contains("(assert (and (>= s3 1) (<= s3 3)))"));
}

#[test]
fn test_circuit_uses_zero_based_named_array_indices() {
    let r = translate_fzn(
        "array [0..2] of var int: succ;\n\
         constraint fzn_circuit(succ);\n\
         solve satisfy;\n",
    );

    assert!(r
        .smtlib
        .contains("(assert (and (>= succ_0 0) (<= succ_0 2)))"));
    assert!(r.smtlib.contains("(assert (not (= succ_0 0)))"));
    assert!(r.smtlib.contains("(assert (not (= succ_2 2)))"));
    assert!(r
        .smtlib
        .contains("(assert (=> (= succ_0 1) (>= _circ0_2 (+ 1 1))))"));
}

#[test]
fn test_circuit_singleton_is_its_self_loop() {
    let r = translate_fzn(
        "array [7..7] of var int: succ;\n\
         constraint fzn_circuit(succ);\n\
         solve satisfy;\n",
    );

    assert!(r
        .smtlib
        .contains("(assert (and (>= succ_7 7) (<= succ_7 7)))"));
    assert!(r.smtlib.contains("(assert (= succ_7 7))"));
    assert!(!r.smtlib.contains("(assert (not (= succ_7 7)))"));
}

// --- Global: cumulative ---

#[test]
fn test_cumulative() {
    let r = translate_fzn(
        "array [1..2] of var 0..10: s;\n\
         array [1..2] of int: d = [3, 2];\n\
         array [1..2] of int: r = [2, 3];\n\
         int: cap = 4;\n\
         constraint fzn_cumulative(s, d, r, cap);\n\
         solve satisfy;\n",
    );
    // Event-point encoding: 2 event points × 2 tasks = 4 auxiliary load vars
    let load_count = r.smtlib.matches("(declare-const _cum").count();
    assert_eq!(load_count, 4, "2×2 auxiliary load variables");
    // Each load var has 2 implications (active => r[j], !active => 0)
    let impl_count = r.smtlib.matches("(assert (=>").count();
    assert_eq!(impl_count, 8, "4 load vars × 2 implications each");
    // 2 sum constraints (one per event point)
    assert!(r.smtlib.contains("(assert (<="));
    // Activity check uses overlap condition
    assert!(r.smtlib.contains("(and (<="));
}

#[test]
fn test_cumulative_var_resources() {
    let r = translate_fzn(
        "array [1..2] of var 0..10: s;\n\
         array [1..2] of var 1..5: d;\n\
         array [1..2] of var 1..3: r;\n\
         var 1..5: cap;\n\
         constraint cumulative(s, d, r, cap);\n\
         solve satisfy;\n",
    );
    // Event-point encoding with variable durations and resources
    let load_count = r.smtlib.matches("(declare-const _cum").count();
    assert_eq!(load_count, 4, "2×2 auxiliary load variables");
    // Activity checks reference variable durations: (+ s_N d_N)
    assert!(r.smtlib.contains("(+ s_1 d_1)"));
    assert!(r.smtlib.contains("(+ s_2 d_2)"));
    // Sum constraint uses variable capacity
    assert!(r.smtlib.contains("cap)"));
}

#[test]
fn test_cumulative_rejects_array_length_mismatch() {
    let err = translate_fzn_err(
        "var 0..5: s;\n\
         constraint fzn_cumulative([s], [1, 2], [1], 2);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref msg)
            if msg.contains("cumulative: array length mismatch")),
        "expected cumulative array length mismatch, got: {err}"
    );
}

// --- Global: inverse ---

#[test]
fn test_inverse() {
    let r = translate_fzn(
        "array [1..3] of var 1..3: f;\n\
         array [1..3] of var 1..3: g;\n\
         constraint fzn_inverse(f, g);\n\
         solve satisfy;\n",
    );
    // Forward: f[1]=1 => g[1]=1
    assert!(r.smtlib.contains("(assert (=> (= f_1 1) (= g_1 1)))"));
    // Forward: f[1]=2 => g[2]=1
    assert!(r.smtlib.contains("(assert (=> (= f_1 2) (= g_2 1)))"));
    // Backward: g[1]=1 => f[1]=1
    assert!(r.smtlib.contains("(assert (=> (= g_1 1) (= f_1 1)))"));
}

#[test]
fn test_inverse_adds_index_range_guards_for_unbounded_vars() {
    let r = translate_fzn(
        "var int: f1;\n\
         var int: f2;\n\
         var int: g1;\n\
         var int: g2;\n\
         constraint fzn_inverse([f1, f2], [g1, g2]);\n\
         solve satisfy;\n",
    );

    assert!(r.smtlib.contains("(assert (and (>= f1 1) (<= f1 2)))"));
    assert!(r.smtlib.contains("(assert (and (>= f2 1) (<= f2 2)))"));
    assert!(r.smtlib.contains("(assert (and (>= g1 1) (<= g1 2)))"));
    assert!(r.smtlib.contains("(assert (and (>= g2 1) (<= g2 2)))"));
}

#[test]
fn test_inverse_uses_each_named_arrays_declared_index_set() {
    let r = translate_fzn(
        "array [0..1] of var int: f;\n\
         array [4..5] of var int: g;\n\
         constraint fzn_inverse(f, g);\n\
         solve satisfy;\n",
    );

    assert!(r.smtlib.contains("(assert (and (>= f_0 4) (<= f_0 5)))"));
    assert!(r.smtlib.contains("(assert (and (>= g_4 0) (<= g_4 1)))"));
    assert!(r.smtlib.contains("(assert (=> (= f_0 4) (= g_4 0)))"));
    assert!(r.smtlib.contains("(assert (=> (= g_5 1) (= f_1 5)))"));
}

#[test]
fn test_inverse_rejects_different_array_cardinalities() {
    let err = translate_fzn_err(
        "array [0..1] of var int: f;\n\
         array [4..6] of var int: g;\n\
         constraint fzn_inverse(f, g);\n\
         solve satisfy;\n",
    );

    assert!(
        matches!(err, TranslateError::UnsupportedType(ref message)
            if message.contains("inverse: array cardinality mismatch")),
        "unexpected error: {err}"
    );
}

#[test]
fn test_global_dispatch_rejects_missing_and_extra_arguments() {
    let cases = [
        ("fzn_circuit()", 1, 0),
        ("fzn_circuit([], [])", 1, 2),
        ("all_different_int()", 1, 0),
        ("all_different_int([], [])", 1, 2),
    ];

    for (constraint, expected, got) in cases {
        let err = translate_fzn_err(&format!("constraint {constraint};\nsolve satisfy;\n"));
        assert!(
            matches!(err, TranslateError::WrongArgCount {
                expected: actual_expected,
                got: actual_got,
                ..
            } if actual_expected == expected && actual_got == got),
            "unexpected error for {constraint}: {err}"
        );
    }
}

// --- Global: diffn ---

#[test]
fn test_diffn() {
    let r = translate_fzn(
        "array [1..2] of var 0..10: x;\n\
         array [1..2] of var 0..10: y;\n\
         array [1..2] of int: dx = [2, 3];\n\
         array [1..2] of int: dy = [3, 2];\n\
         constraint fzn_diffn(x, y, dx, dy);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (or"));
    assert!(r.smtlib.contains("(<= (+ x_1 2) x_2)"));
    assert!(r.smtlib.contains("(<= (+ x_2 3) x_1)"));
    assert!(r.smtlib.contains("(<= (+ y_1 3) y_2)"));
    assert!(r.smtlib.contains("(<= (+ y_2 2) y_1)"));
}

#[test]
fn test_diffn_rejects_array_length_mismatch() {
    let err = translate_fzn_err(
        "var 0..5: x;\n\
         var 0..5: y;\n\
         constraint fzn_diffn([x], [y], [1, 2], [1]);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref msg)
            if msg.contains("diffn: array length mismatch")),
        "expected diffn array length mismatch, got: {err}"
    );
}

// --- Integration: Scheduling model ---

#[test]
fn test_scheduling_model() {
    let input = "\
        array [1..3] of var 0..20: s;\n\
        array [1..3] of int: d = [5, 3, 4];\n\
        array [1..3] of int: r = [2, 1, 2];\n\
        int: cap = 3;\n\
        constraint fzn_cumulative(s, d, r, cap);\n\
        constraint int_le(s[1], s[2]);\n\
        solve satisfy;\n";
    let r = translate_fzn(input);
    // Event-point encoding: 3 event points × 3 tasks = 9 auxiliary load vars
    let load_count = r.smtlib.matches("(declare-const _cum").count();
    assert_eq!(load_count, 9, "3×3 auxiliary load variables");
    // int_le constraint still present
    assert!(r.smtlib.contains("(assert (<= s_1 s_2))"));
    assert!(r.smtlib.contains("(check-sat)"));
}

// --- Set-logic tests ---

#[test]
fn test_set_logic_qf_lia_default() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_eq(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(set-logic QF_LIA)"));
}

#[test]
fn test_set_logic_qf_nia_for_multiplication() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_times(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(set-logic QF_NIA)"));
}

#[test]
fn test_set_logic_qf_nia_for_div() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_div(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(set-logic QF_NIA)"));
}

#[test]
fn test_set_logic_lia_for_set_variables() {
    // Set variables use boolean decomposition (no bitvectors), so QF_LIA.
    let r = translate_fzn(
        "var 0..3: x;\nvar set of 0..3: S;\n\
         constraint set_in(x, S);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(set-logic QF_LIA)"));
}

#[test]
fn test_set_logic_lia_for_constant_times_variable() {
    // int_times(constant, variable, result) is linear: r = 3 * x
    let r = translate_fzn(
        "int: c = 3;\nvar int: x;\nvar int: z;\n\
         constraint int_times(c, x, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(set-logic QF_LIA)"));
}

#[test]
fn test_set_logic_lia_for_literal_times_variable() {
    // int_times(literal, variable, result) is linear: r = 5 * x
    let r = translate_fzn(
        "var int: x;\nvar int: z;\n\
         constraint int_times(5, x, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(set-logic QF_LIA)"));
}

#[test]
fn test_set_logic_lia_for_mod_constants() {
    // int_mod(constant, constant, variable) is a constant computation
    let r = translate_fzn(
        "var int: z;\n\
         constraint int_mod(72, 12, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(set-logic QF_LIA)"));
}

#[test]
fn test_set_logic_nia_for_variable_times_variable() {
    // int_times(variable, variable, result) is genuinely nonlinear
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_times(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(set-logic QF_NIA)"));
}

include!("tests_globals/declarations_and_regular.rs");
