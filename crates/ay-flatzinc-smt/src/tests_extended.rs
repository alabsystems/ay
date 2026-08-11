// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Extended constraint coverage tests for FlatZinc-to-SMT translation.
// Extracted from tests.rs to keep files under 500 lines.
// Covers: reified constraints, extended comparisons/arithmetic/boolean,
// array boolean, DZN output, SmtInt utility, and logic detection.

use super::*;
use ay_core::kani_compat::DetHashMap as HashMap;

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

// --- Reified constraint tests ---

#[test]
fn test_int_eq_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_eq_reif(x, y, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (= x y)))"));
    assert!(r.smtlib.contains("(assert (=> (= x y) b))"));
}

#[test]
fn test_int_le_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_le_reif(x, y, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (<= x y)))"));
    assert!(r.smtlib.contains("(assert (=> (<= x y) b))"));
}

#[test]
fn test_int_lin_eq_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_lin_eq_reif([1, 1], [x, y], 5, b);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (= (+ x y) 5)))"));
    assert!(r.smtlib.contains("(assert (=> (= (+ x y) 5) b))"));
}

#[test]
fn test_int_ne_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_ne_reif(x, y, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (not (= x y))))"));
    assert!(r.smtlib.contains("(assert (=> (not (= x y)) b))"));
}

#[test]
fn test_int_gt_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_gt_reif(x, y, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (> x y)))"));
    assert!(r.smtlib.contains("(assert (=> (> x y) b))"));
}

#[test]
fn test_int_ge_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_ge_reif(x, y, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (>= x y)))"));
    assert!(r.smtlib.contains("(assert (=> (>= x y) b))"));
}

#[test]
fn test_bool_eq_reif() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: r;\n\
         constraint bool_eq_reif(a, b, r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (= a b)))"));
    assert!(r.smtlib.contains("(assert (=> (= a b) r))"));
}

#[test]
fn test_int_lin_le_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_lin_le_reif([1, 1], [x, y], 10, b);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (<= (+ x y) 10)))"));
    assert!(r.smtlib.contains("(assert (=> (<= (+ x y) 10) b))"));
}

#[test]
fn test_int_lin_ne_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_lin_ne_reif([1, 1], [x, y], 5, b);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (not (= (+ x y) 5))))"));
    assert!(r.smtlib.contains("(assert (=> (not (= (+ x y) 5)) b))"));
}

#[test]
fn test_set_in_reif() {
    let r = translate_fzn(
        "var int: x;\nvar bool: b;\n\
         constraint set_in_reif(x, {1, 3, 5}, b);\nsolve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (=> b (or (= x 1) (= x 3) (= x 5))))"));
    assert!(r
        .smtlib
        .contains("(assert (=> (or (= x 1) (= x 3) (= x 5)) b))"));
}

#[test]
fn test_set_in_reif_single() {
    let r = translate_fzn(
        "var int: x;\nvar bool: b;\n\
         constraint set_in_reif(x, {42}, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (= x 42)))"));
    assert!(r.smtlib.contains("(assert (=> (= x 42) b))"));
}

// --- DZN output tests ---

#[test]
fn test_dzn_scalar() {
    let mut values = HashMap::default();
    values.insert("x".into(), "5".into());
    let output_vars = vec![OutputVarInfo {
        fzn_name: "x".into(),
        smt_names: vec!["x".into()],
        is_array: false,
        array_range: None,
        is_bool: false,
        is_set: false,
        set_range: None,
    }];
    let dzn = format_dzn_solution(&values, &output_vars);
    assert_eq!(dzn.trim(), "x = 5;");
}

#[test]
fn test_dzn_array() {
    let mut values = HashMap::default();
    values.insert("q_1".into(), "2".into());
    values.insert("q_2".into(), "4".into());
    values.insert("q_3".into(), "1".into());
    let output_vars = vec![OutputVarInfo {
        fzn_name: "q".into(),
        smt_names: vec!["q_1".into(), "q_2".into(), "q_3".into()],
        is_array: true,
        array_range: Some((1, 3)),
        is_bool: false,
        is_set: false,
        set_range: None,
    }];
    let dzn = format_dzn_solution(&values, &output_vars);
    assert_eq!(dzn.trim(), "q = array1d(1..3, [2, 4, 1]);");
}

// --- Extended comparison constraint tests ---

#[test]
fn test_int_gt() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_gt(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (> x y))"));
}

#[test]
fn test_int_ge() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_ge(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (>= x y))"));
}

// --- Extended arithmetic constraint tests ---

#[test]
fn test_int_minus() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_minus(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= z (- x y)))"));
}

#[test]
fn test_int_div() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_div(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= y 0)))"));
    assert!(r.smtlib.contains("(div (ite (>= x 0) x (- x))"));
    assert!(r.smtlib.contains("(assert (= z (ite"));
}

#[test]
fn test_int_mod() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_mod(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= y 0)))"));
    assert!(r.smtlib.contains("(assert (= z (- x (* (ite"));
}

#[test]
fn test_int_div_and_mod_match_flatzinc_sign_semantics() {
    for (dividend, divisor, quotient, remainder) in [
        (7, 3, 2, 1),
        (-7, 3, -2, -1),
        (7, -3, -2, 1),
        (-7, -3, 2, -1),
    ] {
        let input = format!(
            "var int: q;\nvar int: r;\n\
             constraint int_div({dividend}, {divisor}, q);\n\
             constraint int_mod({dividend}, {divisor}, r);\n\
             constraint int_eq(q, {quotient});\n\
             constraint int_eq(r, {remainder});\n\
             solve satisfy;\n"
        );
        assert_eq!(
            solve_fzn_verdict(&input),
            "sat",
            "unexpected div/mod result for {dividend}, {divisor}"
        );
    }
}

#[test]
fn test_int_div_and_mod_reject_zero_divisor() {
    for constraint in ["int_div(7, 0, result)", "int_mod(7, 0, result)"] {
        let input = format!("var int: result;\nconstraint {constraint};\nsolve satisfy;\n");
        assert_eq!(solve_fzn_verdict(&input), "unsat");
    }
}

#[test]
fn test_int_negate() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_negate(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= y (- x)))"));
}

// --- Extended boolean constraint tests ---

#[test]
fn test_bool_xor() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: r;\n\
         constraint bool_xor(a, b, r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (xor a b)))"));
    assert!(r.smtlib.contains("(assert (=> (xor a b) r))"));
}

#[test]
fn test_bool_eq() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\n\
         constraint bool_eq(a, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= a b))"));
}

// --- Boolean linear constraint tests ---

#[test]
fn test_bool_lin_eq() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\n\
         constraint bool_lin_eq([1, 1], [a, b], 1);\nsolve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (= (+ (ite a 1 0) (ite b 1 0)) 1))"));
}

#[test]
fn test_bool_lin_le() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\n\
         constraint bool_lin_le([2, 3], [a, b], 4);\nsolve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (<= (+ (* 2 (ite a 1 0)) (* 3 (ite b 1 0))) 4))"));
}

#[test]
fn test_linear_constraints_reject_parallel_array_length_mismatch() {
    let extra_coefficient = translate_fzn_err(
        "var int: x;\n\
         constraint int_lin_eq([1, 2], [x], 0);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(extra_coefficient, TranslateError::UnsupportedType(ref message)
            if message.contains("coefficient array length 2")
                && message.contains("variable array length 1")),
        "unexpected error: {extra_coefficient}"
    );

    let extra_boolean = translate_fzn_err(
        "var bool: a;\n\
         var bool: b;\n\
         var bool: r;\n\
         constraint bool_lin_eq([1], [a, b], 1);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(extra_boolean, TranslateError::UnsupportedType(ref message)
            if message.contains("coefficient array length 1")
                && message.contains("variable array length 2")),
        "unexpected error: {extra_boolean}"
    );
}

// --- Array boolean constraint tests ---

#[test]
fn test_array_bool_and() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: c;\nvar bool: r;\n\
         constraint array_bool_and([a, b, c], r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (and a b c)))"));
    assert!(r.smtlib.contains("(assert (=> (and a b c) r))"));
}

#[test]
fn test_array_bool_and_single() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: r;\n\
         constraint array_bool_and([a], r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r a))"));
    assert!(r.smtlib.contains("(assert (=> a r))"));
}

#[test]
fn test_array_bool_or() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: c;\nvar bool: r;\n\
         constraint array_bool_or([a, b, c], r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (or a b c)))"));
    assert!(r.smtlib.contains("(assert (=> (or a b c) r))"));
}

#[test]
fn test_array_bool_or_single() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: r;\n\
         constraint array_bool_or([a], r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r a))"));
    assert!(r.smtlib.contains("(assert (=> a r))"));
}

#[test]
fn test_array_bool_xor() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: c;\n\
         constraint array_bool_xor([a, b, c]);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (xor a (xor b c)))"));
}

#[test]
fn test_array_bool_xor_two() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\n\
         constraint array_bool_xor([a, b]);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (xor a b))"));
}

// --- SmtInt / smt_int tests ---

#[test]
fn test_smt_int_positive() {
    assert_eq!(translate::smt_int(42), "42");
}

#[test]
fn test_smt_int_negative() {
    assert_eq!(translate::smt_int(-7), "(- 7)");
}

#[test]
fn test_smt_int_zero() {
    assert_eq!(translate::smt_int(0), "0");
}

#[test]
fn test_smt_int_display_matches_smt_int() {
    for n in [-100, -7, -1, 0, 1, 7, 42, 100, i64::MIN + 1, i64::MAX] {
        assert_eq!(translate::SmtInt(n).to_string(), translate::smt_int(n));
    }
}

#[test]
fn test_smt_int_in_format_args() {
    let result = format!("(assert (= x {}))", translate::SmtInt(-5));
    assert_eq!(result, "(assert (= x (- 5)))");
}

// --- Logic detection tests (QF_LIA vs QF_NIA) ---

#[test]
fn test_detect_logic_no_nonlinear_is_qf_lia() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_plus(x, y, x);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(set-logic QF_LIA)"),
        "int_plus should produce QF_LIA"
    );
}

#[test]
fn test_detect_logic_var_times_var_is_qf_nia() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_times(x, y, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(set-logic QF_NIA)"),
        "variable * variable should produce QF_NIA"
    );
}

#[test]
fn test_detect_logic_const_times_var_is_qf_lia() {
    // int_times(3, x, z) where 3 is a literal -> linear, not nonlinear
    let r = translate_fzn(
        "var int: x;\nvar int: z;\n\
         constraint int_times(3, x, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(set-logic QF_LIA)"),
        "constant * variable should produce QF_LIA, not QF_NIA"
    );
}

#[test]
fn test_detect_logic_param_times_var_is_qf_lia() {
    // int_times(n, x, z) where n is a parameter -> linear
    let r = translate_fzn(
        "int: n = 3;\nvar int: x;\nvar int: z;\n\
         constraint int_times(n, x, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(set-logic QF_LIA)"),
        "parameter * variable should produce QF_LIA, not QF_NIA"
    );
}

#[test]
fn test_detect_logic_int_pow_var_var_is_qf_nia() {
    let r = translate_fzn(
        "var int: x;\nvar 0..3: y;\nvar int: z;\n\
         constraint int_pow(x, y, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(set-logic QF_NIA)"),
        "int_pow(var, var) should produce QF_NIA"
    );
}

#[test]
fn test_detect_logic_variable_base_constant_square_is_qf_nia() {
    let r = translate_fzn(
        "var int: x;\nvar int: z;\n\
         constraint int_pow(x, 2, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(set-logic QF_NIA)"),
        "x^2 emits variable multiplication and must use QF_NIA"
    );
}

#[test]
fn test_int_pow_rejects_unbounded_negative_and_too_large_exponents() {
    let cases = [
        (
            "var int: exponent;\nvar int: result;\n\
             constraint int_pow(2, exponent, result);\nsolve satisfy;\n",
            "finite non-negative integer domain",
        ),
        (
            "var -1..2: exponent;\nvar int: result;\n\
             constraint int_pow(2, exponent, result);\nsolve satisfy;\n",
            "negative exponent",
        ),
        (
            "var 65..65: exponent;\nvar int: result = 1;\n\
             constraint int_pow(2, exponent, result);\nsolve satisfy;\n",
            "exceeds the maximum supported",
        ),
    ];
    for (input, expected_message) in cases {
        let error = translate_fzn_err(input);
        assert!(
            matches!(error, TranslateError::UnsupportedType(ref message)
                if message.contains(expected_message)),
            "unexpected error: {error}"
        );
    }
}

#[test]
fn test_int_pow_enumerates_unsorted_integer_set_domain_exactly() {
    let r = translate_fzn(
        "var int: x;\nvar {3, 1}: exponent;\nvar int: result;\n\
         constraint int_pow(x, exponent, result);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(= exponent 1)"));
    assert!(r.smtlib.contains("(= exponent 3)"));
    assert!(!r.smtlib.contains("(= exponent 2)"));
    assert!(r.smtlib.contains("(* x (* x x))"));
}

#[test]
fn test_logic_detection_handles_full_width_scalar_range() {
    let r = translate_fzn(
        "var -9223372036854775808..9223372036854775807: x;\n\
         var int: y;\nvar int: z;\n\
         constraint int_times(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(set-logic QF_NIA)"));
}

#[test]
fn test_detect_logic_int_pow_const_const_is_qf_lia() {
    // int_pow(2, 3, z) where both are constants -> constant computation
    let r = translate_fzn(
        "int: base = 2;\nint: exp = 3;\nvar int: z;\n\
         constraint int_pow(base, exp, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(set-logic QF_LIA)"),
        "int_pow(constant, constant) should produce QF_LIA"
    );
}

#[test]
fn quadratic_encoding_work_guard_accepts_budget_and_rejects_next_square() {
    translate::ensure_quadratic_work("boundary", 1024, 1024, 1)
        .expect("the exact materialization budget is accepted");
    let error = translate::ensure_quadratic_work("boundary", 1025, 1025, 1)
        .expect_err("the next square must exceed the materialization budget");
    assert!(
        matches!(error, TranslateError::UnsupportedType(ref message)
            if message.contains("quadratic encoding")
                && message.contains("1050625")
                && message.contains("1048576")),
        "unexpected work-limit error: {error}"
    );
}

#[test]
fn oversized_all_different_fails_before_quadratic_emission() {
    let error = translate_fzn_err(
        "array [1..1025] of var 0..1: xs;\n\
         constraint all_different_int(xs);\nsolve satisfy;\n",
    );
    assert!(
        matches!(error, TranslateError::UnsupportedType(ref message)
            if message.contains("all_different") && message.contains("1050625")),
        "unexpected all_different work-limit error: {error}"
    );
}
