// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests_extended` to preserve test FQNs.

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
