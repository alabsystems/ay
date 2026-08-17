// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `builtin_coverage` to preserve test FQNs.

#[test]
fn test_int_pow_constant_exponent_3() {
    let r = translate_fzn(
        "var int: x;\nvar int: z;\n\
         constraint int_pow(x, 3, z);\nsolve satisfy;\n",
    );
    // x^3 = (* x (* x x))
    assert!(
        r.smtlib.contains("(assert (= z (* x (* x x))))"),
        "int_pow with constant exp=3 should produce (* x (* x x)).\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_pow_constant_exponent_0() {
    let r = translate_fzn(
        "var int: x;\nvar int: z;\n\
         constraint int_pow(x, 0, z);\nsolve satisfy;\n",
    );
    // x^0 = 1
    assert!(
        r.smtlib.contains("(assert (= z 1))"),
        "int_pow with constant exp=0 should produce 1.\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_pow_constant_exponent_1() {
    let r = translate_fzn(
        "var int: x;\nvar int: z;\n\
         constraint int_pow(x, 1, z);\nsolve satisfy;\n",
    );
    // x^1 = x
    assert!(
        r.smtlib.contains("(assert (= z x))"),
        "int_pow with constant exp=1 should produce x.\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_pow_constant_exponent_2() {
    let r = translate_fzn(
        "var int: x;\nvar int: z;\n\
         constraint int_pow(x, 2, z);\nsolve satisfy;\n",
    );
    // x^2 = (* x x)
    assert!(
        r.smtlib.contains("(assert (= z (* x x)))"),
        "int_pow with constant exp=2 should produce (* x x).\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_pow_variable_exponent() {
    let r = translate_fzn(
        "var int: x;\nvar 0..3: n;\nvar int: z;\n\
         constraint int_pow(x, n, z);\nsolve satisfy;\n",
    );
    // Variable exponent with domain 0..3 produces ite chain
    assert!(
        r.smtlib.contains("(ite (= n 0) 1"),
        "int_pow with variable exp should produce ite chain starting at 0.\nSMT:\n{}",
        r.smtlib
    );
    assert!(
        r.smtlib.contains("(ite (= n 3) (* x (* x x))"),
        "int_pow with variable exp should include n=3 case.\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_pow_variable_base_square_uses_qf_nia() {
    // int_pow(x, 2, z) emits z = x*x, so it is nonlinear even though the
    // exponent itself is constant.
    let r = translate_fzn(
        "var int: x;\nvar int: z;\n\
         constraint int_pow(x, 2, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(set-logic QF_NIA)"),
        "int_pow with variable base and exponent 2 should use QF_NIA.\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_pow_variable_exponent_triggers_qf_nia() {
    // int_pow(x, n, z) — both x and n are variables, so this is genuinely
    // nonlinear and must use QF_NIA.
    let r = translate_fzn(
        "var int: x;\nvar 0..5: n;\nvar int: z;\n\
         constraint int_pow(x, n, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(set-logic QF_NIA)"),
        "int_pow with variable exponent should trigger QF_NIA.\nSMT:\n{}",
        r.smtlib
    );
}
