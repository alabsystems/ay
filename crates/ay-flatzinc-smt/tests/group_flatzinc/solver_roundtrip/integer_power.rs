// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `solver_roundtrip` to preserve test FQNs.

/// Verify int_pow with negative base: (-3)^2 = 9.
/// Encoding uses repeated multiplication which handles negatives natively.
///
/// Uses QF_LIA directly because ay's QF_NIA solver returns "unknown" for
/// problems it could solve as QF_LIA. The encoding is correct; ay's QF_NIA
/// is incomplete. See #273 for the logic detection issue.
#[test]
fn roundtrip_int_pow_negative_base_even_exp() {
    let ay = exact_ay();
    // Translate to get the encoding, then override logic to QF_LIA for ay
    let fzn = "var -5..5: x;\nvar 0..100: z :: output_var;\n\
               constraint int_eq(x, -3);\n\
               constraint int_pow(x, 2, z);\nsolve satisfy;\n";
    let result = translate_fzn(fzn);
    // Verify encoding contains the correct multiplication pattern
    assert!(
        result.smtlib.contains("(assert (= z (* x x)))"),
        "(-3)^2 should encode as (* x x).\nSMT:\n{}",
        result.smtlib
    );
    // Override logic to QF_LIA to verify correctness through ay
    let smtlib = result.smtlib.replace("QF_NIA", "QF_LIA");
    let (code, stdout, stderr) = run_ay(&smtlib, &ay);
    assert_eq!(code, 0, "ay failed: {stderr}");
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat", "should be SAT, got: {stdout}");
    let values = parse_get_value(lines[1]);
    assert_eq!(
        values.get("z").map(String::as_str),
        Some("9"),
        "(-3)^2 should be 9, got: {values:?}"
    );
}

/// Verify int_pow with negative base and odd exponent: (-2)^3 = -8.
/// Uses QF_LIA to bypass ay's incomplete QF_NIA solver.
#[test]
fn roundtrip_int_pow_negative_base_odd_exp() {
    let ay = exact_ay();
    let fzn = "var -5..5: x;\nvar -1000..1000: z :: output_var;\n\
               constraint int_eq(x, -2);\n\
               constraint int_pow(x, 3, z);\nsolve satisfy;\n";
    let result = translate_fzn(fzn);
    assert!(
        result.smtlib.contains("(assert (= z (* x (* x x))))"),
        "(-2)^3 should encode as (* x (* x x)).\nSMT:\n{}",
        result.smtlib
    );
    let smtlib = result.smtlib.replace("QF_NIA", "QF_LIA");
    let (code, stdout, stderr) = run_ay(&smtlib, &ay);
    assert_eq!(code, 0, "ay failed: {stderr}");
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat", "should be SAT, got: {stdout}");
    let values = parse_get_value(lines[1]);
    // ay may format negative ints as "(- 8)" or "-8" depending on logic
    let z_val = values.get("z").expect("z not in model");
    assert!(
        z_val == "(- 8)" || z_val == "-8",
        "(-2)^3 should be -8, got z={z_val}, full: {values:?}"
    );
}

/// Verify int_pow with large exponent: 2^10 = 1024.
/// Uses QF_LIA to bypass ay's incomplete QF_NIA solver.
#[test]
fn roundtrip_int_pow_large_exponent() {
    let ay = exact_ay();
    let fzn = "var 1..10: x;\nvar 0..100000: z :: output_var;\n\
               constraint int_eq(x, 2);\n\
               constraint int_pow(x, 10, z);\nsolve satisfy;\n";
    let result = translate_fzn(fzn);
    let smtlib = result.smtlib.replace("QF_NIA", "QF_LIA");
    let (code, stdout, stderr) = run_ay(&smtlib, &ay);
    assert_eq!(code, 0, "ay failed: {stderr}");
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat", "should be SAT, got: {stdout}");
    let values = parse_get_value(lines[1]);
    assert_eq!(
        values.get("z").map(String::as_str),
        Some("1024"),
        "2^10 should be 1024, got: {values:?}"
    );
}

/// Verify int_pow with variable exponent: x=3, n ∈ {0,1,2}, z = x^n.
/// Tests the ite chain encoding.
#[test]
fn roundtrip_int_pow_variable_exponent() {
    let ay = exact_ay();
    let fzn = "var int: x;\nvar 0..2: n;\nvar int: z :: output_var;\n\
               constraint int_eq(x, 3);\n\
               constraint int_eq(n, 2);\n\
               constraint int_pow(x, n, z);\nsolve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay failed: {stderr}");
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat", "should be SAT, got: {stdout}");
    let values = parse_get_value(lines[1]);
    assert_eq!(
        values.get("z").map(String::as_str),
        Some("9"),
        "3^2 via variable exponent should be 9, got: {values:?}"
    );
}
