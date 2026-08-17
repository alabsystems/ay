// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `solver_roundtrip` to preserve test FQNs.

#[test]
fn roundtrip_reified_eq_false() {
    let ay = exact_ay();
    // b <=> (x = y), with x=5, y=3, so b should be false
    let fzn = "var int: x :: output_var;\n\
               var int: y :: output_var;\n\
               var bool: b :: output_var;\n\
               constraint int_eq(x, 5);\n\
               constraint int_eq(y, 3);\n\
               constraint int_eq_reif(x, y, b);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat");

    let values = parse_get_value(lines[1]);
    assert_eq!(
        values.get("b").unwrap(),
        "false",
        "5 != 3 so eq_reif should be false"
    );

    let dzn = format_dzn_solution(&values, &result.output_vars);
    assert!(dzn.contains("b = false;"), "DZN: {dzn}");
}

#[test]
fn roundtrip_reified_ne_false() {
    let ay = exact_ay();
    // b <=> (x != y), with x=5, y=5, so b should be false
    let fzn = "var int: x :: output_var;\n\
               var int: y :: output_var;\n\
               var bool: b :: output_var;\n\
               constraint int_eq(x, 5);\n\
               constraint int_eq(y, 5);\n\
               constraint int_ne_reif(x, y, b);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat");

    let values = parse_get_value(lines[1]);
    assert_eq!(
        values.get("b").unwrap(),
        "false",
        "5 = 5 so ne_reif should be false"
    );
}

#[test]
fn roundtrip_reified_lt_false() {
    let ay = exact_ay();
    // b <=> (x < y), with x=5, y=3, so b should be false
    let fzn = "var int: x :: output_var;\n\
               var int: y :: output_var;\n\
               var bool: b :: output_var;\n\
               constraint int_eq(x, 5);\n\
               constraint int_eq(y, 3);\n\
               constraint int_lt_reif(x, y, b);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat");

    let values = parse_get_value(lines[1]);
    assert_eq!(
        values.get("b").unwrap(),
        "false",
        "5 < 3 is false so lt_reif should be false"
    );
}

#[test]
fn roundtrip_negative_values() {
    let ay = exact_ay();
    // x + y = 0, x in -5..5, y in -5..5, x > 0 -> y < 0
    let fzn = "var -5..5: x :: output_var;\n\
               var -5..5: y :: output_var;\n\
               constraint int_lin_eq([1, 1], [x, y], 0);\n\
               constraint int_gt(x, 0);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let (code, stdout, stderr) = run_ay(&result.smtlib, &ay);
    assert_eq!(code, 0, "ay stderr: {stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat");

    let values = parse_get_value(lines[1]);
    // Parse values, handling SMT negative format "(- N)"
    let x_raw = values.get("x").unwrap();
    let y_raw = values.get("y").unwrap();
    let x = parse_smt_int(x_raw);
    let y = parse_smt_int(y_raw);
    assert_eq!(x + y, 0, "x + y should equal 0: x={x}, y={y}");
    assert!(x > 0, "x should be positive: {x}");
    assert!(y < 0, "y should be negative: {y}");

    // Verify DZN handles negative formatting
    let dzn = format_dzn_solution(&values, &result.output_vars);
    assert!(
        dzn.contains(&format!("y = {y};")),
        "DZN should format negative: {dzn}"
    );
}
