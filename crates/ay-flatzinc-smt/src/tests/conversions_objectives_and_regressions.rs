// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

// --- Type conversion tests ---

#[test]
fn test_bool2int() {
    let r = translate_fzn(
        "var bool: b;\nvar int: i;\n\
         constraint bool2int(b, i);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= i (ite b 1 0)))"));
}

// --- Set membership tests ---

#[test]
fn test_set_in_literal() {
    let r = translate_fzn(
        "var int: x;\n\
         constraint set_in(x, {1, 3, 5});\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (or (= x 1) (= x 3) (= x 5)))"));
}

#[test]
fn test_set_in_range() {
    let r = translate_fzn(
        "var int: x;\n\
         constraint set_in(x, 1..5);\nsolve satisfy;\n",
    );
    // Range expands to individual equalities
    assert!(r.smtlib.contains("(assert (or (= x 1) (= x 2)"));
}

// --- Global constraint tests ---

#[test]
fn test_alldifferent() {
    let r = translate_fzn(
        "array [1..3] of var 1..3: x;\n\
         constraint fzn_all_different_int(x);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= x_1 x_2)))"));
    assert!(r.smtlib.contains("(assert (not (= x_1 x_3)))"));
    assert!(r.smtlib.contains("(assert (not (= x_2 x_3)))"));
}

// --- Objective tests ---

#[test]
fn test_solve_satisfy() {
    let r = translate_fzn("var int: x;\nsolve satisfy;\n");
    assert!(r.objective.is_none());
    assert!(r.smtlib.contains("(check-sat)"));
}

#[test]
fn test_solve_minimize() {
    let r = translate_fzn("var int: obj;\nsolve minimize obj;\n");
    let obj = r.objective.as_ref().expect("should have objective");
    assert!(obj.minimize);
    assert_eq!(obj.smt_expr, "obj");
}

#[test]
fn test_solve_maximize() {
    let r = translate_fzn("var int: obj;\nsolve maximize obj;\n");
    let obj = r.objective.as_ref().expect("should have objective");
    assert!(!obj.minimize);
    assert_eq!(obj.smt_expr, "obj");
}

// --- Output variable tests ---

#[test]
fn test_output_var_annotation() {
    let r = translate_fzn("var 1..5: x :: output_var;\nsolve satisfy;\n");
    assert_eq!(r.output_vars.len(), 1);
    assert_eq!(r.output_vars[0].fzn_name, "x");
    assert!(!r.output_vars[0].is_array);
}

#[test]
fn test_output_array_annotation() {
    let r = translate_fzn(
        "array [1..3] of var 1..5: q :: output_array([1..3]);\n\
         solve satisfy;\n",
    );
    assert_eq!(r.output_vars.len(), 1);
    assert_eq!(r.output_vars[0].fzn_name, "q");
    assert!(r.output_vars[0].is_array);
    assert_eq!(r.output_vars[0].array_range, Some((1, 3)));
    assert_eq!(r.output_vars[0].smt_names.len(), 3);
}

// --- Integration: N-Queens model ---

#[test]
fn test_nqueens_4_model() {
    let input = "\
        int: n = 4;\n\
        array [1..4] of var 1..4: q :: output_array([1..4]);\n\
        constraint fzn_all_different_int(q);\n\
        constraint int_ne(q[1], q[2]);\n\
        solve satisfy;\n";
    let r = translate_fzn(input);
    // Should have 4 array elements declared
    assert!(r.smtlib.contains("(declare-const q_1 Int)"));
    assert!(r.smtlib.contains("(declare-const q_4 Int)"));
    // Bounds for each element
    assert!(r.smtlib.contains("(assert (>= q_1 1))"));
    assert!(r.smtlib.contains("(assert (<= q_1 4))"));
    // Alldifferent pairwise
    assert!(r.smtlib.contains("(assert (not (= q_1 q_2)))"));
    assert!(r.smtlib.contains("(assert (not (= q_3 q_4)))"));
    // Direct constraint using array access
    assert!(r.smtlib.contains("(assert (not (= q_1 q_2)))"));
    // Output variable tracking
    assert_eq!(r.output_vars.len(), 1);
    assert_eq!(r.output_vars[0].fzn_name, "q");
    assert_eq!(r.output_vars[0].smt_names.len(), 4);
    // check-sat and get-value present
    assert!(r.smtlib.contains("(check-sat)"));
    assert!(r.smtlib.contains("(get-value ("));
}

// --- int_times linearization tests ---

#[test]
fn test_int_times_linearized_small_domain() {
    // When one operand has a small range (0..3 = 4 values), int_times should
    // linearize via ITE chain instead of using nonlinear `*`.
    let r = translate_fzn(
        "var 0..3: a;\nvar int: b;\nvar int: r;\n\
         constraint int_times(a, b, r);\nsolve satisfy;\n",
    );
    // Should NOT contain bare multiplication
    assert!(
        !r.smtlib.contains("(assert (= r (* a b)))"),
        "Expected linearized ITE, not bare multiplication:\n{}",
        r.smtlib
    );
    // Should contain ITE chain with domain values 0, 1, 2, 3
    assert!(
        r.smtlib.contains("(ite (= a 0)"),
        "Expected ITE for a=0:\n{}",
        r.smtlib
    );
    assert!(
        r.smtlib.contains("(ite (= a 1)"),
        "Expected ITE for a=1:\n{}",
        r.smtlib
    );
    // Value 0 should produce "0" (not (* 0 b))
    assert!(
        r.smtlib.contains("(ite (= a 0) 0"),
        "Expected 0 for a*b when a=0:\n{}",
        r.smtlib
    );
    // Value 1 should produce "b" (not (* 1 b))
    assert!(
        r.smtlib.contains("(ite (= a 1) b"),
        "Expected b for a*b when a=1:\n{}",
        r.smtlib
    );
    // Logic should be QF_LIA, not QF_NIA
    assert!(
        r.smtlib.contains("(set-logic QF_LIA)"),
        "Expected QF_LIA after linearization, got:\n{}",
        r.smtlib.lines().next().unwrap_or("")
    );
}

#[test]
fn test_int_times_linearized_second_operand() {
    // When the second operand is small-domain, should also linearize.
    let r = translate_fzn(
        "var int: a;\nvar 0..2: b;\nvar int: r;\n\
         constraint int_times(a, b, r);\nsolve satisfy;\n",
    );
    assert!(
        !r.smtlib.contains("(assert (= r (* a b)))"),
        "Expected linearized ITE, not bare multiplication:\n{}",
        r.smtlib
    );
    assert!(
        r.smtlib.contains("(ite (= b"),
        "Expected ITE on b (second operand):\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_times_unbounded_stays_nonlinear() {
    // When both operands are unbounded, should use nonlinear `*`.
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_times(x, y, z);\nsolve satisfy;\n",
    );
    assert!(
        r.smtlib.contains("(assert (= z (* x y)))"),
        "Expected nonlinear multiplication for unbounded vars:\n{}",
        r.smtlib
    );
}

#[test]
fn test_int_times_bool_operand_linearized() {
    // Bool variables have domain {0, 1} and should trigger linearization.
    let r = translate_fzn(
        "var bool: flag;\nvar int: x;\nvar int: r;\n\
         var 0..1: flag_int;\n\
         constraint bool2int(flag, flag_int);\n\
         constraint int_times(flag_int, x, r);\nsolve satisfy;\n",
    );
    // 0..1 domain should linearize: ite(flag_int=0, 0, x)
    assert!(
        !r.smtlib.contains("(* flag_int x)"),
        "Expected linearized ITE for 0..1 domain:\n{}",
        r.smtlib
    );
}

// --- Error handling tests ---

#[test]
fn test_unsupported_constraint_error() {
    let input = "var int: x;\nconstraint unknown_constraint(x);\nsolve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(input).unwrap();
    let err = translate(&model).unwrap_err();
    assert!(
        matches!(err, TranslateError::UnsupportedConstraint(ref s) if s == "unknown_constraint")
    );
}

// --- Edge case tests ---

#[test]
fn test_empty_model() {
    let r = translate_fzn("solve satisfy;\n");
    assert!(r.smtlib.contains("(check-sat)"));
    assert!(r.output_vars.is_empty());
    assert!(r.objective.is_none());
}

#[test]
fn test_single_element_set_in() {
    let r = translate_fzn(
        "var int: x;\n\
         constraint set_in(x, {42});\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= x 42))"));
}

#[test]
fn test_negative_int_in_smt() {
    let r = translate_fzn(
        "int: n = -5;\nvar int: x;\n\
         constraint int_eq(x, n);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= x (- 5)))"));
}
