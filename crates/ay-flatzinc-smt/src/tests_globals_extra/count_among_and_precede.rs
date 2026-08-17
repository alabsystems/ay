// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests_globals_extra` to preserve test FQNs.

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
