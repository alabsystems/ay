// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for 100% builtin constraint coverage in flatzinc-smt.
//!
//! Covers every constraint handler in builtins.rs that was previously untested:
//! int_gt, int_ge, int_minus, int_div, int_mod, int_negate,
//! bool_xor, bool_eq, bool_lin_eq, bool_lin_le,
//! int_ne_reif, int_gt_reif, int_ge_reif, bool_eq_reif,
//! int_lin_le_reif, int_lin_ne_reif, set_in_reif + edge cases.
//!
//! Part of #319 (FlatZinc translation correctness), #273 (MiniZinc entry).

use ay_flatzinc_smt::translate;

fn translate_fzn(input: &str) -> ay_flatzinc_smt::TranslationResult {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect("translate failed")
}

// --- Integer comparison: int_gt, int_ge ---

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

// --- Integer arithmetic: int_minus, int_div, int_mod, int_negate ---

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
    assert!(r.smtlib.contains("(assert (= z (ite (= (>= x 0) (>= y 0))"));
    assert!(r.smtlib.contains("(div (ite (>= x 0) x (- x))"));
}

#[test]
fn test_int_mod() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_mod(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= y 0)))"));
    assert!(r
        .smtlib
        .contains("(assert (= z (- x (* (ite (= (>= x 0) (>= y 0))"));
}

#[test]
fn test_int_negate() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_negate(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= y (- x)))"));
}

// --- Boolean: bool_xor, bool_eq ---

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

// --- Boolean linear: bool_lin_eq, bool_lin_le ---

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

// --- Reified: int_ne_reif, int_gt_reif, int_ge_reif, bool_eq_reif ---

#[test]
fn test_int_ne_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_ne_reif(x, y, b);\nsolve satisfy;\n",
    );
    // Negated reified uses iff decomposition with (not (= ...))
    assert!(r.smtlib.contains("(assert (=> b (not (= x y))))"));
    assert!(r.smtlib.contains("(assert (=> (not (= x y)) b))"));
}

#[test]
fn test_int_gt_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_gt_reif(x, y, b);\nsolve satisfy;\n",
    );
    // Reified uses iff decomposition: b => (> x y) and (> x y) => b
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

// --- Reified linear: int_lin_le_reif, int_lin_ne_reif ---

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

// --- Reified set: set_in_reif ---

#[test]
fn test_set_in_reif() {
    let r = translate_fzn(
        "var int: x;\nvar bool: b;\n\
         constraint set_in_reif(x, {1, 3, 5}, b);\nsolve satisfy;\n",
    );
    // Reified set membership uses iff decomposition
    assert!(r
        .smtlib
        .contains("(assert (=> b (or (= x 1) (= x 3) (= x 5))))"));
    assert!(r
        .smtlib
        .contains("(assert (=> (or (= x 1) (= x 3) (= x 5)) b))"));
}

#[test]
fn test_set_in_reif_single_element() {
    let r = translate_fzn(
        "var int: x;\nvar bool: b;\n\
         constraint set_in_reif(x, {42}, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (= x 42)))"));
    assert!(r.smtlib.contains("(assert (=> (= x 42) b))"));
}

// --- Global constraint algorithm audit ---

/// Verify cumulative event-point encoding produces auxiliary variables and
/// sum constraints (one per event point).
///
/// The encoding declares load variables _cum{id}_{i}_{j} for each event
/// point i and task j, with implications constraining them to r[j] or 0,
/// then asserts the sum <= capacity at each event point.
#[test]
fn test_cumulative_event_point_encoding_structure() {
    // 3 tasks, durations 10 each, resources 2 each, capacity 3
    let r = translate_fzn(
        "var 0..20: s1;\nvar 0..20: s2;\nvar 0..20: s3;\n\
         constraint fzn_cumulative([s1,s2,s3], [10,10,10], [2,2,2], 3);\n\
         solve satisfy;\n",
    );
    let smt = &r.smtlib;
    // 3 event points × 3 tasks = 9 auxiliary load variables
    let load_decl_count = smt.matches("(declare-const _cum").count();
    assert_eq!(
        load_decl_count, 9,
        "cumulative should declare 9 auxiliary load variables (3×3)"
    );
    // Each load variable has 2 implications: active => r[j], !active => 0
    let implication_count = smt.matches("(assert (=>").count();
    assert_eq!(
        implication_count, 18,
        "cumulative should generate 18 implications (9 vars × 2 each)"
    );
    // 3 sum assertions (one per event point)
    let sum_count = smt.matches("(assert (<= (+").count();
    assert_eq!(
        sum_count, 3,
        "cumulative should generate 3 sum assertions (one per event point)"
    );
}

/// Verify the event-point encoding is sound for 3+ overlapping tasks.
///
/// With resources [2,2,2] and capacity 5, every pair fits (4 <= 5)
/// but all three overlapping uses 6 > 5. The old pairwise encoding missed
/// this; the event-point encoding correctly constrains it via implications.
#[test]
fn test_cumulative_triple_overlap_soundness() {
    let r = translate_fzn(
        "var 0..20: s1;\nvar 0..20: s2;\nvar 0..20: s3;\n\
         constraint fzn_cumulative([s1,s2,s3], [10,10,10], [2,2,2], 5);\n\
         solve satisfy;\n",
    );
    let smt = &r.smtlib;
    // Auxiliary variables with implications (not ite)
    let load_decl_count = smt.matches("(declare-const _cum").count();
    assert_eq!(load_decl_count, 9, "should have 9 load variables (3×3)");
    // No pairwise disjunctions should exist (old encoding artifact)
    let pairwise_count = smt.matches("(assert (or (>=").count();
    assert_eq!(
        pairwise_count, 0,
        "event-point encoding should not produce pairwise disjunctions"
    );
    // Each active condition appears in 2 implications (active => r, !active => 0)
    // 9 load vars × 2 = 18 occurrences of the overlap check pattern
    let active_count = smt.matches("(and (<= s").count();
    assert_eq!(
        active_count, 18,
        "should have 18 activity checks (9 load vars × 2 implications each)"
    );
}

// --- Edge cases ---

#[test]
fn test_empty_model() {
    let r = translate_fzn("solve satisfy;\n");
    assert!(r.smtlib.contains("(check-sat)"));
    assert!(r.output_vars.is_empty());
    assert!(r.objective.is_none());
}

#[test]
fn test_set_in_single_element() {
    let r = translate_fzn(
        "var int: x;\n\
         constraint set_in(x, {42});\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= x 42))"));
}

// --- Previously untested built-in constraints ---

include!("builtin_coverage/core_builtins.rs");

// --- Global: count_eq ---

#[test]
fn test_count_eq() {
    let r = translate_fzn(
        "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\nvar int: c;\n\
         constraint fzn_count_eq([x, y, z], 2, c);\nsolve satisfy;\n",
    );
    // count_eq encodes as sum of ite equality checks
    assert!(r.smtlib.contains("(ite (= x 2) 1 0)"));
    assert!(r.smtlib.contains("(ite (= y 2) 1 0)"));
    assert!(r.smtlib.contains("(ite (= z 2) 1 0)"));
}

// --- Array element access ---

#[test]
fn test_array_int_element() {
    let r = translate_fzn(
        "var 1..3: i;\nvar int: v;\n\
         constraint array_int_element(i, [10, 20, 30], v);\n\
         solve satisfy;\n",
    );
    // array_element builds 1-based ite chain: (ite (= i 1) 10 (ite (= i 2) 20 30))
    assert!(r
        .smtlib
        .contains("(assert (= v (ite (= i 1) 10 (ite (= i 2) 20 30))))"));
}

#[test]
fn test_array_var_int_element() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         var 1..3: i;\nvar int: v;\n\
         constraint array_var_int_element(i, [x, y, z], v);\n\
         solve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (= v (ite (= i 1) x (ite (= i 2) y z))))"));
}

#[test]
fn test_array_bool_element() {
    let r = translate_fzn(
        "var 1..2: i;\nvar bool: v;\n\
         constraint array_bool_element(i, [true, false], v);\n\
         solve satisfy;\n",
    );
    // Bool constants: true/false in the ite chain
    assert!(
        r.smtlib.contains("(ite (= i 1)"),
        "array_bool_element should produce ite chain: got {}",
        r.smtlib
    );
}

#[test]
fn test_array_var_bool_element() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: c;\n\
         var 1..3: i;\nvar bool: v;\n\
         constraint array_var_bool_element(i, [a, b, c], v);\n\
         solve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (= v (ite (= i 1) a (ite (= i 2) b c))))"));
}

#[test]
fn test_set_in_multi_element() {
    let r = translate_fzn(
        "var int: x;\n\
         constraint set_in(x, {1, 3, 5, 7});\nsolve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (or (= x 1) (= x 3) (= x 5) (= x 7)))"));
}

// --- Set variable constraints (boolean decomposition) ---

include!("builtin_coverage/set_variables.rs");

// --- Integer power: int_pow ---

include!("builtin_coverage/integer_power.rs");
