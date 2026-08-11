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

#[test]
fn test_int_eq() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_eq(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= x y))"));
}

#[test]
fn test_int_ne() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_ne(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= x y)))"));
}

#[test]
fn test_int_lt() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lt(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (< x y))"));
}

#[test]
fn test_int_le() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_le(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (<= x y))"));
}

#[test]
fn test_bool_not() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\n\
         constraint bool_not(a, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (not a)))"));
    assert!(r.smtlib.contains("(assert (=> (not a) b))"));
}

#[test]
fn test_bool_and() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: r;\n\
         constraint bool_and(a, b, r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (and a b)))"));
    assert!(r.smtlib.contains("(assert (=> (and a b) r))"));
}

#[test]
fn test_bool_or() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: r;\n\
         constraint bool_or(a, b, r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (or a b)))"));
    assert!(r.smtlib.contains("(assert (=> (or a b) r))"));
}

#[test]
fn test_bool_clause() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: c;\n\
         constraint bool_clause([a, b], [c]);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (or a b (not c)))"));
}

#[test]
fn test_int_plus() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_plus(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= z (+ x y)))"));
}

#[test]
fn test_int_times() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_times(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= z (* x y)))"));
}

#[test]
fn test_int_abs() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_abs(x, y);\nsolve satisfy;\n",
    );
    // int_abs uses ite encoding: y = (ite (>= x 0) x (- x))
    assert!(r.smtlib.contains("(assert (= y (ite (>= x 0) x (- x))))"));
}

#[test]
fn test_int_min() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_min(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= z (ite (<= x y) x y)))"));
}

#[test]
fn test_int_max() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_max(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= z (ite (>= x y) x y)))"));
}

#[test]
fn test_int_lin_eq() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lin_eq([2, 3], [x, y], 10);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= (+ (* 2 x) (* 3 y)) 10))"));
}

#[test]
fn test_int_lin_le() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lin_le([1, 1], [x, y], 5);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (<= (+ x y) 5))"));
}

#[test]
fn test_int_lin_ne() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lin_ne([1, 1], [x, y], 10);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= (+ x y) 10)))"));
}

#[test]
fn test_bool2int() {
    let r = translate_fzn(
        "var bool: b;\nvar int: x;\n\
         constraint bool2int(b, x);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= x (ite b 1 0)))"));
}

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
fn test_array_bool_or() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: c;\nvar bool: r;\n\
         constraint array_bool_or([a, b, c], r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (or a b c)))"));
    assert!(r.smtlib.contains("(assert (=> (or a b c) r))"));
}

#[test]
fn test_array_bool_xor() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: c;\n\
         constraint array_bool_xor([a, b, c]);\nsolve satisfy;\n",
    );
    // SMT-LIB xor is binary, so 3-element xor chains: (xor a (xor b c))
    assert!(r.smtlib.contains("(assert (xor a (xor b c)))"));
}

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
fn test_int_lt_reif() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar bool: b;\n\
         constraint int_lt_reif(x, y, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (< x y)))"));
    assert!(r.smtlib.contains("(assert (=> (< x y) b))"));
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

#[test]
fn test_set_var_declaration() {
    let r = translate_fzn("var set of 0..3: s;\nsolve satisfy;\n");
    // var set of 0..3 → 4 boolean variables s__bit__0 .. s__bit__3
    assert!(r.smtlib.contains("(declare-const s__bit__0 Bool)"));
    assert!(r.smtlib.contains("(declare-const s__bit__3 Bool)"));
}

#[test]
fn test_set_card() {
    let r = translate_fzn(
        "var set of 0..3: s;\n\
         constraint set_card(s, 2);\nsolve satisfy;\n",
    );
    // Popcount: sum of boolean ite chains = 2
    assert!(r.smtlib.contains("(ite s__bit__0 1 0)"));
    assert!(r.smtlib.contains("(ite s__bit__3 1 0)"));
}

#[test]
fn test_set_union() {
    let r = translate_fzn(
        "var set of 0..3: s1;\nvar set of 0..3: s2;\nvar set of 0..3: s3;\n\
         constraint set_union(s1, s2, s3);\nsolve satisfy;\n",
    );
    // Per-bit union: s3__bit__i = s1__bit__i or s2__bit__i
    assert!(r
        .smtlib
        .contains("(assert (= s3__bit__0 (or s1__bit__0 s2__bit__0)))"));
    assert!(r
        .smtlib
        .contains("(assert (= s3__bit__3 (or s1__bit__3 s2__bit__3)))"));
}

#[test]
fn test_set_in_reif_with_set_var() {
    let r = translate_fzn(
        "var set of 0..3: s;\nvar bool: b;\n\
         constraint set_in_reif(2, s, b);\nsolve satisfy;\n",
    );
    // Element 2 in set of 0..3 → bit 2
    assert!(r.smtlib.contains("(assert (=> b s__bit__2))"));
    assert!(r.smtlib.contains("(assert (=> s__bit__2 b))"));
}

#[test]
fn test_set_in_with_set_var() {
    let r = translate_fzn(
        "var 0..3: x;\nvar set of 0..3: s;\n\
         constraint set_in(x, s);\nsolve satisfy;\n",
    );
    // set_in with set variable builds a disjunction over the domain
    assert!(r.smtlib.contains("(and (= x 0) s__bit__0)"));
    assert!(r.smtlib.contains("(and (= x 3) s__bit__3)"));
}

#[test]
fn test_array_set_element() {
    let r = translate_fzn(
        "array [1..3] of set of int: arr = [{0, 2}, {1, 3}, {0, 1, 2, 3}];\n\
         var 1..3: i;\nvar set of 0..3: s;\n\
         constraint array_set_element(i, arr, s);\nsolve satisfy;\n",
    );
    // Per-bit ITE chain over array.
    // Bit 0 (element 0): {0,2} has 0→true, {1,3} no→false, {0,1,2,3} has 0→true
    // Expected: (assert (= s__bit__0 (ite (= i 1) true (ite (= i 2) false true))))
    assert!(
        r.smtlib
            .contains("(assert (= s__bit__0 (ite (= i 1) true (ite (= i 2) false true))))"),
        "bit 0 ITE chain incorrect.\nSMT:\n{}",
        r.smtlib
    );
    // Bit 1 (element 1): {0,2} no→false, {1,3} has 1→true, {0,1,2,3} has 1→true
    // Expected: (assert (= s__bit__1 (ite (= i 1) false (ite (= i 2) true true))))
    assert!(
        r.smtlib
            .contains("(assert (= s__bit__1 (ite (= i 1) false (ite (= i 2) true true))))"),
        "bit 1 ITE chain incorrect.\nSMT:\n{}",
        r.smtlib
    );
    // Bit 3 (element 3): {0,2} no→false, {1,3} has 3→true, {0,1,2,3} has 3→true
    // Expected: (assert (= s__bit__3 (ite (= i 1) false (ite (= i 2) true true))))
    assert!(
        r.smtlib
            .contains("(assert (= s__bit__3 (ite (= i 1) false (ite (= i 2) true true))))"),
        "bit 3 ITE chain incorrect.\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_set_in_reif_element_outside_domain() {
    // Element 10 is outside domain 0..3 → membership is always false → (assert (not b))
    let r = translate_fzn(
        "var set of 0..3: s;\nvar bool: b;\n\
         constraint set_in_reif(10, s, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not b))"));
}

#[test]
fn test_set_in_reif_element_below_domain() {
    // Element -1 is below domain 0..3 → membership is always false
    let r = translate_fzn(
        "var set of 0..3: s;\nvar bool: b;\n\
         constraint set_in_reif(-1, s, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not b))"));
}

#[test]
fn test_set_in_var_single_element_domain() {
    // When the set domain has width 1 (e.g., var set of 5..5), set_in_var
    // takes the single-conjunct branch emitting bare (assert ...) without (or ...).
    let r = translate_fzn(
        "var 5..5: x;\nvar set of 5..5: s;\n\
         constraint set_in(x, s);\nsolve satisfy;\n",
    );
    // Single element: (and (= x 5) s__bit__0)
    assert!(
        r.smtlib.contains("(and (= x 5) s__bit__0)"),
        "single-element set_in should produce (and (= x 5) s__bit__0).\nSMT:\n{}",
        r.smtlib
    );
    // Must NOT have (or ...) wrapper since there's only one disjunct
    assert!(
        !r.smtlib.contains("(assert (or (and (= x 5) s__bit__0))"),
        "single-element set_in should not use (or) wrapper"
    );
}

#[test]
fn test_array_set_element_single_array() {
    // Single-element array: array_set_element(i, [{0,2}], s) with i = 1.
    // No ITE chain needed — each bit is directly true/false.
    let r = translate_fzn(
        "array [1..1] of set of int: arr = [{0, 2}];\n\
         var 1..1: i;\nvar set of 0..2: s;\n\
         constraint array_set_element(i, arr, s);\nsolve satisfy;\n",
    );
    // Bit 0 (element 0): {0,2} has 0 → true. Single array element, no ITE.
    assert!(
        r.smtlib.contains("(assert (= s__bit__0 true))"),
        "single-element array: bit 0 should be true.\nSMT:\n{}",
        r.smtlib
    );
    // Bit 1 (element 1): {0,2} no → false.
    assert!(
        r.smtlib.contains("(assert (= s__bit__1 false))"),
        "single-element array: bit 1 should be false.\nSMT:\n{}",
        r.smtlib
    );
    // Bit 2 (element 2): {0,2} has 2 → true.
    assert!(
        r.smtlib.contains("(assert (= s__bit__2 true))"),
        "single-element array: bit 2 should be true.\nSMT:\n{}",
        r.smtlib
    );
}

// --- Integer power: int_pow ---

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
