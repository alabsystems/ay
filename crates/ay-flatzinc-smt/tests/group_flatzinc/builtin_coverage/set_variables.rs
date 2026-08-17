// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `builtin_coverage` to preserve test FQNs.

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
