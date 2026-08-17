// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

// --- Array element tests ---

#[test]
fn test_array_int_element() {
    let r = translate_fzn(
        "var 1..3: idx;\narray [1..3] of var 1..5: arr;\nvar 1..5: val;\n\
         constraint array_int_element(idx, arr, val);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= val (ite (= idx 1) arr_1"));
}

#[test]
fn test_array_int_element_adds_index_range_guard() {
    let r = translate_fzn(
        "var int: idx;\n\
         var 0..40: val;\n\
         constraint array_int_element(idx, [10, 20, 30], val);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (and (>= idx 1) (<= idx 3)))"));
}

#[test]
fn test_array_var_int_element_adds_index_range_guard() {
    let r = translate_fzn(
        "var int: idx;\n\
         var 0..40: x;\n\
         var 0..40: y;\n\
         var 0..40: z;\n\
         var 0..40: val;\n\
         constraint array_var_int_element(idx, [x, y, z], val);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (and (>= idx 1) (<= idx 3)))"));
}

#[test]
fn test_array_var_int_element_out_of_range_zero_keeps_index_guard() {
    let r = translate_fzn(
        "var int: idx;\n\
         var 0..40: x;\n\
         var 0..40: y;\n\
         var 0..40: z;\n\
         var 0..40: val;\n\
         constraint int_eq(idx, 0);\n\
         constraint array_var_int_element(idx, [x, y, z], val);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= idx 0))"));
    assert!(r.smtlib.contains("(assert (and (>= idx 1) (<= idx 3)))"));
}

#[test]
fn test_array_bool_element_adds_index_range_guard() {
    let r = translate_fzn(
        "var int: idx;\n\
         var bool: val;\n\
         constraint array_bool_element(idx, [true, false], val);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (and (>= idx 1) (<= idx 2)))"));
}

#[test]
fn test_array_var_bool_element_out_of_range_zero_keeps_index_guard() {
    let r = translate_fzn(
        "var int: idx;\n\
         var bool: a;\n\
         var bool: b;\n\
         var bool: val;\n\
         constraint int_eq(idx, 0);\n\
         constraint array_var_bool_element(idx, [a, b], val);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= idx 0))"));
    assert!(r.smtlib.contains("(assert (and (>= idx 1) (<= idx 2)))"));
}

#[test]
fn test_array_int_element_rejects_empty_array() {
    let err = translate_fzn_err(
        "var 1..1: idx;\n\
         var 0..1: val;\n\
         constraint array_int_element(idx, [], val);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref msg)
            if msg.contains("array_int_element: empty array")),
        "expected array_int_element empty array rejection, got: {err}"
    );
}

#[test]
fn test_array_set_element_adds_index_range_guard() {
    let r = translate_fzn(
        "array [1..2] of set of int: arr = [{0}, {1}];\n\
         var int: idx;\n\
         var set of 0..1: s;\n\
         constraint array_set_element(idx, arr, s);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (and (>= idx 1) (<= idx 2)))"));
}

#[test]
fn test_array_set_element_uses_named_array_lower_bound() {
    let r = translate_fzn(
        "array [0..1] of set of int: arr = [{0}, {1}];\n\
         var 0..0: idx;\n\
         var set of 0..1: s;\n\
         constraint array_set_element(idx, arr, s);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (and (>= idx 0) (<= idx 1)))"));
    assert!(
        r.smtlib
            .contains("(assert (= s__bit__0 (ite (= idx 0) true false)))"),
        "array_set_element should select the first entry at its declared lower bound.\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_array_set_element_constrains_source_members_outside_result_domain() {
    let parameter = translate_fzn(
        "array [1..1] of set of int: arr = [{2}];\n\
         var 1..1: idx;\n\
         var set of 1..1: result;\n\
         constraint array_set_element(idx, arr, result);\n\
         solve satisfy;\n",
    );
    assert!(
        parameter.smtlib.contains("(assert (= false true))"),
        "source members outside the result domain must make equality impossible.\nSMT:\n{}",
        parameter.smtlib
    );

    let variables = translate_fzn(
        "var set of 2..2: source;\n\
         array [1..1] of var set of 2..2: arr = [source];\n\
         var 1..1: idx;\n\
         var set of 1..1: result;\n\
         constraint set_in(2, source);\n\
         constraint array_set_element(idx, arr, result);\n\
         solve satisfy;\n",
    );
    assert!(
        variables
            .smtlib
            .contains("(assert (= false source__bit__0))"),
        "set-variable sources must also be compared outside the result domain.\nSMT:\n{}",
        variables.smtlib
    );
}

#[test]
fn test_array_set_element_rejects_empty_array() {
    let err = translate_fzn_err(
        "array [1..0] of set of int: arr = [];\n\
         var 1..1: idx;\n\
         var set of 0..1: s;\n\
         constraint array_set_element(idx, arr, s);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref msg)
            if msg.contains("array_set_element: empty array")),
        "expected array_set_element empty array rejection, got: {err}"
    );
}

#[test]
fn test_array_set_element_accepts_set_variable_array_literal() {
    let r = translate_fzn(
        "var set of 0..1: a;\n\
         var set of 0..1: b;\n\
         var int: idx;\n\
         var set of 0..1: s;\n\
         constraint array_set_element(idx, [a, b], s);\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (and (>= idx 1) (<= idx 2)))"));
    assert!(
        r.smtlib
            .contains("(assert (= s__bit__0 (ite (= idx 1) a__bit__0 b__bit__0)))"),
        "array_set_element should select the source set variable bit at FlatZinc index 1.\nSMT:\n{}",
        r.smtlib
    );
    assert!(
        r.smtlib
            .contains("(assert (= s__bit__1 (ite (= idx 1) a__bit__1 b__bit__1)))"),
        "array_set_element should select the source set variable bit at FlatZinc index 1.\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_array_set_element_accepts_named_set_variable_array() {
    let r = translate_fzn(
        "var set of 0..1: a;\n\
         var set of 0..1: b;\n\
         array [-1..0] of var set of 0..1: arr = [a, b];\n\
         var int: idx;\n\
         var set of 0..1: s;\n\
         constraint array_set_element(idx, arr, s);\n\
         solve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (and (>= idx (- 1)) (<= idx 0)))"));
    assert!(
        r.smtlib
            .contains("(assert (= s__bit__0 (ite (= idx (- 1)) a__bit__0 b__bit__0)))"),
        "named set array should select source set variable bits by FlatZinc index.\nSMT:\n{}",
        r.smtlib
    );
}

#[test]
fn test_array_set_element_rejects_empty_array_literal() {
    let err = translate_fzn_err(
        "var 1..1: idx;\n\
         var set of 0..1: s;\n\
         constraint array_set_element(idx, [], s);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref msg)
            if msg.contains("array_set_element: empty array")),
        "expected array_set_element empty array literal rejection, got: {err}"
    );
}

#[test]
fn test_array_set_element_rejects_empty_named_set_variable_array() {
    let err = translate_fzn_err(
        "array [1..0] of var set of 0..1: arr = [];\n\
         var 1..1: idx;\n\
         var set of 0..1: s;\n\
         constraint array_set_element(idx, arr, s);\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref msg)
            if msg.contains("array_set_element: empty array")),
        "expected array_set_element empty named array rejection, got: {err}"
    );
}
