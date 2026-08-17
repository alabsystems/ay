// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `builtin_coverage` to preserve test FQNs.

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
