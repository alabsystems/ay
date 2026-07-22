// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AUFLIA model extraction tests.
//!
//! Consumer: verification-consumer uses AUFLIA for separation logic verification and needs
//! correct model values for arrays, UF, and LIA terms. These tests verify
//! that the combined model extraction (EUF + LIA + Arrays) produces
//! consistent values.

use ay_frontend::sexp::{parse_sexp, SExpr};

fn get_value_binding(line: &str, name: &str) -> Option<SExpr> {
    let parsed = parse_sexp(line).ok()?;
    let SExpr::List(ref bindings) = parsed else {
        return None;
    };
    for binding in bindings {
        let SExpr::List(ref items) = binding else {
            continue;
        };
        if items.len() != 2 {
            continue;
        }
        if items[0].as_symbol() == Some(name) {
            return Some(items[1].clone());
        }
    }
    None
}

fn get_value_binding_for_expr(line: &str, expr: &str) -> Option<SExpr> {
    let expected = parse_sexp(expr).ok()?;
    let parsed = parse_sexp(line).ok()?;
    let SExpr::List(ref bindings) = parsed else {
        return None;
    };
    for binding in bindings {
        let SExpr::List(ref items) = binding else {
            continue;
        };
        if items.len() != 2 {
            continue;
        }
        if items[0] == expected {
            return Some(items[1].clone());
        }
    }
    None
}

fn get_binding_values(line: &str) -> Vec<i64> {
    let parsed = parse_sexp(line)
        .unwrap_or_else(|err| panic!("parse get-value output failed: {err}: {line}"));
    let SExpr::List(ref bindings) = parsed else {
        panic!("expected get-value bindings, got {line}");
    };
    bindings
        .iter()
        .map(|binding| {
            let SExpr::List(ref items) = binding else {
                panic!("expected binding pair, got {binding:?} in {line}");
            };
            assert!(
                items.len() == 2,
                "expected 2-item binding, got {items:?} in {line}"
            );
            sexpr_to_i64(&items[1]).unwrap_or_else(|| panic!("expected integer value in {line}"))
        })
        .collect()
}

fn sexpr_to_i64(expr: &SExpr) -> Option<i64> {
    match expr {
        SExpr::Numeral(numeral) => numeral.parse::<i64>().ok(),
        SExpr::List(items)
            if items.len() == 2
                && items[0].as_symbol() == Some("-")
                && items[1].as_numeral().is_some() =>
        {
            items[1]
                .as_numeral()?
                .parse::<i64>()
                .ok()
                .map(|value| -value)
        }
        _ => None,
    }
}

/// Basic AUFLIA model extraction: array store/select with LIA index.
/// Verifies that the model correctly reflects stored values.
#[test]
fn test_auflia_model_store_select_value() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun v () Int)

(assert (= i 3))
(assert (= v 42))
(assert (= (select (store a i v) i) 42))
(check-sat)
(get-value (i v (select (store a i v) i)))
"#,
    );
    assert_eq!(
        outputs.len(),
        2,
        "expected sat + get-value, got: {outputs:?}"
    );
    assert_eq!(outputs[0].trim(), "sat", "should be sat: {outputs:?}");
    let value_line = &outputs[1];
    let i_val =
        sexpr_to_i64(&get_value_binding(value_line, "i").expect("missing get-value binding for i"))
            .expect("i should be an integer");
    let v_val =
        sexpr_to_i64(&get_value_binding(value_line, "v").expect("missing get-value binding for v"))
            .expect("v should be an integer");
    assert_eq!(i_val, 3, "expected i = 3, got {i_val} from {value_line}");
    assert_eq!(v_val, 42, "expected v = 42, got {v_val} from {value_line}");
    assert_eq!(
        get_binding_values(value_line),
        vec![3, 42, 42],
        "expected get-value results [3, 42, 42], got {value_line}"
    );
}

/// AUFLIA model: UF function values consistent with LIA equalities.
/// Tests that when f(x) = f(y) is asserted with x = y, the model
/// correctly assigns f(x) and f(y) the same value.
#[test]
fn test_auflia_model_uf_consistency_with_lia() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic AUFLIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun f (Int) Int)

(assert (= x y))
(assert (= (f x) 7))
(check-sat)
(get-value (x y (f x) (f y)))
"#,
    );
    assert_eq!(
        outputs.len(),
        2,
        "expected sat + get-value, got: {outputs:?}"
    );
    assert_eq!(outputs[0].trim(), "sat", "should be sat: {outputs:?}");
    let value_line = &outputs[1];
    let x_val =
        sexpr_to_i64(&get_value_binding(value_line, "x").expect("missing get-value binding for x"))
            .expect("x should be an integer");
    let y_val =
        sexpr_to_i64(&get_value_binding(value_line, "y").expect("missing get-value binding for y"))
            .expect("y should be an integer");
    let fx_val = sexpr_to_i64(
        &get_value_binding_for_expr(value_line, "(f x)").expect("missing get-value for (f x)"),
    )
    .expect("f(x) should be an integer");
    let fy_val = sexpr_to_i64(
        &get_value_binding_for_expr(value_line, "(f y)").expect("missing get-value for (f y)"),
    )
    .expect("f(y) should be an integer");
    assert_eq!(x_val, y_val, "expected x = y in model, got {value_line}");
    assert_eq!(fx_val, 7, "expected f(x) = 7, got {value_line}");
    assert_eq!(fy_val, 7, "expected f(y) = 7, got {value_line}");
}

/// AUFLIA model: nested store chain with distinct indices.
/// Verifies that model reports correct values at each index of a
/// multi-write array.
#[test]
fn test_auflia_model_nested_store_chain() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic AUFLIA)
(declare-fun a () (Array Int Int))

; Write 10 at index 0, 20 at index 1, 30 at index 2
(define-fun b () (Array Int Int) (store a 0 10))
(define-fun c () (Array Int Int) (store b 1 20))
(define-fun d () (Array Int Int) (store c 2 30))

(assert (= (select d 0) 10))
(assert (= (select d 1) 20))
(assert (= (select d 2) 30))
(check-sat)
(get-value ((select d 0) (select d 1) (select d 2)))
"#,
    );
    assert_eq!(
        outputs.len(),
        2,
        "expected sat + get-value, got: {outputs:?}"
    );
    assert_eq!(outputs[0].trim(), "sat", "should be sat: {outputs:?}");
    let value_line = &outputs[1];
    assert_eq!(
        get_binding_values(value_line),
        vec![10, 20, 30],
        "expected get-value results [10, 20, 30], got {value_line}"
    );
}

/// AUFLIA model: array with UF-derived index equality.
/// When EUF derives i = j via UF congruence, the model should reflect
/// that select(a, i) = select(a, j).
#[test]
fn test_auflia_model_uf_derived_index_equality() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)

; UF injectivity forces x = y
(assert (= (f x) (f y)))
(assert (forall ((u Int) (v Int)) (=> (= (f u) (f v)) (= u v))))

; Array constraint
(assert (= (select a x) 100))

(check-sat)
(get-value (x y (select a x) (select a y)))
"#,
    );
    assert_eq!(
        outputs.len(),
        2,
        "expected sat + get-value, got: {outputs:?}"
    );
    assert!(
        matches!(outputs[0].trim(), "sat" | "unknown"),
        "should be sat or sound unknown: {outputs:?}"
    );
    if outputs[0].trim() == "unknown" {
        return;
    }
    let value_line = &outputs[1];
    let x_val =
        sexpr_to_i64(&get_value_binding(value_line, "x").expect("missing get-value binding for x"))
            .expect("x should be an integer");
    let y_val =
        sexpr_to_i64(&get_value_binding(value_line, "y").expect("missing get-value binding for y"))
            .expect("y should be an integer");
    let ax = sexpr_to_i64(
        &get_value_binding_for_expr(value_line, "(select a x)")
            .expect("missing get-value for (select a x)"),
    )
    .expect("select a x should be an integer");
    let ay = sexpr_to_i64(
        &get_value_binding_for_expr(value_line, "(select a y)")
            .expect("missing get-value for (select a y)"),
    )
    .expect("select a y should be an integer");
    assert_eq!(x_val, y_val, "expected x = y in model, got {value_line}");
    assert_eq!(ax, 100, "expected select(a, x) = 100, got {value_line}");
    assert_eq!(ay, 100, "expected select(a, y) = 100, got {value_line}");
}

/// AUFLIA model extraction across push/pop scopes.
/// Verifies that model values in different scopes are independent.
#[test]
fn test_auflia_model_across_push_pop() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun x () Int)

(push 1)
(assert (= (select a 0) 10))
(assert (= x 5))
(check-sat)
(get-value ((select a 0) x))
(pop 1)

(push 1)
(assert (= (select a 0) 99))
(assert (= x 77))
(check-sat)
(get-value ((select a 0) x))
(pop 1)
"#,
    );
    assert_eq!(
        outputs.len(),
        4,
        "expected sat/get-value/sat/get-value, got: {outputs:?}"
    );
    assert_eq!(
        outputs[0].trim(),
        "sat",
        "first scope should be sat: {outputs:?}"
    );
    let first_values = &outputs[1];
    let first_select = sexpr_to_i64(
        &get_value_binding_for_expr(first_values, "(select a 0)")
            .expect("missing first-scope get-value for (select a 0)"),
    )
    .expect("first-scope select should be an integer");
    let first_x = sexpr_to_i64(
        &get_value_binding(first_values, "x").expect("missing first-scope get-value for x"),
    )
    .expect("first-scope x should be an integer");
    assert_eq!(
        first_select, 10,
        "expected scope-1 select(a,0)=10, got {first_values}"
    );
    assert_eq!(first_x, 5, "expected scope-1 x=5, got {first_values}");

    assert_eq!(
        outputs[2].trim(),
        "sat",
        "second scope should be sat: {outputs:?}"
    );
    let second_values = &outputs[3];
    let second_select = sexpr_to_i64(
        &get_value_binding_for_expr(second_values, "(select a 0)")
            .expect("missing second-scope get-value for (select a 0)"),
    )
    .expect("second-scope select should be an integer");
    let second_x = sexpr_to_i64(
        &get_value_binding(second_values, "x").expect("missing second-scope get-value for x"),
    )
    .expect("second-scope x should be an integer");
    assert_eq!(
        second_select, 99,
        "expected scope-2 select(a,0)=99, got {second_values}"
    );
    assert_eq!(second_x, 77, "expected scope-2 x=77, got {second_values}");
}

/// AUFLIA model: array with quantified axiom (verification-consumer pattern).
/// Tests the typical verification-consumer pattern of quantified array bridge axioms
/// with ground term seeding.
#[test]
fn test_auflia_model_verification_consumer_pattern_quantified_array() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic AUFLIA)
(declare-sort Heap 0)
(declare-fun heap_array (Heap) (Array Int Int))
(declare-fun heap_read (Heap Int) Int)

; Bridge axiom: heap_read(h, i) = select(heap_array(h), i)
(assert (forall ((h Heap) (i Int))
    (! (= (heap_read h i) (select (heap_array h) i))
       :pattern ((heap_read h i)))))

(declare-const h Heap)

; Write 42 at address 10
(assert (= (select (heap_array h) 10) 42))

; Ground seed
(assert (= (heap_read h 10) (select (heap_array h) 10)))

(check-sat)
(get-value ((heap_read h 10)))
"#,
    );
    assert_eq!(
        outputs.len(),
        2,
        "expected sat + get-value, got: {outputs:?}"
    );
    assert!(
        matches!(outputs[0].trim(), "sat" | "unknown"),
        "should be sat or sound unknown: {outputs:?}"
    );
    if outputs[0].trim() == "unknown" {
        return;
    }
    let value_line = &outputs[1];
    let heap_read = sexpr_to_i64(
        &get_value_binding_for_expr(value_line, "(heap_read h 10)")
            .expect("missing get-value for (heap_read h 10)"),
    )
    .expect("heap_read(h,10) should be an integer");
    assert_eq!(
        heap_read, 42,
        "expected heap_read(h,10) = 42 via bridge axiom, got {value_line}"
    );
}
