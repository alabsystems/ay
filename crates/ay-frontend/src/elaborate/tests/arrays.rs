// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elaborate_array_select() {
    let input = r#"
            (declare-const a (Array Int Int))
            (assert (= (select a 0) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_array_store() {
    let input = r#"
            (declare-const a (Array Int Int))
            (declare-const b (Array Int Int))
            (assert (= (store a 0 42) b))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_array_select_rejects_wrong_index_sort_9699() {
    let input = r#"
            (declare-const a (Array Int Int))
            (assert (= (select a true) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let err = commands
        .iter()
        .try_for_each(|cmd| ctx.process_command(cmd).map(|_| ()))
        .unwrap_err();

    assert!(
        matches!(&err, ElaborateError::SortMismatch { expected, actual } if expected == "Int" && actual == "Bool"),
        "expected select index sort mismatch, got {err:?}"
    );
}

#[test]
fn test_elaborate_array_store_rejects_wrong_index_sort_9699() {
    let input = r#"
            (declare-const a (Array Int Int))
            (assert (= (store a true 42) a))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let err = commands
        .iter()
        .try_for_each(|cmd| ctx.process_command(cmd).map(|_| ()))
        .unwrap_err();

    assert!(
        matches!(&err, ElaborateError::SortMismatch { expected, actual } if expected == "Int" && actual == "Bool"),
        "expected store index sort mismatch, got {err:?}"
    );
}

#[test]
fn test_elaborate_array_store_rejects_wrong_value_sort_9699() {
    let input = r#"
            (declare-const a (Array Int Int))
            (assert (= (store a 0 true) a))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let err = commands
        .iter()
        .try_for_each(|cmd| ctx.process_command(cmd).map(|_| ()))
        .unwrap_err();

    assert!(
        matches!(&err, ElaborateError::SortMismatch { expected, actual } if expected == "Int" && actual == "Bool"),
        "expected store value sort mismatch, got {err:?}"
    );
}

#[test]
fn array_operators_reject_non_array_first_operands() {
    for input in [
        "(assert (select true false))",
        "(assert (= (store 0 0 1) 0))",
        "(assert (= (default 0) 0))",
    ] {
        let commands = parse(input).expect("wrong-sort array application still parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("array operation must reject a non-Array first operand");
        assert!(
            matches!(
                error,
                ElaborateError::SortMismatch { ref expected, .. }
                    if expected.starts_with("Array:")
            ),
            "expected Array sort mismatch for `{input}`, got {error:?}"
        );
    }
}

#[test]
fn test_elaborate_array_select_store_composition() {
    let input = r#"
            (declare-const a (Array Int Int))
            (assert (= (select (store a 0 42) 0) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_const_array() {
    let input = r#"
            (declare-const x Int)
            (assert (= (select ((as const (Array Int Int)) 0) x) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    // The assertion should simplify to (= 0 0) which is true
}

#[test]
fn test_elaborate_const_array_bool() {
    let input = r#"
            (declare-const i Int)
            (assert (select ((as const (Array Int Bool)) true) i))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

#[test]
fn test_elaborate_const_array_with_store() {
    let input = r#"
            (assert (= (select (store ((as const (Array Int Int)) 0) 5 100) 5) 100))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

/// Regression test for #6124: const array with BV index sort.
/// Now uses `SExpr::to_raw_string()` (#6125) so `_` and `as` are not quoted.
#[test]
fn test_elaborate_const_array_bv_index_sort_6124() {
    let input = r#"
            (set-logic QF_AUFBV)
            (declare-const P (_ BitVec 32))
            (declare-const V (Array (_ BitVec 32) Bool))
            (assert (and
                (= P (_ bv0 32))
                (= V (store ((as const (Array (_ BitVec 32) Bool)) false) P true))
                (not (select V P))))
            (check-sat)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // Formula should parse without errors; the const array index sort
    // (_ BitVec 32) must be resolved as BitVec(32), not Uninterpreted.
    assert_eq!(ctx.assertions.len(), 1);
}

/// Test nested Array sorts via QualifiedApp: (Array (_ BitVec 32) (_ BitVec 64))
#[test]
fn test_elaborate_const_array_bv_both_sorts() {
    let input = r#"
            (declare-const idx (_ BitVec 32))
            (assert (= (select ((as const (Array (_ BitVec 32) (_ BitVec 64))) (_ bv0 64)) idx) (_ bv0 64)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
}

/// Test map[f] array operation: ((_ map f) a1 ... an) (#8533)
/// Verifies that (select ((_ map f) a1 a2) i) rewrites to (f (select a1 i) (select a2 i)).
#[test]
fn test_elaborate_array_map_binary_function() {
    let input = r#"
            (declare-fun f (Int Int) Int)
            (declare-const a (Array Int Int))
            (declare-const b (Array Int Int))
            (declare-const i Int)
            (assert (= (select ((_ map f) a b) i) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // The assertion should parse successfully. The select-over-map
    // is rewritten to f(select(a, i), select(b, i)) = 42.
    assert_eq!(ctx.assertions.len(), 1);
}

/// Test map[not] for set complement: ((_ map not) s) where s : (Array Int Bool)
#[test]
fn test_elaborate_array_map_not_set_complement() {
    let input = r#"
            (declare-fun not (Bool) Bool)
            (declare-const s (Array Int Bool))
            (declare-const i Int)
            (assert (select ((_ map not) s) i))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
}

/// Test map[f] with unary function
#[test]
fn test_elaborate_array_map_unary_function() {
    let input = r#"
            (declare-fun inc (Int) Int)
            (declare-const a (Array Int Int))
            (assert (= (select ((_ map inc) a) 0) 1))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
}

/// Test map[f] sort computation: result is (Array IndexSort ReturnSort)
#[test]
fn test_elaborate_array_map_sort() {
    let input = r#"
            (declare-fun f (Int) Bool)
            (declare-const a (Array Int Int))
            (declare-const m (Array Int Bool))
            (assert (= ((_ map f) a) m))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // map[f : Int -> Bool](a : Array Int Int) should have sort (Array Int Bool),
    // which matches m. The assertion should parse and elaborate successfully.
    assert_eq!(ctx.assertions.len(), 1);
}

/// Test map[f] error: wrong number of array arguments
#[test]
fn test_elaborate_array_map_arity_mismatch() {
    let input = r#"
            (declare-fun f (Int Int) Int)
            (declare-const a (Array Int Int))
            (assert (= (select ((_ map f) a) 0) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut had_error = false;
    for cmd in &commands {
        if ctx.process_command(cmd).is_err() {
            had_error = true;
        }
    }
    assert!(had_error, "Expected error for arity mismatch in map[f]");
}

/// Test map[f] error: non-array argument
#[test]
fn test_elaborate_array_map_non_array_arg() {
    let input = r#"
            (declare-fun f (Int) Int)
            (declare-const x Int)
            (assert (= ((_ map f) x) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut had_error = false;
    for cmd in &commands {
        if ctx.process_command(cmd).is_err() {
            had_error = true;
        }
    }
    assert!(had_error, "Expected error for non-array argument to map[f]");
}

/// Test as-array: (_ as-array f) creates an array from a function (#8534)
#[test]
fn test_elaborate_as_array_basic() {
    let input = r#"
            (declare-fun f (Int) Int)
            (declare-const i Int)
            (assert (= (select (_ as-array f) i) (f i)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // select(as-array(f), i) should rewrite to f(i), making both sides identical.
    // The equality f(i) = f(i) should simplify to true.
    assert_eq!(ctx.assertions.len(), 1);
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "select(as-array(f), i) = f(i) should simplify to true"
    );
}

/// Test as-array with Bool return sort (#8534)
#[test]
fn test_elaborate_as_array_bool_return() {
    let input = r#"
            (declare-fun p (Int) Bool)
            (declare-const x Int)
            (assert (select (_ as-array p) x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // The assertion should be p(x), not select(as-array(p), x)
    let assertion = ctx.assertions[0];
    match ctx.terms.get(assertion) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "p", "Expected p(...) after select-as-array rewrite");
            assert_eq!(args.len(), 1);
        }
        _ => panic!("Expected p(x) after as-array rewrite"),
    }
}

/// Test as-array error: function has wrong arity (#8534)
#[test]
fn test_elaborate_as_array_wrong_arity() {
    let input = r#"
            (declare-fun g (Int Int) Int)
            (assert (= (_ as-array g) (_ as-array g)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut had_error = false;
    for cmd in &commands {
        if ctx.process_command(cmd).is_err() {
            had_error = true;
        }
    }
    assert!(
        had_error,
        "Expected error: as-array requires a unary function"
    );
}

#[test]
fn as_array_rejects_ambiguous_unary_overload() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-fun f (Bool) Bool) \
         (assert (= (_ as-array f) (_ as-array f)))",
    )
    .unwrap();
    let mut ctx = Context::new();
    assert!(
        commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .is_err(),
        "as-array has no operand domain with which to disambiguate two unary overloads"
    );
}

#[test]
fn indexed_as_array_preserves_native_alias_identity() {
    let mut ctx = Context::new();
    ctx.register_native_function_alias(
        "surface".to_string(),
        "!private-as-array".to_string(),
        vec![Sort::Int],
        Sort::Bool,
    )
    .unwrap();
    let commands = parse("(declare-const i Int) (assert (select (_ as-array surface) i))").unwrap();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }
    let TermData::App(Symbol::Named(name), _) = ctx.terms.get(ctx.assertions[0]) else {
        panic!("select(as-array(alias), i) must rewrite to the selected function");
    };
    assert_eq!(name, "!private-as-array");
}

include!("arrays/default_map_and_lambda.rs");
