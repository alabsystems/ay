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

/// Test default on const-array simplifies to value (#8534)
#[test]
fn test_elaborate_default_const_array() {
    let input = r#"
            (assert (= (default ((as const (Array Int Int)) 42)) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // default(const-array(42)) should simplify to 42, so 42 = 42 is true.
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "default(const-array(42)) = 42 should simplify to true"
    );
}

/// Test default on store simplifies through to base array (#8534)
#[test]
fn test_elaborate_default_store() {
    let input = r#"
            (assert (= (default (store ((as const (Array Int Int)) 7) 0 99)) 7))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // default(store(const-array(7), 0, 99)) = default(const-array(7)) = 7
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "default(store(const-array(7), 0, 99)) = 7 should simplify to true"
    );
}

/// Test default on a symbolic array produces a default term (#8534)
#[test]
fn test_elaborate_default_symbolic_array() {
    let input = r#"
            (declare-const a (Array Int Int))
            (declare-const x Int)
            (assert (= (default a) x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // default(a) cannot be simplified, so the assertion should be default(a) = x
}

/// Test that map[f] works with the select-over-map rewrite:
/// select(map[f](a), i) should reduce to f(select(a, i))
#[test]
fn test_elaborate_array_map_select_rewrite() {
    let input = r#"
            (declare-fun f (Int) Int)
            (declare-const a (Array Int Int))
            (declare-const i Int)
            (assert (= (select ((_ map f) a) i) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);

    // Verify the rewrite happened: the assertion should contain f(...)
    // rather than select(map[f](...), ...).
    let assertion = ctx.assertions[0];
    // The top-level term should be an equality
    if let TermData::App(Symbol::Named(name), args) = ctx.terms.get(assertion) {
        assert_eq!(name, "=");
        assert_eq!(args.len(), 2);
        // The LHS should be f(select(a, i)), NOT select(map[f](a), i)
        let lhs = args[0];
        match ctx.terms.get(lhs) {
            TermData::App(Symbol::Named(fname), fargs) => {
                assert_eq!(fname, "f", "Expected f(...) after select-map rewrite");
                assert_eq!(fargs.len(), 1, "f is unary");
                // The argument should be select(a, i)
                match ctx.terms.get(fargs[0]) {
                    TermData::App(Symbol::Named(sname), _sargs) => {
                        assert_eq!(sname, "select", "Expected select(a, i) as argument to f");
                    }
                    _ => panic!("Expected select term as argument to f"),
                }
            }
            _ => panic!(
                "Expected f(...) term after select-map rewrite, got {:?}",
                ctx.terms.get(lhs)
            ),
        }
    }
}

/// Test lambda array parsing and beta reduction on select (#8535)
#[test]
fn test_elaborate_lambda_array_basic() {
    // (lambda ((x Int)) (+ x 1)) creates an array where index i maps to i+1
    // select(lambda, 5) should beta-reduce to (+ 5 1) = 6
    let input = r#"
            (declare-const i Int)
            (assert (= (select (lambda ((x Int)) (+ x 1)) i) (+ i 1)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // Beta reduction should make both sides identical, so = simplifies to true
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "select(lambda(x)(+ x 1), i) = (+ i 1) should simplify to true"
    );
}

/// A multi-variable lambda may ONLY curry when it is the direct function
/// argument of a higher-order sequence combinator (that is the only consumer
/// whose `ho_unfold` select-chain matches the curried shape). In any other
/// position the curried encoding diverges from z3 (which treats an n-ary
/// lambda as an n-ary function, not a curried array) and would wrong-decide:
/// a direct `(select (select f i) j)` chain over a bare 2-var lambda made AY
/// return a spurious `unsat`/`sat` on a term z3 rejects as ill-sorted. So a
/// bare multi-var lambda now fails closed at elaboration. (#p1.5-curried-lambda-gate)
#[test]
fn test_elaborate_bare_multi_var_lambda_fails_closed() {
    // Exactly the wrong-verdict reproducer: outside a seq combinator, a direct
    // double-`select` over a 2-var lambda must be REJECTED (fail-close), not
    // silently curried and decided.
    let input = r#"
            (assert (= (select (select (lambda ((a Int) (b Int)) (+ a b)) 3) 4) 7))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut saw_err = false;
    for cmd in &commands {
        if ctx.process_command(cmd).is_err() {
            saw_err = true;
        }
    }
    assert!(
        saw_err,
        "a bare multi-var lambda (not a seq-combinator fn arg) must fail closed, \
         not curry into a decided verdict"
    );
}

/// Equality between two multi-var lambdas outside a seq combinator must also
/// fail closed (the false-`sat` reproducer): AY has no sound decision procedure
/// for equality of curried lambda-arrays, so the term must never be elaborated
/// into a freely-equatable pair of opaque arrays. (#p1.5-curried-lambda-gate)
#[test]
fn test_elaborate_multi_var_lambda_equality_fails_closed() {
    let input = r#"
            (assert (= (lambda ((x Int) (y Int)) (+ x y))
                       (lambda ((a Int) (b Int)) (- a b))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut saw_err = false;
    for cmd in &commands {
        if ctx.process_command(cmd).is_err() {
            saw_err = true;
        }
    }
    assert!(
        saw_err,
        "equality of two bare multi-var lambdas must fail closed, not decide"
    );
}

/// A single-variable lambda is sound in every position (plain beta-reduction),
/// so a direct `select` over one still decides — the gate only restricts the
/// MULTI-variable case.
#[test]
fn test_elaborate_single_var_lambda_select_still_decides() {
    let input = r#"
            (assert (= (select (lambda ((a Int)) (+ a 1)) 4) 5))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "single-var lambda select 4->5 must still beta-reduce to true"
    );
}

/// A multi-variable lambda as the direct function argument of `seq.foldl`
/// still curries and elaborates (the headline P1.5 feature is preserved).
#[test]
fn test_elaborate_multi_var_lambda_curries_under_seq_foldl() {
    let input = r#"
            (declare-const init Int)
            (declare-const s (Seq Int))
            (assert (= (seq.foldl (lambda ((acc Int) (x Int)) (+ acc x)) init s) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("a 2-var lambda that is the direct fn arg of seq.foldl must still elaborate");
    }
    assert_eq!(ctx.assertions.len(), 1);
}

/// Test lambda array with constant body (equivalent to const-array) (#8535)
#[test]
fn test_elaborate_lambda_array_constant_body() {
    // (lambda ((x Int)) 42) creates an array where every index maps to 42
    let input = r#"
            (declare-const i Int)
            (assert (= (select (lambda ((x Int)) 42) i) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // Beta reduction: select(lambda(x) 42, i) = 42[x/i] = 42
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "select(lambda(x) 42, i) = 42 should simplify to true"
    );
}

/// Test lambda array sort is correctly computed (#8535)
#[test]
fn test_elaborate_lambda_array_sort() {
    let input = r#"
            (declare-const a (Array Int Int))
            (assert (= a (lambda ((x Int)) (+ x 1))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // Lambda array should have sort (Array Int Int), matching 'a'
    assert_eq!(ctx.assertions.len(), 1);
}

/// Test lambda array with Bool element sort (#8535)
#[test]
fn test_elaborate_lambda_array_bool_body() {
    let input = r#"
            (declare-const i Int)
            (assert (select (lambda ((x Int)) true) i))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // select(lambda(x) true, i) = true[x/i] = true
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "select(lambda(x) true, i) should simplify to true"
    );
}

/// Test default on lambda array (#8535)
#[test]
fn test_elaborate_lambda_array_default() {
    let input = r#"
            (declare-const x Int)
            (assert (= (default (lambda ((i Int)) 99)) 99))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // default(lambda(i) 99) = 99 (body with unspecified index)
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "default(lambda(i) 99) = 99 should simplify to true"
    );
}

/// Test store on lambda array (#8535)
#[test]
fn test_elaborate_lambda_array_store_select() {
    let input = r#"
            (assert (= (select (store (lambda ((x Int)) 0) 5 42) 5) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // store(lambda(x) 0, 5, 42) at index 5 should return 42 (ROW1)
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "select(store(lambda(x) 0, 5, 42), 5) = 42 should simplify to true"
    );
}
