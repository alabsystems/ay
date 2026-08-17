// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `elaborate::tests::arrays` to preserve test FQNs.

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

/// Store defaults remain symbolic until the solver can inspect the carrier.
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
    // The Int carrier ultimately preserves the base default, but that is an
    // array-theory axiom.  The elaborator must not apply the same rewrite to a
    // finite carrier, where Z3's default may be the stored value.
    assert!(
        !ctx.terms.is_true(ctx.assertions[0]),
        "default(store(...)) must survive elaboration for carrier-sensitive solving"
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

#[test]
fn indexed_array_map_resolves_exact_overload_and_preserves_identity() {
    let mut ctx = Context::new();
    ctx.register_native_function_alias(
        "surface".to_string(),
        "!private-int-domain".to_string(),
        vec![Sort::Int],
        Sort::Bool,
    )
    .unwrap();
    ctx.register_native_function_alias(
        "surface".to_string(),
        "!private-bool-domain".to_string(),
        vec![Sort::Bool],
        Sort::Int,
    )
    .unwrap();
    let commands = parse(
        "(declare-const a (Array Int Bool)) (declare-const i Int) \
         (assert (= (select ((_ map surface) a) i) 0))",
    )
    .unwrap();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }

    let TermData::App(Symbol::Named(eq), args) = ctx.terms.get(ctx.assertions[0]) else {
        panic!("assertion must remain equality");
    };
    assert_eq!(eq, "=");
    let TermData::App(Symbol::Named(selected), _) = ctx.terms.get(args[0]) else {
        panic!("select(map(alias), i) must rewrite to the selected function");
    };
    assert_eq!(selected, "!private-bool-domain");
}

#[test]
fn indexed_array_map_rejects_same_domain_result_ambiguity() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-fun f (Int) Bool) \
         (declare-const a (Array Int Int)) (assert (= ((_ map f) a) a))",
    )
    .unwrap();
    let mut ctx = Context::new();
    assert!(
        commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .is_err(),
        "array map must not choose between overloads with the same domain"
    );
}

#[test]
fn defined_function_array_map_expands_pointwise() {
    let commands = parse(
        "(define-fun f ((x Int)) Int (+ x 1)) \
         (declare-const a (Array Int Int)) \
         (declare-const i Int) \
         (assert (= (select ((_ map f) a) i) (+ (select a i) 1)))",
    )
    .unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

#[test]
fn defined_function_as_array_expands_to_lambda() {
    let commands = parse(
        "(define-fun f ((x Int)) Int (+ x 1)) \
         (declare-const i Int) \
         (assert (= (select (_ as-array f) i) (+ i 1)))",
    )
    .unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

#[test]
fn defined_function_array_expansion_is_capture_avoiding() {
    let commands = parse(
        "(declare-const global Int) \
         (define-fun f ((x Int)) Int (+ x global)) \
         (declare-const i Int) \
         (assert (let ((global 99)) (= (select (_ as-array f) i) (f i))))",
    )
    .unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }
    assert!(ctx.terms.is_true(ctx.assertions[0]));
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
