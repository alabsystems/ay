// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elaborate_negative_integer_literals() {
    let input = r#"
            (declare-const x Int)
            (assert (= x -1))
            (assert (>= x -42))
            (assert (<= (+ x -5) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 3);
}

#[test]
fn test_elaborate_negative_in_multiplication() {
    let input = r#"
            (declare-const v0 Int)
            (declare-const v1 Int)
            (assert (= (+ (* 1 v0) (* 2 v1)) 38))
            (assert (>= (+ (* 2 v0) (* -1 v1)) -46))
            (assert (<= (+ (* -1 v0) (* -1 v1)) 39))
            (assert (<= (+ (* -4 v0) (* 5 v1)) -21))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 4);
}

#[test]
fn test_elaborate_negative_decimal_literals() {
    let input = r#"
            (declare-const x Real)
            (assert (= x -3.14))
            (assert (>= x -0.5))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn test_elaborate_negative_zero() {
    let input = r#"
            (assert (= -0 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

/// Regression test: mk_div panics with integer literals in QF_LRA
/// SMT-LIB integer literals in real division must be coerced to Real.
/// Reproducer for ay#2179.
#[test]
fn test_real_div_promotes_int_literals() {
    // This panicked before the fix: "BUG: mk_div expects Real args"
    let input = r#"
            (set-logic QF_LRA)
            (declare-const z Real)
            (assert (= z (/ 7 2)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    // Verify the division args are Real, not Int
    let assertion = ctx.assertions[0];
    if let TermData::App(Symbol::Named(name), args) = ctx.terms.get(assertion) {
        assert_eq!(name, "=");
        let div_term = args[1];
        if let TermData::App(Symbol::Named(div_name), div_args) = ctx.terms.get(div_term) {
            assert_eq!(div_name, "/");
            for &arg in div_args {
                assert_eq!(
                    *ctx.terms.sort(arg),
                    Sort::Real,
                    "Division arg should be Real, not Int"
                );
            }
        }
    }
}

/// Regression test: `distinct` with mixed Int/Real args must coerce
/// Int to Real, matching the behavior of `=`.
/// Without the fix, this hits a debug_assert in mk_eq (called by
/// mk_distinct) because Int and Real sorts mismatch.
#[test]
fn test_distinct_promotes_int_to_real() {
    let input = r#"
            (set-logic QF_LRA)
            (declare-const x Real)
            (declare-const y Real)
            (assert (distinct x 0 y 1))
            (check-sat)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_to_int() {
    let input = r#"
            (set-logic QF_LIRA)
            (declare-const x Real)
            (declare-const y Int)
            (assert (= y (to_int x)))
            (check-sat)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    if let TermData::App(Symbol::Named(name), args) = ctx.terms.get(assertion) {
        assert_eq!(name, "=");
        let to_int_term = args[1];
        assert_eq!(*ctx.terms.sort(to_int_term), Sort::Int);
    }
}

#[test]
fn test_elaborate_to_int_constant_fold() {
    // to_int of a constant rational should fold to floor
    let input = r#"
            (set-logic QF_LIRA)
            (declare-const y Int)
            (assert (= y (to_int 3.7)))
            (check-sat)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_is_int() {
    let input = r#"
            (set-logic QF_LIRA)
            (declare-const x Real)
            (assert (is_int x))
            (check-sat)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    assert_eq!(*ctx.terms.sort(assertion), Sort::Bool);
}

#[test]
fn test_elaborate_to_int_sort_mismatch() {
    let input = r#"
            (declare-const x Int)
            (assert (= x (to_int x)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut err = None;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            err = Some(e);
            break;
        }
    }
    assert!(err.is_some(), "to_int on Int arg should fail");
}

#[test]
fn test_elaborate_is_int_sort_mismatch() {
    let input = r#"
            (declare-const x Int)
            (assert (is_int x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut err = None;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            err = Some(e);
            break;
        }
    }
    assert!(err.is_some(), "is_int on Int arg should fail");
}

#[test]
fn test_elaborate_fp_to_real() {
    let input = r#"
            (set-logic QF_FPLRA)
            (declare-const x (_ FloatingPoint 8 24))
            (declare-const r Real)
            (assert (= r (fp.to_real x)))
            (check-sat)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    if let TermData::App(Symbol::Named(name), args) = ctx.terms.get(assertion) {
        assert_eq!(name, "=");
        let fp_to_real_term = args[1];
        assert_eq!(*ctx.terms.sort(fp_to_real_term), Sort::Real);
    }
}

#[test]
fn test_elaborate_fp_to_real_sort_mismatch() {
    let input = r#"
            (declare-const x Int)
            (assert (= 0 (fp.to_real x)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut err = None;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            err = Some(e);
            break;
        }
    }
    assert!(err.is_some(), "fp.to_real on Int arg should fail");
}

/// W19-5: define-fun with Real return sort and Int numeral body must coerce.
///
/// `(define-fun _7 () Real 0)` must produce a Real-sorted term, not Int.
/// Without coercion, downstream mk_eq on `_7 = <real_var>` panics in debug
/// and silently corrupts theory reasoning in release (#6812).
#[test]
fn test_define_fun_real_sort_coerces_int_numeral() {
    let input = r#"
        (set-logic QF_UFLRA)
        (define-fun _7 () Real 0)
        (define-fun _14 () Real 1)
        (declare-fun x () Real)
        (assert (= x _7))
        (assert (>= x _14))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // The key check: _7 must elaborate as Real, not Int.
    // If it's Int, the (= x _7) assertion would fail mk_eq's sort check.
    // Two assertions means both (= x _7) and (>= x _14) parsed without
    // a sort mismatch panic.
    assert_eq!(
        ctx.assertions.len(),
        2,
        "both assertions must elaborate cleanly"
    );
}

// ---------------------------------------------------------------------------
// `^` (power) operator over Int/Real (#8731)
// ---------------------------------------------------------------------------

/// `(^ base 0)` must elaborate to the multiplicative identity in the base's
/// sort. For an Int base the result is the Int literal `1`; for a Real base
/// the result is the Real literal `1.0`.
#[test]
fn test_elaborate_power_zero_exponent_real_base() {
    let input = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (^ x 0) 1.0))
    "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // `(^ x 0) = 1.0` folds to `(= 1.0 1.0)` which further folds to `true`,
    // so the assertion is trivially true.
    assert_eq!(ctx.assertions.len(), 1);
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "(^ x 0) = 1.0 must constant-fold to true"
    );
}

/// `(^ base 1)` returns the base unchanged.
#[test]
fn test_elaborate_power_one_exponent() {
    let input = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (^ x 1) x))
    "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "(^ x 1) = x must fold to true"
    );
}

/// `(^ 2.0 3)` must constant-fold to `8.0` via repeated multiplication.
#[test]
fn test_elaborate_power_literal_real_base_positive_exp() {
    let input = r#"
        (set-logic QF_NRA)
        (assert (= (^ 2.0 3) 8.0))
    "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    assert!(
        ctx.terms.is_true(ctx.assertions[0]),
        "(= (^ 2.0 3) 8.0) must fold to true"
    );
}

/// `(^ 3.0 (- 2))` must elaborate such that for a non-zero base the result
/// is `(/ 1.0 9.0)`. Because the base is a non-zero literal, the ITE guard
/// folds to the reciprocal branch.
#[test]
fn test_elaborate_power_negative_exp_literal_base() {
    let input = r#"
        (set-logic QF_NRA)
        (declare-const y Real)
        (assert (= y (^ 3.0 (- 2))))
    "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // y must be Real-sorted to match the reciprocal.
    let assertion = ctx.assertions[0];
    if let TermData::App(Symbol::Named(name), args) = ctx.terms.get(assertion) {
        assert_eq!(name, "=");
        assert_eq!(*ctx.terms.sort(args[1]), Sort::Real);
    } else {
        panic!("expected top-level equality");
    }
}

/// `(^ x 2)` with a non-literal base must unfold to a product in the base's
/// sort (Real here). After unfolding, neither side of the resulting
/// comparison should contain a raw `^` application — it must have been
/// rewritten into `*`.
#[test]
fn test_elaborate_power_variable_base_small_exp() {
    let input = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (>= (^ x 2) 0.0))
    "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    // The top-level assertion is a (possibly normalized) comparison. Walk
    // it to ensure no sub-term is a raw `^` application.
    fn contains_pow(terms: &TermStore, t: TermId) -> bool {
        match terms.get(t) {
            TermData::App(Symbol::Named(name), args) if name == "^" => true,
            TermData::App(_, args) => args.iter().any(|&a| contains_pow(terms, a)),
            TermData::Ite(c, th, el) => {
                contains_pow(terms, *c) || contains_pow(terms, *th) || contains_pow(terms, *el)
            }
            TermData::Not(inner) => contains_pow(terms, *inner),
            TermData::Let(bindings, body) => {
                bindings.iter().any(|(_, v)| contains_pow(terms, *v)) || contains_pow(terms, *body)
            }
            _ => false,
        }
    }
    assert!(
        !contains_pow(&ctx.terms, ctx.assertions[0]),
        "literal-integer exponent must be unfolded to *, not left as ^"
    );
}

/// `(^ x y)` with a symbolic exponent must be kept as an uninterpreted
/// `^` application in the base's sort, per SMT-LIB partial semantics.
#[test]
fn test_elaborate_power_symbolic_exp_stays_uninterpreted() {
    let input = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= 1.0 (^ x y)))
    "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    if let TermData::App(Symbol::Named(name), args) = ctx.terms.get(assertion) {
        assert_eq!(name, "=");
        // Check that one side is a `^` application kept as-is.
        let rhs_is_pow = args
            .iter()
            .any(|&a| matches!(ctx.terms.get(a), TermData::App(Symbol::Named(n), _) if n == "^"));
        assert!(rhs_is_pow, "symbolic-exponent ^ must be preserved");
    }
}

/// `(^ 2 5)` over Int base produces `32` via constant folding.
#[test]
fn test_elaborate_power_int_base_literal_fold() {
    let input = r#"
        (set-logic QF_NIA)
        (declare-const y Int)
        (assert (= y (^ 2 5)))
    "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    if let TermData::App(Symbol::Named(name), args) = ctx.terms.get(assertion) {
        assert_eq!(name, "=");
        // The literal rhs must have folded to 32.
        if let TermData::Const(ay_core::Constant::Int(n)) = ctx.terms.get(args[1]) {
            assert_eq!(*n, num_bigint::BigInt::from(32));
        } else {
            panic!("expected Int constant 32, got {:?}", ctx.terms.get(args[1]));
        }
    }
}
