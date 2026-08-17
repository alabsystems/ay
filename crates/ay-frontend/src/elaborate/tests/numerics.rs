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

#[test]
fn z3_500_tilde_is_exactly_unary_minus() {
    let commands = parse(
        "(assert (= (~ 3) (- 3)))\
         (assert (= (~ 3.5) (- 3.5)))\
         (assert (= (~ true) (- 1)))",
    )
    .unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 3);
    assert!(ctx
        .assertions
        .iter()
        .all(|&assertion| ctx.terms.is_true(assertion)));

    for invalid in [
        "(assert (~))",
        "(assert (= (~ 1 2) 0))",
        "(assert (= (~ \"x\") 0))",
        "(set-option :int-real-coercions false)(assert (= (~ true) (- 1)))",
    ] {
        let commands = parse(invalid).unwrap();
        let mut ctx = Context::new();
        assert!(commands
            .iter()
            .any(|command| ctx.process_command(command).is_err()));
    }
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
fn test_elaborate_to_int_accepts_int_identity() {
    let input = r#"
            (declare-const x Int)
            (assert (= x (to_int x)))
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
fn test_elaborate_is_int_accepts_int_with_default_coercions() {
    let input = r#"
            (declare-const x Int)
            (assert (is_int x))
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

include!("numerics/real_power_edge_cases.rs");

// ---------------------------------------------------------------------------
// Z3 registry and SMT-LIB theory `:left-assoc` arithmetic arities
// ---------------------------------------------------------------------------

/// Elaborate every assertion of `input` in ONE context and return the
/// assertion `TermId`s, so structural identity can be compared by interning.
fn elaborate_assertions(input: &str) -> (Context, Vec<TermId>) {
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    let assertions = ctx.assertions.clone();
    (ctx, assertions)
}

/// True when elaborating `input` reports an error on some command.
fn elaboration_rejects(input: &str) -> bool {
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    commands.iter().any(|cmd| ctx.process_command(cmd).is_err())
}

include!("numerics/coercions_and_integer_power.rs");
