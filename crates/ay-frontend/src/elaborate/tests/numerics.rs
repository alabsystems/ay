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

/// A surviving symbolic or non-integral `^` must fail closed. Encoding it as
/// an uninterpreted function is unsound when constraints determine the
/// exponent later (for example, `y = 2`).
#[test]
fn test_elaborate_power_unsupported_exponents_are_rejected() {
    for input in [
        r#"
            (set-logic QF_NRA)
            (declare-const x Real)
            (declare-const y Real)
            (assert (= 1.0 (^ x y)))
        "#,
        r#"
            (set-logic QF_NRA)
            (declare-const x Real)
            (assert (= 1.0 (^ x 0.5)))
        "#,
    ] {
        let commands = parse(input).unwrap();
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .find_map(|command| ctx.process_command(command).err())
            .expect("unsupported exponent must be rejected");
        assert!(
            matches!(&error, ElaborateError::Unsupported(message) if message.contains('^')),
            "unexpected rejection for {input}: {error}"
        );
    }
}

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

/// Z3 5.0.0's null registry and the HORN/ALL extension registries coerce each
/// arithmetic Bool operand to `(ite b 1 0)`. This is an arithmetic application
/// rule: homogeneous Bool equality itself must remain Bool-sorted.
#[test]
fn z3_500_null_horn_all_bool_to_numeric_arithmetic_coercions() {
    let assertions = r"
        (assert (= (+ true false) 1))
        (assert (= (- true false) 1))
        (assert (= (- true) (- 1)))
        (assert (= (~ true) (- 1)))
        (assert (= (* true false) 0))
        (assert (= (/ true true) 1.0))
        (assert (= (div true true) 1))
        (assert (= (mod true true) 0))
        (assert (= (rem true true) 0))
        (assert (= (abs true) 1))
        (assert (< false true))
        (assert (<= false true))
        (assert (> true false))
        (assert (>= true false))
        (assert (= (to_real true) 1.0))
        (assert (= (to_int true) 1))
        (assert (is_int true))
    ";

    for logic_prefix in ["", "(set-logic HORN)\n", "(set-logic ALL)\n"] {
        let input = format!("{logic_prefix}{assertions}");
        let (ctx, elaborated) = elaborate_assertions(&input);
        assert_eq!(elaborated.len(), 17, "{input}");
        assert!(
            elaborated
                .iter()
                .all(|&assertion| ctx.terms.is_true(assertion)),
            "Bool arithmetic must have its Z3 numeric meaning: {input}"
        );
    }
}

/// The coercion option controls Bool-to-Int just as it controls Int-to-Real.
/// A homogeneous Bool list must not slip through the equality-oriented
/// exemption in `maybe_promote_numeric_args` when the surrounding app is
/// arithmetic.
#[test]
fn z3_500_disabling_int_real_coercions_rejects_bool_arithmetic() {
    for logic_prefix in ["", "(set-logic HORN)\n", "(set-logic ALL)\n"] {
        for assertion in [
            "(assert (= (+ true false) 1))",
            "(assert (= (- true false) 1))",
            "(assert (= (~ true) (- 1)))",
            "(assert (= (* true false) 0))",
            "(assert (= (/ true true) 1.0))",
            "(assert (= (div true true) 1))",
            "(assert (= (mod true true) 0))",
            "(assert (= (rem true true) 0))",
            "(assert (= (abs true) 1))",
            "(assert (< false true))",
            "(assert (<= false true))",
            "(assert (> true false))",
            "(assert (>= true false))",
            "(assert (= (to_real true) 1.0))",
            "(assert (= (to_int true) 1))",
            "(assert (is_int true))",
        ] {
            let input =
                format!("(set-option :int-real-coercions false)\n{logic_prefix}{assertion}");
            assert!(
                elaboration_rejects(&input),
                "disabled Bool arithmetic coercion must reject: {input}"
            );
        }
    }
}

/// The `/` declaration has a Real domain. Its explicit Int-to-Real lowering
/// must obey the same option; a homogeneous Int list is not enough to make the
/// application well-sorted when coercions are disabled.
#[test]
fn z3_500_disabling_int_real_coercions_rejects_int_real_division_promotion() {
    for logic_prefix in ["", "(set-logic HORN)\n", "(set-logic ALL)\n"] {
        let input = format!(
            "(set-option :int-real-coercions false)\n{logic_prefix}\
             (assert (= (/ 4 2) 2.0))"
        );
        assert!(
            elaboration_rejects(&input),
            "disabled Int-to-Real division promotion must reject: {input}"
        );
    }
}

/// Z3 recognizes identity applications of `to_real` at Real and `to_int` at
/// Int even when implicit coercions are disabled. `is_int` is different: its
/// declared domain remains Real when the option is false.
#[test]
fn z3_500_cast_identities_are_independent_of_implicit_coercions() {
    let (ctx, assertions) = elaborate_assertions(
        r"
        (set-option :int-real-coercions false)
        (assert (= (to_real 3.0) 3.0))
        (assert (= (to_int 3) 3))
    ",
    );
    assert_eq!(assertions.len(), 2);
    assert!(assertions
        .iter()
        .all(|&assertion| ctx.terms.is_true(assertion)));
    assert!(elaboration_rejects(
        "(set-option :int-real-coercions false)\n(assert (is_int 3))"
    ));
}

/// Bool arithmetic first requires the Int declaration family. A standard
/// Int logic admits that coercion; a Real-only logic does not. HORN and ALL
/// are extension registries and are covered by the positive matrix above.
#[test]
fn standard_logic_bool_numeric_coercion_keeps_theory_boundaries() {
    let (ctx, assertions) = elaborate_assertions(
        "(set-logic QF_LIA)\n(assert (= (+ true false) 1))\n(assert (< false true))",
    );
    assert!(assertions
        .iter()
        .all(|&assertion| ctx.terms.is_true(assertion)));
    assert!(elaboration_rejects(
        "(set-logic QF_LRA)\n(assert (= (+ true false) 1.0))"
    ));
}

/// `divisible` is the one arithmetic-plugin boundary where Z3 5.0.0 does not
/// apply Bool-to-Int. Keep its declared Int domain even though its internal
/// desugaring uses the now-coercing `mod` application.
#[test]
fn z3_500_divisible_does_not_coerce_bool() {
    assert!(elaboration_rejects(
        "(set-option :smtlib2_compliant true)\n(assert ((_ divisible 1) true))"
    ));
    let (ctx, assertions) =
        elaborate_assertions("(set-option :smtlib2_compliant true)\n(assert ((_ divisible 1) 2))");
    assert_eq!(assertions.len(), 1);
    assert!(ctx.terms.is_true(assertions[0]));
}

/// Z3 5.0.0 never gives the associative arithmetic declarations a nullary
/// identity. This applies to the null registry and its HORN/ALL extensions.
#[test]
fn z3_500_zero_argument_arithmetic_apps_are_rejected() {
    for logic_prefix in ["", "(set-logic HORN)\n", "(set-logic ALL)\n"] {
        for assertion in [
            "(assert (= (+) 0))",
            "(assert (= (-) 0))",
            "(assert (= (*) 1))",
        ] {
            let input = format!("{logic_prefix}{assertion}");
            assert!(
                elaboration_rejects(&input),
                "zero-argument arithmetic must be rejected: {input}"
            );
        }
    }
}

/// The Z3 5.0.0 null-logic declaration registry treats a unary application of
/// its binary left-associative `/` and `div` declarations as the typed identity.
/// The Z3 extension logics HORN and ALL retain the same registry behavior.
#[test]
fn z3_500_null_horn_and_all_unary_division_are_typed_identities() {
    for logic_prefix in ["", "(set-logic HORN)\n", "(set-logic ALL)\n"] {
        let input = format!("{logic_prefix}(assert (= (/ 5.0) 5.0))\n(assert (= (div 5) 5))");
        let (ctx, assertions) = elaborate_assertions(&input);
        assert_eq!(assertions.len(), 2, "{input}");
        assert!(
            assertions
                .iter()
                .all(|&assertion| ctx.terms.is_true(assertion)),
            "unary division must elaborate to its operand: {input}"
        );
    }
}

/// Unary registry identities remain typed: `/` takes Real and `div` takes Int.
#[test]
fn z3_500_null_logic_unary_division_rejects_wrong_sorts() {
    for input in [
        "(assert (= (/ 5) 5.0))",
        "(assert (= (/ true) 1.0))",
        "(assert (= (div 5.0) 5))",
        "(assert (= (div true) 1))",
    ] {
        assert!(
            elaboration_rejects(input),
            "ill-sorted unary division must be rejected: {input}"
        );
    }
}

/// SMT-LIB 2.6 theory `Reals` declares `(/ Real Real Real :left-assoc)`, so
/// `(/ a b c)` abbreviates `(/ (/ a b) c)`. Compared by interned `TermId`, not
/// by a solver verdict.
#[test]
fn division_is_left_associative() {
    let (_ctx, assertions) = elaborate_assertions(
        r"
        (set-logic QF_LRA)
        (declare-const a Real)
        (declare-const b Real)
        (declare-const c Real)
        (assert (= (/ a b c) 0.0))
        (assert (= (/ (/ a b) c) 0.0))
        (assert (= (/ a b c a) 0.0))
        (assert (= (/ (/ (/ a b) c) a) 0.0))
    ",
    );
    assert_eq!(assertions.len(), 4);
    assert_eq!(
        assertions[0], assertions[1],
        "(/ a b c) must intern to the same term as (/ (/ a b) c)"
    );
    assert_eq!(
        assertions[2], assertions[3],
        "(/ a b c a) must intern to the same term as (/ (/ (/ a b) c) a)"
    );
}

/// SMT-LIB 2.6 theory `Ints` declares `(div Int Int Int :left-assoc)`.
#[test]
fn intdiv_is_left_associative() {
    let (_ctx, assertions) = elaborate_assertions(
        r"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= (div a b c) 0))
        (assert (= (div (div a b) c) 0))
    ",
    );
    assert_eq!(assertions.len(), 2);
    assert_eq!(
        assertions[0], assertions[1],
        "(div a b c) must intern to the same term as (div (div a b) c)"
    );
}

/// `mod`, `rem` and `abs` are NOT `:left-assoc` in SMT-LIB 2.6 `Ints`; they are
/// fixed arity and an over-application is a well-sortedness error. Pinning this
/// keeps the `:left-assoc` fix from spreading to operators the standard makes
/// binary.
#[test]
fn mod_rem_abs_stay_fixed_arity() {
    for input in [
        "(set-logic QF_LIA)\n(assert (= (mod 100 7 3) 2))",
        "(set-logic QF_LIA)\n(assert (= (rem 100 7 3) 2))",
        "(set-logic QF_LIA)\n(assert (= (abs 1 2) 1))",
    ] {
        assert!(
            elaboration_rejects(input),
            "over-applied fixed-arity operator must be rejected: {input}"
        );
    }
}

/// A one-argument `/` or `div` remains ill-sorted after selecting a standard
/// SMT-LIB logic: theory-level `:left-assoc` means two-or-more, not one-or-more.
#[test]
fn standard_logic_division_still_requires_two_arguments() {
    for input in [
        "(set-logic QF_LRA)\n(declare-const a Real)\n(assert (= (/ a) 0.0))",
        "(set-logic QF_LIA)\n(declare-const a Int)\n(assert (= (div a) 0))",
    ] {
        assert!(
            elaboration_rejects(input),
            "unary division must be rejected: {input}"
        );
    }
}

/// The folded value of a fully-constant n-ary `/` and `div` follows the
/// left-associative reading: `(/ 8.0 2.0 2.0) = 2.0` and `(div 100 5 2) = 10`.
#[test]
fn nary_division_folds_left_associatively() {
    let (ctx, assertions) = elaborate_assertions(
        r"
        (set-logic QF_LIRA)
        (assert (= (/ 8.0 2.0 2.0) 2.0))
        (assert (= (div 100 5 2) 10))
    ",
    );
    assert_eq!(assertions.len(), 2);
    for a in assertions {
        assert!(
            matches!(
                ctx.terms.get(a),
                TermData::Const(ay_core::Constant::Bool(true))
            ),
            "constant-folded n-ary division must be true, got {:?}",
            ctx.terms.get(a)
        );
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

// ---------------------------------------------------------------------------
// SMT-LIB 2.7 `**` (integer exponentiation) / QF_EIA
// ---------------------------------------------------------------------------

#[test]
fn integer_power_ground_rules_fold_exactly() {
    let (ctx, assertions) = elaborate_assertions(
        r"
        (set-logic QF_EIA)
        (assert (= (** 2 10) 1024))
        (assert (= (** (- 2) 3) (- 8)))
        (assert (= (** 0 0) 1))
        (assert (= (** 1 (- 7)) 1))
        (assert (= (** (- 1) (- 3)) (- 1)))
        (assert (= (** (- 1) (- 4)) 1))
        (assert (= (** 2 (- 3)) 0))
        (assert (= (** (- 2) (- 3)) 0))
    ",
    );
    assert_eq!(assertions.len(), 8);
    assert!(
        assertions.iter().all(|&term| ctx.terms.is_true(term)),
        "every standard ground-power fact must fold to true"
    );
}

#[test]
fn integer_power_wrong_fact_twins_fold_false() {
    let (ctx, assertions) = elaborate_assertions(
        r"
        (set-logic QF_EIA)
        (assert (= (** 2 10) 1023))
        (assert (= (** 0 0) 0))
        (assert (= (** (- 1) (- 3)) 1))
        (assert (= (** 2 (- 3)) 1))
    ",
    );
    assert_eq!(assertions.len(), 4);
    assert!(
        assertions.iter().all(|&term| ctx.terms.is_false(term)),
        "each deliberately wrong power fact must fold to false"
    );
}

#[test]
fn integer_power_zero_to_negative_exponent_remains_underspecified() {
    let (ctx, assertions) = elaborate_assertions(
        r"
        (set-logic QF_EIA)
        (assert (= (** 0 (- 4)) 0))
        (assert (= (** 0 (- 4)) 1))
    ",
    );
    assert_eq!(assertions.len(), 2);
    assert!(assertions
        .iter()
        .all(|&term| { !ctx.terms.is_true(term) && !ctx.terms.is_false(term) }));
}

#[test]
fn integer_power_literal_exponent_eliminates_builtin() {
    let (ctx, assertions) = elaborate_assertions(
        r"
        (set-logic QF_EIA)
        (declare-const x Int)
        (assert (= (** x 3) (* x x x)))
    ",
    );
    assert_eq!(assertions.len(), 1);
    assert!(
        ctx.terms.is_true(assertions[0]),
        "literal-exponent ** must lower to an equivalent integer product"
    );
}

#[test]
fn integer_power_symbolic_exponent_is_preserved_as_typed_builtin() {
    let (ctx, assertions) = elaborate_assertions(
        r"
        (set-logic QF_EIA)
        (declare-const exponent Int)
        (assert (= (** 2 exponent) 4))
    ",
    );
    assert_eq!(assertions.len(), 1);
    let has_power = ctx.terms.term_ids().any(|id| {
        matches!(ctx.terms.get(id), TermData::App(symbol, args) if symbol.name() == "**" && args.len() == 2)
    });
    assert!(
        has_power,
        "symbolic ** must survive for the executor's unknown gate"
    );
}

#[test]
fn integer_power_requires_two_integer_arguments() {
    for input in [
        "(set-logic QF_EIA) (assert (= (** 2) 2))",
        "(set-logic QF_EIA) (assert (= (** 2 3 4) 8))",
        "(set-logic QF_EIA) (assert (= (** 2.0 3) 8))",
        "(set-logic QF_EIA) (assert (= (** 2 3.0) 8))",
        "(set-logic QF_EIA) (assert (= (** true 3) 1))",
    ] {
        assert!(
            elaboration_rejects(input),
            "ill-typed or wrong-arity integer power must be rejected: {input}"
        );
    }
}
