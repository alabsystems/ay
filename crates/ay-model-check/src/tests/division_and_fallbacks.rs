// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn sat_euclidean_mod_and_div() {
    // SMT-LIB: (-7) = 3*(-3) + 2, so (mod -7 3) = 2 and (div -7 3) = -3.
    let mut ts = TermStore::new();
    let neg7 = ts.mk_int(int(-7));
    let three = ts.mk_int(int(3));
    let two = ts.mk_int(int(2));
    let neg3 = ts.mk_int(int(-3));
    let m = app(&mut ts, "mod", &[neg7, three], Sort::Int);
    let d = app(&mut ts, "div", &[neg7, three], Sort::Int);
    let em = app(&mut ts, "=", &[m, two], Sort::Bool);
    let ed = app(&mut ts, "=", &[d, neg3], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[em, ed]));
}

#[test]
fn zero_divisors_use_the_exact_typed_fallbacks() {
    let mut ts = TermStore::new();
    let real_one = ts.mk_rational(BigRational::from_integer(int(1)));
    let real_zero = ts.mk_rational(BigRational::from_integer(int(0)));
    let int_one = ts.mk_int(int(1));
    let int_zero = ts.mk_int(int(0));
    let real_div = app(&mut ts, "/", &[real_one, real_zero], Sort::Real);
    let int_div = app(&mut ts, "div", &[int_one, int_zero], Sort::Int);
    let int_mod = app(&mut ts, "mod", &[int_one, int_zero], Sort::Int);
    let real_choice = BigRational::new(int(7), int(2));
    let real_expected = ts.mk_rational(real_choice.clone());
    let int_div_expected = ts.mk_int(int(-4));
    let int_mod_expected = ts.mk_int(int(9));
    let real_eq = app(&mut ts, "=", &[real_div, real_expected], Sort::Bool);
    let div_eq = app(&mut ts, "=", &[int_div, int_div_expected], Sort::Bool);
    let mod_eq = app(&mut ts, "=", &[int_mod, int_mod_expected], Sort::Bool);
    let model = UfStubModel::new()
        .unconstrained(
            real_div,
            ProvenUnconstrainedKind::RealDivByZero,
            ModelValue::Real(real_choice),
        )
        .unconstrained(
            int_div,
            ProvenUnconstrainedKind::IntDivByZero,
            ModelValue::Int(int(-4)),
        )
        .unconstrained(
            int_mod,
            ProvenUnconstrainedKind::IntModByZero,
            ModelValue::Int(int(9)),
        );

    assert_confirmed(&verdict(&ts, &model, &[real_eq, div_eq, mod_eq]));
    assert_eq!(model.unconstrained_calls.get(), 3);
}

#[test]
fn real_division_checks_the_zero_divisor_before_rationalizing_an_algebraic_numerator() {
    let mut ts = TermStore::new();
    let numerator = ts.mk_var("sqrt-two", Sort::Real);
    let zero = ts.mk_rational(BigRational::from_integer(int(0)));
    let division = app(&mut ts, "/", &[numerator, zero], Sort::Real);
    let selected = BigRational::new(int(5), int(3));
    let sqrt_two = algebraic::Algebraic::root_of(
        algebraic::integer_poly(&[-2, 0, 1]),
        BigRational::from_integer(int(1)),
        BigRational::from_integer(int(2)),
    )
    .expect("sqrt(2) is a valid algebraic value");
    let model = UfStubModel::new()
        .leaf(numerator, ModelValue::Algebraic(Box::new(sqrt_two)))
        .unconstrained(
            division,
            ProvenUnconstrainedKind::RealDivByZero,
            ModelValue::Real(selected.clone()),
        );

    assert!(matches!(
        evaluate_term(&ts, &model, division),
        EvalOutcome::Value(ModelValue::Real(value)) if value == selected
    ));
    assert_eq!(model.unconstrained_calls.get(), 1);
}

#[test]
fn committed_zero_division_value_precedes_typed_fallback() {
    let mut ts = TermStore::new();
    let one = ts.mk_int(int(1));
    let zero = ts.mk_int(int(0));
    let div = app(&mut ts, "div", &[one, zero], Sort::Int);
    let committed = ts.mk_int(int(3));
    let assertion = app(&mut ts, "=", &[div, committed], Sort::Bool);
    let model = UfStubModel::new()
        .uf(div, ModelValue::Int(int(3)))
        .unconstrained(
            div,
            ProvenUnconstrainedKind::IntDivByZero,
            ModelValue::Int(int(99)),
        );

    assert_confirmed(&verdict(&ts, &model, &[assertion]));
    assert_eq!(model.unconstrained_calls.get(), 0);
}

#[test]
fn nonzero_real_div_div_and_mod_never_consult_unconstrained_fallback() {
    let mut ts = TermStore::new();
    let real_four = ts.mk_rational(BigRational::from_integer(int(4)));
    let real_two = ts.mk_rational(BigRational::from_integer(int(2)));
    let int_seven = ts.mk_int(int(7));
    let int_three = ts.mk_int(int(3));
    let real_div = app(&mut ts, "/", &[real_four, real_two], Sort::Real);
    let int_div = app(&mut ts, "div", &[int_seven, int_three], Sort::Int);
    let int_mod = app(&mut ts, "mod", &[int_seven, int_three], Sort::Int);
    let real_expected = ts.mk_rational(BigRational::from_integer(int(2)));
    let int_div_expected = ts.mk_int(int(2));
    let int_mod_expected = ts.mk_int(int(1));
    let real_assertion = app(&mut ts, "=", &[real_div, real_expected], Sort::Bool);
    let div_assertion = app(&mut ts, "=", &[int_div, int_div_expected], Sort::Bool);
    let mod_assertion = app(&mut ts, "=", &[int_mod, int_mod_expected], Sort::Bool);
    let model = UfStubModel::new()
        .unconstrained(
            real_div,
            ProvenUnconstrainedKind::RealDivByZero,
            ModelValue::Real(BigRational::from_integer(int(99))),
        )
        .unconstrained(
            int_div,
            ProvenUnconstrainedKind::IntDivByZero,
            ModelValue::Int(int(99)),
        )
        .unconstrained(
            int_mod,
            ProvenUnconstrainedKind::IntModByZero,
            ModelValue::Int(int(99)),
        );

    assert_confirmed(&verdict(
        &ts,
        &model,
        &[real_assertion, div_assertion, mod_assertion],
    ));
    assert_eq!(model.unconstrained_calls.get(), 0);
}

#[test]
fn malformed_division_signatures_never_mint_typed_authority() {
    let mut ts = TermStore::new();
    let real_zero = ts.mk_rational(BigRational::from_integer(int(0)));
    let int_zero = ts.mk_int(int(0));
    let int_one = ts.mk_int(int(1));

    let unary_real_div = app(&mut ts, "/", &[real_zero], Sort::Real);
    let real_div_with_int_operands = app(&mut ts, "/", &[int_one, int_zero], Sort::Real);
    let int_div_with_real_operands = app(&mut ts, "div", &[real_zero, real_zero], Sort::Int);
    let mod_with_real_result = app(&mut ts, "mod", &[int_one, int_zero], Sort::Real);
    let model = UfStubModel::new()
        .unconstrained(
            unary_real_div,
            ProvenUnconstrainedKind::RealDivByZero,
            ModelValue::Real(BigRational::from_integer(int(7))),
        )
        .unconstrained(
            real_div_with_int_operands,
            ProvenUnconstrainedKind::RealDivByZero,
            ModelValue::Real(BigRational::from_integer(int(7))),
        )
        .unconstrained(
            int_div_with_real_operands,
            ProvenUnconstrainedKind::IntDivByZero,
            ModelValue::Int(int(7)),
        )
        .unconstrained(
            mod_with_real_result,
            ProvenUnconstrainedKind::IntModByZero,
            ModelValue::Int(int(7)),
        );

    for malformed in [
        unary_real_div,
        real_div_with_int_operands,
        int_div_with_real_operands,
        mod_with_real_result,
    ] {
        assert!(
            matches!(
                evaluate_term(&ts, &model, malformed),
                EvalOutcome::Unevaluable(_)
            ),
            "malformed arithmetic application must fail closed"
        );
    }
    assert_eq!(model.unconstrained_calls.get(), 0);
}

#[test]
fn zero_division_rejects_wrong_sort_before_congruence_insertion() {
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let zero = ts.mk_int(int(0));
    let div_a = app(&mut ts, "div", &[a, zero], Sort::Int);
    let div_b = app(&mut ts, "div", &[b, zero], Sort::Int);
    let model = UfStubModel::new()
        .leaf(a, ModelValue::Int(int(1)))
        .leaf(b, ModelValue::Int(int(1)))
        .unconstrained(
            div_a,
            ProvenUnconstrainedKind::IntDivByZero,
            ModelValue::Bool(true),
        )
        .unconstrained(
            div_b,
            ProvenUnconstrainedKind::IntDivByZero,
            ModelValue::Int(int(7)),
        );
    let evaluator = Evaluator::new(&ts, &model);

    match evaluator.evaluate(div_a) {
        EvalOutcome::Unevaluable(reason) => assert!(reason.contains("must still be a number")),
        other => panic!("wrong-sort div fallback must fail closed, got {other:?}"),
    }
    assert!(matches!(
        evaluator.evaluate(div_b),
        EvalOutcome::Value(ModelValue::Int(value)) if value == int(7)
    ));
}

#[test]
fn congruent_zero_divisions_share_one_fallback_value() {
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let zero = ts.mk_int(int(0));
    let div_a = app(&mut ts, "div", &[a, zero], Sort::Int);
    let div_b = app(&mut ts, "div", &[b, zero], Sort::Int);
    let seven = ts.mk_int(int(7));
    let eight = ts.mk_int(int(8));
    let first_definition = app(&mut ts, "=", &[div_a, seven], Sort::Bool);
    let conflicting_definition = app(&mut ts, "=", &[div_b, eight], Sort::Bool);
    let model = UfStubModel::new()
        .leaf(a, ModelValue::Int(int(1)))
        .leaf(b, ModelValue::Int(int(1)))
        .unconstrained(
            div_a,
            ProvenUnconstrainedKind::IntDivByZero,
            ModelValue::Int(int(7)),
        )
        .unconstrained(
            div_b,
            ProvenUnconstrainedKind::IntDivByZero,
            ModelValue::Int(int(8)),
        );

    // Evaluating the first definition installs div(1, 0) = 7 in the
    // value-keyed graph.  The congruent second application must reuse that
    // value instead of consulting its incompatible per-term fallback, making
    // the second asserted definition false.
    assert_violates(&verdict(
        &ts,
        &model,
        &[first_definition, conflicting_definition],
    ));
    assert_eq!(model.unconstrained_calls.get(), 1);
}

#[test]
fn equal_cross_extension_zero_division_keys_fail_closed() {
    // Exact UNSAT shape: the polynomial and positivity assertions force both
    // x and y to the one real value +sqrt(2).  Division by zero is total but
    // unconstrained, so it may choose any value at sqrt(2), not TWO values at
    // the same argument.  The two exact root objects deliberately use
    // different isolating intervals. `value_eq` cannot compare those
    // extensions, which must stop the gate rather than be mistaken for proof
    // that x and y differ.
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Real);
    let y = ts.mk_var("y", Sort::Real);
    let zero = ts.mk_rational(BigRational::from_integer(int(0)));
    let two = ts.mk_rational(BigRational::from_integer(int(2)));
    let seven = ts.mk_rational(BigRational::from_integer(int(7)));
    let eight = ts.mk_rational(BigRational::from_integer(int(8)));
    let x_squared = app(&mut ts, "*", &[x, x], Sort::Real);
    let y_squared = app(&mut ts, "*", &[y, y], Sort::Real);
    let x_is_root = app(&mut ts, "=", &[x_squared, two], Sort::Bool);
    let y_is_root = app(&mut ts, "=", &[y_squared, two], Sort::Bool);
    let x_positive = app(&mut ts, ">", &[x, zero], Sort::Bool);
    let y_positive = app(&mut ts, ">", &[y, zero], Sort::Bool);
    let div_x = app(&mut ts, "/", &[x, zero], Sort::Real);
    let div_y = app(&mut ts, "/", &[y, zero], Sort::Real);
    let first_definition = app(&mut ts, "=", &[div_x, seven], Sort::Bool);
    let conflicting_definition = app(&mut ts, "=", &[div_y, eight], Sort::Bool);

    let model = UfStubModel::new()
        .leaf(
            x,
            sqrt_two_between(
                BigRational::from_integer(int(1)),
                BigRational::from_integer(int(2)),
            ),
        )
        .leaf(
            y,
            sqrt_two_between(
                BigRational::new(int(4), int(3)),
                BigRational::new(int(3), int(2)),
            ),
        )
        .unconstrained(
            div_x,
            ProvenUnconstrainedKind::RealDivByZero,
            ModelValue::Real(BigRational::from_integer(int(7))),
        )
        .unconstrained(
            div_y,
            ProvenUnconstrainedKind::RealDivByZero,
            ModelValue::Real(BigRational::from_integer(int(8))),
        );

    match verdict(
        &ts,
        &model,
        &[
            x_is_root,
            y_is_root,
            x_positive,
            y_positive,
            first_definition,
            conflicting_definition,
        ],
    ) {
        GateVerdict::CannotConfirm { reason } => {
            assert!(reason.contains("cannot decide congruence-key equality"));
            assert!(reason.contains("algebraic equality across different extensions"));
        }
        other => panic!("equal algebraic /0 keys must fail closed, got {other:?}"),
    }
    assert_eq!(
        model.unconstrained_calls.get(),
        1,
        "the ambiguous second key must fail before adopting another value"
    );
}

#[test]
fn generic_application_never_consults_unconstrained_fallback() {
    let mut ts = TermStore::new();
    let one = ts.mk_int(int(1));
    let application = app(&mut ts, "f", &[one], Sort::Int);
    let model = UfStubModel::new().unconstrained(
        application,
        ProvenUnconstrainedKind::IntDivByZero,
        ModelValue::Int(int(7)),
    );

    match evaluate_term(&ts, &model, application) {
        EvalOutcome::Unevaluable(reason) => assert!(reason.contains("model commits no value")),
        other => panic!("generic application must not use typed fallback, got {other:?}"),
    }
    assert_eq!(model.unconstrained_calls.get(), 0);
}

#[test]
fn sat_bitvector_add() {
    let mut ts = TermStore::new();
    let a = ts.mk_bitvec(int(3), 4);
    let b = ts.mk_bitvec(int(1), 4);
    let four = ts.mk_bitvec(int(4), 4);
    let sum = app(&mut ts, "bvadd", &[a, b], Sort::bitvec(4));
    let eq = app(&mut ts, "=", &[sum, four], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn sat_bitvector_signed_div_and_extract() {
    // bvsdiv of -6 / 2 over 4 bits = -3 (= 1101). extract [1:0] of 1101 = 01.
    let mut ts = TermStore::new();
    let neg6 = ts.mk_bitvec(int(-6), 4); // 1010
    let two = ts.mk_bitvec(int(2), 4);
    let q = app(&mut ts, "bvsdiv", &[neg6, two], Sort::bitvec(4)); // 1101
    let expect = ts.mk_bitvec(int(-3), 4);
    let eq = app(&mut ts, "=", &[q, expect], Sort::Bool);
    let ext = ts.mk_app(Symbol::indexed("extract", vec![1, 0]), [q], Sort::bitvec(2));
    let one2 = ts.mk_bitvec(int(1), 2); // 01
    let eq2 = app(&mut ts, "=", &[ext, one2], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq, eq2]));
}
