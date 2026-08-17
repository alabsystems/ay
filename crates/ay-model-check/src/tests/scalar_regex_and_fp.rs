// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn sat_bool_leaf() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Bool);
    let m = StubModel::new().with(x, ModelValue::Bool(true));
    assert_confirmed(&verdict(&ts, &m, &[x]));
}

#[test]
fn sat_int_arithmetic() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let one = ts.mk_int(int(1));
    let four = ts.mk_int(int(4));
    let sum = app(&mut ts, "+", &[x, one], Sort::Int);
    let eq = app(&mut ts, "=", &[sum, four], Sort::Bool);
    let m = StubModel::new().with(x, ModelValue::Int(int(3)));
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn regex_membership_confirms_literal_between_allchar_stars() {
    let mut ts = TermStore::new();
    let subject = ts.mk_var("subject", Sort::String);
    let allchar = app(&mut ts, "re.allchar", &[], Sort::RegLan);
    let left = app(&mut ts, "re.*", &[allchar], Sort::RegLan);
    let needle_text = ts.mk_string("\\<SCRIPT".to_string());
    let needle = app(&mut ts, "str.to_re", &[needle_text], Sort::RegLan);
    let allchar = app(&mut ts, "re.allchar", &[], Sort::RegLan);
    let right = app(&mut ts, "re.*", &[allchar], Sort::RegLan);
    let regex = app(&mut ts, "re.++", &[left, needle, right], Sort::RegLan);
    let membership = app(&mut ts, "str.in_re", &[subject, regex], Sort::Bool);

    let satisfying = StubModel::new().with(subject, ModelValue::Str("xx\\<SCRIPTyy".to_string()));
    assert_confirmed(&verdict(&ts, &satisfying, &[membership]));

    let violating = StubModel::new().with(subject, ModelValue::Str("xx<SCRIPTyy".to_string()));
    assert_violates(&verdict(&ts, &violating, &[membership]));
}

#[test]
fn regex_membership_confirms_digit_intersection_witness() {
    let mut ts = TermStore::new();
    let subject = ts.mk_var("subject", Sort::String);
    let zero = ts.mk_string("0".to_string());
    let nine = ts.mk_string("9".to_string());
    let d0 = app(&mut ts, "re.range", &[zero, nine], Sort::RegLan);
    let d1 = app(&mut ts, "re.range", &[zero, nine], Sort::RegLan);
    let d2 = app(&mut ts, "re.range", &[zero, nine], Sort::RegLan);
    let exactly_three = app(&mut ts, "re.++", &[d0, d1, d2], Sort::RegLan);
    let digit = app(&mut ts, "re.range", &[zero, nine], Sort::RegLan);
    let any_digits = app(&mut ts, "re.*", &[digit], Sort::RegLan);
    let in_three = app(&mut ts, "str.in_re", &[subject, exactly_three], Sort::Bool);
    let in_any = app(&mut ts, "str.in_re", &[subject, any_digits], Sort::Bool);
    let model = StubModel::new().with(subject, ModelValue::Str("000".to_string()));

    assert_confirmed(&verdict(&ts, &model, &[in_three, in_any]));
}

#[test]
fn unsupported_regex_operator_fails_closed() {
    let mut ts = TermStore::new();
    let subject = ts.mk_var("subject", Sort::String);
    let opaque = app(&mut ts, "re.future", &[], Sort::RegLan);
    let membership = app(&mut ts, "str.in_re", &[subject, opaque], Sort::Bool);
    let model = StubModel::new().with(subject, ModelValue::Str("anything".to_string()));

    assert_cannot(&verdict(&ts, &model, &[membership]));
}

#[test]
fn sat_fp_to_real_uses_exact_ieee_fields() {
    let mut ts = TermStore::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let x = ts.mk_var("x", fp16);
    let to_real = app(&mut ts, "fp.to_real", &[x], Sort::Real);
    let five_halves = ts.mk_rational(BigRational::new(int(5), int(2)));
    let exact = app(&mut ts, "=", &[to_real, five_halves], Sort::Bool);

    // Float16 2.5 = sign 0, biased exponent 16, stored fraction 1/4.
    let model = StubModel::new().with(
        x,
        ModelValue::FloatingPoint {
            sign: false,
            exponent: 16,
            significand: 256,
            exponent_bits: 5,
            significand_bits: 11,
        },
    );
    assert_confirmed(&verdict(&ts, &model, &[exact]));
}

#[test]
fn fp_to_real_handles_subnormal_sign_and_both_zeros_exactly() {
    let mut ts = TermStore::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let negative_min = ts.mk_var("negative-min-subnormal", fp16.clone());
    let positive_zero = ts.mk_var("positive-zero", fp16.clone());
    let negative_zero = ts.mk_var("negative-zero", fp16);
    let negative_min_real = app(&mut ts, "fp.to_real", &[negative_min], Sort::Real);
    let positive_zero_real = app(&mut ts, "fp.to_real", &[positive_zero], Sort::Real);
    let negative_zero_real = app(&mut ts, "fp.to_real", &[negative_zero], Sort::Real);
    let expected_min = ts.mk_rational(BigRational::new(int(-1), BigInt::from(1u8) << 24usize));
    let zero = ts.mk_rational(BigRational::from_integer(int(0)));
    let min_exact = app(&mut ts, "=", &[negative_min_real, expected_min], Sort::Bool);
    let positive_zero_exact = app(&mut ts, "=", &[positive_zero_real, zero], Sort::Bool);
    let negative_zero_exact = app(&mut ts, "=", &[negative_zero_real, zero], Sort::Bool);
    let model = StubModel::new()
        .with(
            negative_min,
            ModelValue::FloatingPoint {
                sign: true,
                exponent: 0,
                significand: 1,
                exponent_bits: 5,
                significand_bits: 11,
            },
        )
        .with(
            positive_zero,
            ModelValue::FloatingPoint {
                sign: false,
                exponent: 0,
                significand: 0,
                exponent_bits: 5,
                significand_bits: 11,
            },
        )
        .with(
            negative_zero,
            ModelValue::FloatingPoint {
                sign: true,
                exponent: 0,
                significand: 0,
                exponent_bits: 5,
                significand_bits: 11,
            },
        );
    assert_confirmed(&verdict(
        &ts,
        &model,
        &[min_exact, positive_zero_exact, negative_zero_exact],
    ));
}

#[test]
fn fp_to_real_nonfinite_without_a_model_choice_and_malformed_payloads_fail_closed() {
    for (label, exponent, significand) in [
        ("positive-infinity", 31, 0),
        ("nan", 31, 512),
        ("malformed-significand", 0, 1024),
    ] {
        let mut ts = TermStore::new();
        let x = ts.mk_var(label, Sort::FloatingPoint(5, 11));
        let to_real = app(&mut ts, "fp.to_real", &[x], Sort::Real);
        let zero = ts.mk_rational(BigRational::from_integer(int(0)));
        let assertion = app(&mut ts, "=", &[to_real, zero], Sort::Bool);
        let model = StubModel::new().with(
            x,
            ModelValue::FloatingPoint {
                sign: false,
                exponent,
                significand,
                exponent_bits: 5,
                significand_bits: 11,
            },
        );
        assert_cannot(&verdict(&ts, &model, &[assertion]));
    }
}

#[test]
fn fp_to_real_nonfinite_uses_only_its_typed_fallback() {
    for (label, significand) in [("positive-infinity", 0), ("nan", 512)] {
        let mut ts = TermStore::new();
        let x = ts.mk_var(label, Sort::FloatingPoint(5, 11));
        let to_real = app(&mut ts, "fp.to_real", &[x], Sort::Real);
        let selected = BigRational::new(int(7), int(3));
        let expected = ts.mk_rational(selected.clone());
        let assertion = app(&mut ts, "=", &[to_real, expected], Sort::Bool);
        let model = UfStubModel::new()
            .leaf(
                x,
                ModelValue::FloatingPoint {
                    sign: false,
                    exponent: 31,
                    significand,
                    exponent_bits: 5,
                    significand_bits: 11,
                },
            )
            .unconstrained(
                to_real,
                ProvenUnconstrainedKind::FpToRealNonFinite,
                ModelValue::Real(selected),
            );

        assert_confirmed(&verdict(&ts, &model, &[assertion]));
        assert_eq!(model.unconstrained_calls.get(), 1, "{label}");
    }
}

#[test]
fn finite_fp_to_real_never_consults_unconstrained_fallback() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("finite", Sort::FloatingPoint(5, 11));
    let to_real = app(&mut ts, "fp.to_real", &[x], Sort::Real);
    let five_halves = ts.mk_rational(BigRational::new(int(5), int(2)));
    let assertion = app(&mut ts, "=", &[to_real, five_halves], Sort::Bool);
    let model = UfStubModel::new()
        .leaf(
            x,
            ModelValue::FloatingPoint {
                sign: false,
                exponent: 16,
                significand: 256,
                exponent_bits: 5,
                significand_bits: 11,
            },
        )
        .unconstrained(
            to_real,
            ProvenUnconstrainedKind::FpToRealNonFinite,
            ModelValue::Real(BigRational::from_integer(int(99))),
        );

    assert_confirmed(&verdict(&ts, &model, &[assertion]));
    assert_eq!(model.unconstrained_calls.get(), 0);
}

#[test]
fn nonfinite_fp_to_real_rejects_wrong_sort_fallback() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("infinity", Sort::FloatingPoint(5, 11));
    let to_real = app(&mut ts, "fp.to_real", &[x], Sort::Real);
    let model = UfStubModel::new()
        .leaf(
            x,
            ModelValue::FloatingPoint {
                sign: false,
                exponent: 31,
                significand: 0,
                exponent_bits: 5,
                significand_bits: 11,
            },
        )
        .unconstrained(
            to_real,
            ProvenUnconstrainedKind::FpToRealNonFinite,
            ModelValue::Bool(true),
        );

    match evaluate_term(&ts, &model, to_real) {
        EvalOutcome::Unevaluable(reason) => assert!(reason.contains("must still be a real")),
        other => panic!("wrong-sort fp.to_real fallback must fail closed, got {other:?}"),
    }
}

#[test]
fn fp_to_real_rejects_ill_typed_or_mismatched_formats_before_fallback() {
    let cases = [
        ("integer operand", Sort::Int, 5, 11, Sort::Real),
        (
            "payload format mismatch",
            Sort::FloatingPoint(5, 11),
            8,
            24,
            Sort::Real,
        ),
        (
            "non-real result",
            Sort::FloatingPoint(5, 11),
            5,
            11,
            Sort::Int,
        ),
    ];

    for (label, operand_sort, payload_eb, payload_sb, result_sort) in cases {
        let mut ts = TermStore::new();
        let x = ts.mk_var(label, operand_sort);
        let to_real = app(&mut ts, "fp.to_real", &[x], result_sort);
        let model = UfStubModel::new()
            .leaf(
                x,
                ModelValue::FloatingPoint {
                    sign: false,
                    exponent: (1u64 << payload_eb) - 1,
                    significand: 0,
                    exponent_bits: payload_eb,
                    significand_bits: payload_sb,
                },
            )
            .unconstrained(
                to_real,
                ProvenUnconstrainedKind::FpToRealNonFinite,
                ModelValue::Real(BigRational::from_integer(int(7))),
            );

        assert!(
            matches!(
                evaluate_term(&ts, &model, to_real),
                EvalOutcome::Unevaluable(_)
            ),
            "{label} must fail closed"
        );
        assert_eq!(
            model.unconstrained_calls.get(),
            0,
            "{label} must not mint typed authority"
        );
    }
}

#[test]
fn legacy_unconstrained_hook_applies_only_to_nonfinite_fp_to_real() {
    let mut ts = TermStore::new();
    let nan = ts.mk_var("nan", Sort::FloatingPoint(5, 11));
    let to_real = app(&mut ts, "fp.to_real", &[nan], Sort::Real);
    let one = ts.mk_rational(BigRational::from_integer(int(1)));
    let zero = ts.mk_rational(BigRational::from_integer(int(0)));
    let real_div = app(&mut ts, "/", &[one, zero], Sort::Real);
    let model = LegacyUnconstrainedModel::new()
        .leaf(
            nan,
            ModelValue::FloatingPoint {
                sign: false,
                exponent: 31,
                significand: 1,
                exponent_bits: 5,
                significand_bits: 11,
            },
        )
        .unconstrained(to_real, ModelValue::Real(BigRational::from_integer(int(7))))
        .unconstrained(
            real_div,
            ModelValue::Real(BigRational::from_integer(int(9))),
        );

    assert!(matches!(
        evaluate_term(&ts, &model, to_real),
        EvalOutcome::Value(ModelValue::Real(value)) if value == BigRational::from_integer(int(7))
    ));
    assert_eq!(model.unconstrained_calls.get(), 1);

    // A legacy implementation opted into the historical fp.to_real case, not
    // the later division-by-zero cases. The default typed hook must therefore
    // leave this application unevaluable instead of consulting the old hook.
    assert!(matches!(
        evaluate_term(&ts, &model, real_div),
        EvalOutcome::Unevaluable(_)
    ));
    assert_eq!(model.unconstrained_calls.get(), 1);
}

#[test]
fn distinct_nan_encodings_share_one_fp_to_real_graph_choice() {
    let mut ts = TermStore::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let first_nan = ts.mk_var("first-nan", fp16.clone());
    let second_nan = ts.mk_var("second-nan", fp16);
    let first_to_real = app(&mut ts, "fp.to_real", &[first_nan], Sort::Real);
    let second_to_real = app(&mut ts, "fp.to_real", &[second_nan], Sort::Real);
    let seven = ts.mk_rational(BigRational::from_integer(int(7)));
    let eight = ts.mk_rational(BigRational::from_integer(int(8)));
    let first_definition = app(&mut ts, "=", &[first_to_real, seven], Sort::Bool);
    let conflicting_definition = app(&mut ts, "=", &[second_to_real, eight], Sort::Bool);
    let model = UfStubModel::new()
        .leaf(
            first_nan,
            ModelValue::FloatingPoint {
                sign: false,
                exponent: 31,
                significand: 1,
                exponent_bits: 5,
                significand_bits: 11,
            },
        )
        .leaf(
            second_nan,
            ModelValue::FloatingPoint {
                sign: true,
                exponent: 31,
                significand: 512,
                exponent_bits: 5,
                significand_bits: 11,
            },
        )
        .unconstrained(
            first_to_real,
            ProvenUnconstrainedKind::FpToRealNonFinite,
            ModelValue::Real(BigRational::from_integer(int(7))),
        )
        .unconstrained(
            second_to_real,
            ProvenUnconstrainedKind::FpToRealNonFinite,
            ModelValue::Real(BigRational::from_integer(int(8))),
        );

    // SMT-LIB has one NaN value per format. The two encodings are therefore
    // equal graph arguments, so fp.to_real must make one consistent choice.
    assert_violates(&verdict(
        &ts,
        &model,
        &[first_definition, conflicting_definition],
    ));
    assert_eq!(model.unconstrained_calls.get(), 1);
}
