// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hand-constructed `(assertions, model)` pairs exercising the gate:
//!
//! * (a) models that SATISFY ⇒ `ConfirmedSat`;
//! * (b) models that VIOLATE an assertion ⇒ `ModelViolates` — including
//!   analogues of real wrong-`sat` bugs (seq prefix, array select, datatype
//!   recognizer, seq.indexof);
//! * (c) under-specified / unimplemented / unpinned / quantified ⇒
//!   `CannotConfirm` (never a false `ConfirmedSat`).

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::cell::Cell;
use std::collections::HashMap;

/// A trivial stub model: a fixed map from leaf `TermId` to value.
struct StubModel {
    leaves: HashMap<TermId, ModelValue>,
}

impl StubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
        }
    }
    fn with(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
}

impl ModelView for StubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
}

fn int(n: i64) -> BigInt {
    BigInt::from(n)
}

fn sqrt_two_between(lo: BigRational, hi: BigRational) -> ModelValue {
    ModelValue::Algebraic(Box::new(
        algebraic::Algebraic::root_of(algebraic::integer_poly(&[-2, 0, 1]), lo, hi)
            .expect("the interval isolates positive sqrt(2)"),
    ))
}

fn app(ts: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    ts.mk_app(Symbol::named(name), args, sort)
}

fn verdict(ts: &TermStore, model: &dyn ModelView, asserts: &[TermId]) -> GateVerdict {
    confirm_model(ts, model, asserts)
}

fn assert_confirmed(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::ConfirmedSat),
        "expected ConfirmedSat, got {v:?}"
    );
}
fn assert_violates(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::ModelViolates { .. }),
        "expected ModelViolates, got {v:?}"
    );
}
fn assert_cannot(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::CannotConfirm { .. }),
        "expected CannotConfirm, got {v:?}"
    );
}

// ===========================================================================
// (a) Satisfying models ⇒ ConfirmedSat
// ===========================================================================

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

#[test]
fn sat_array_store_select() {
    // (= (select (store a 1 9) 1) 9) holds for ANY a.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a = ts.mk_var("a", asort.clone());
    let one = ts.mk_int(int(1));
    let nine = ts.mk_int(int(9));
    let stored = app(&mut ts, "store", &[a, one, nine], asort);
    let sel = app(&mut ts, "select", &[stored, one], Sort::Int);
    let eq = app(&mut ts, "=", &[sel, nine], Sort::Bool);
    // a as a const-0 array — irrelevant, the store overrides index 1.
    let m = StubModel::new().with(
        a,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: vec![],
        })),
    );
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn array_default_reads_model_else_value_and_rejects_disagreement() {
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let default = app(&mut ts, "default", &[a], Sort::Int);
    let five = ts.mk_int(int(5));
    let six = ts.mk_int(int(6));
    let equals_five = app(&mut ts, "=", &[default, five], Sort::Bool);
    let equals_six = app(&mut ts, "=", &[default, six], Sort::Bool);
    let model = StubModel::new().with(
        a,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(5)),
            store: vec![],
        })),
    );

    assert_confirmed(&verdict(&ts, &model, &[equals_five]));
    assert_violates(&verdict(&ts, &model, &[equals_six]));
}

#[test]
fn array_default_reduces_const_and_store_but_unpinned_leaf_fails_closed() {
    let mut ts = TermStore::new();
    let five = ts.mk_int(int(5));
    let const_five = app(
        &mut ts,
        "const-array",
        &[five],
        Sort::array(Sort::Int, Sort::Int),
    );
    let unpinned_index = ts.mk_var("unpinned_index", Sort::Int);
    let unpinned_value = ts.mk_var("unpinned_value", Sort::Int);
    let stored = app(
        &mut ts,
        "store",
        &[const_five, unpinned_index, unpinned_value],
        Sort::array(Sort::Int, Sort::Int),
    );
    let structural_default = app(&mut ts, "default", &[stored], Sort::Int);
    let structural_eq = app(&mut ts, "=", &[structural_default, five], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[structural_eq]));

    let free = ts.mk_var("free", Sort::array(Sort::Int, Sort::Int));
    let unpinned_default = app(&mut ts, "default", &[free], Sort::Int);
    let zero = ts.mk_int(int(0));
    let unpinned_eq = app(&mut ts, "=", &[unpinned_default, zero], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[unpinned_eq]));
}

#[test]
fn dependent_lambda_default_uses_only_committed_opaque_scalar() {
    let mut ts = TermStore::new();
    let bound = ts.mk_var("bound", Sort::Bool);
    let one = ts.mk_int(int(1));
    let zero = ts.mk_int(int(0));
    let body = ts.mk_ite(bound, one, zero);
    let lambda = ts.mk_lambda_array(bound, body);
    let default = ts.mk_array_default(lambda);
    let two = ts.mk_int(int(2));
    let equals_two = app(&mut ts, "=", &[default, two], Sort::Bool);

    assert_confirmed(&verdict(
        &ts,
        &UfStubModel::new().uf(default, ModelValue::Int(int(2))),
        &[equals_two],
    ));
    assert_cannot(&verdict(&ts, &UfStubModel::new(), &[equals_two]));
}

#[test]
fn aliased_dependent_lambda_default_uses_only_committed_opaque_scalar() {
    let mut ts = TermStore::new();
    let bound = ts.mk_var("bound", Sort::Bool);
    let one = ts.mk_int(int(1));
    let zero = ts.mk_int(int(0));
    let body = ts.mk_ite(bound, one, zero);
    let lambda = ts.mk_lambda_array(bound, body);
    // Model an expanded define-fun/alias whose outer syntax hides the lambda
    // from `eval_array_default`'s direct fast path.
    let true_term = ts.mk_bool(true);
    let alias = ts.mk_ite(true_term, lambda, lambda);
    let default = ts.mk_array_default(alias);
    let two = ts.mk_int(int(2));
    let equals_two = app(&mut ts, "=", &[default, two], Sort::Bool);

    assert_confirmed(&verdict(
        &ts,
        &UfStubModel::new().uf(default, ModelValue::Int(int(2))),
        &[equals_two],
    ));
    assert_cannot(&verdict(&ts, &UfStubModel::new(), &[equals_two]));
}

#[test]
fn finite_store_default_uses_committed_scalar_instead_of_base_default() {
    let mut ts = TermStore::new();
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let false_term = ts.mk_bool(false);
    let array_sort = Sort::array(Sort::Bool, Sort::Int);
    let base = app(&mut ts, "const-array", &[zero], array_sort.clone());
    let stored = app(&mut ts, "store", &[base, false_term, one], array_sort);
    let default = app(&mut ts, "default", &[stored], Sort::Int);
    let assertion = app(&mut ts, "=", &[default, one], Sort::Bool);
    let model = UfStubModel::new().uf(default, ModelValue::Int(int(1)));

    assert_confirmed(&verdict(&ts, &model, &[assertion]));
}

#[test]
fn unit_store_default_is_structurally_the_stored_value() {
    let mut ts = TermStore::new();
    let unit_sort = Sort::FiniteDomain("Unit".to_string(), 1);
    let unit = ts.mk_var("unit", unit_sort.clone());
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let array_sort = Sort::array(unit_sort, Sort::Int);
    let base = app(&mut ts, "const-array", &[zero], array_sort.clone());
    let stored = app(&mut ts, "store", &[base, unit, one], array_sort);
    let default = app(&mut ts, "default", &[stored], Sort::Int);
    let assertion = app(&mut ts, "=", &[default, one], Sort::Bool);

    assert_confirmed(&verdict(&ts, &StubModel::new(), &[assertion]));
}

#[test]
fn malformed_array_default_fails_closed() {
    let mut ts = TermStore::new();
    let scalar = ts.mk_var("scalar", Sort::Int);
    let malformed = app(&mut ts, "default", &[scalar], Sort::Int);
    let zero = ts.mk_int(int(0));
    let assertion = app(&mut ts, "=", &[malformed, zero], Sort::Bool);
    let model = StubModel::new().with(scalar, ModelValue::Int(int(0)));
    assert_cannot(&verdict(&ts, &model, &[assertion]));
}

#[test]
fn sat_lambda_array_store_beta_reduces_and_restores_binding() {
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let x = ts.mk_var("x", Sort::Int);
    let one = ts.mk_int(int(1));
    let body = app(&mut ts, "+", &[x, one], Sort::Int);
    let lambda = ts.mk_lambda_array(x, body);
    let three = ts.mk_int(int(3));
    let five = ts.mk_int(int(5));
    let seven = ts.mk_int(int(7));
    let forty_two = ts.mk_int(int(42));
    let stored = app(&mut ts, "store", &[lambda, five, forty_two], asort);

    // Raw select applications ensure model-time store peeling and beta
    // reduction are exercised, rather than TermStore's eager rewrites.
    let at_stored = app(&mut ts, "select", &[stored, five], Sort::Int);
    let at_lambda = app(&mut ts, "select", &[stored, three], Sort::Int);
    let at_second_lambda_index = app(&mut ts, "select", &[stored, seven], Sort::Int);

    // The ambient model pin deliberately conflicts with both beta instances.
    // It must be shadowed only while the body is evaluated.
    let model = StubModel::new().with(x, ModelValue::Int(int(99)));
    let evaluator = Evaluator::new(&ts, &model);
    assert!(matches!(
        evaluator.evaluate(at_stored),
        EvalOutcome::Value(ModelValue::Int(n)) if n == int(42)
    ));
    assert!(matches!(
        evaluator.evaluate(at_lambda),
        EvalOutcome::Value(ModelValue::Int(n)) if n == int(4)
    ));
    // The body has the same TermId in both beta reductions. A TermId-only
    // memo must not reuse the value computed under x=3 when x=7 is active.
    assert!(matches!(
        evaluator.evaluate(at_second_lambda_index),
        EvalOutcome::Value(ModelValue::Int(n)) if n == int(8)
    ));
    assert!(matches!(
        evaluator.evaluate(body),
        EvalOutcome::Value(ModelValue::Int(n)) if n == int(100)
    ));
}

#[test]
fn sat_binder_independent_lambda_materializes_for_array_equality() {
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let x = ts.mk_var("x", Sort::Int);
    let zero = ts.mk_int(int(0));
    let five = ts.mk_int(int(5));
    let forty_two = ts.mk_int(int(42));
    let lambda = ts.mk_lambda_array(x, zero);
    let actual = app(&mut ts, "store", &[lambda, five, forty_two], asort.clone());
    let constant = app(&mut ts, "const-array", &[zero], asort.clone());
    let expected = app(&mut ts, "store", &[constant, five, forty_two], asort);
    let eq = app(&mut ts, "=", &[actual, expected], Sort::Bool);

    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn lambda_beta_does_not_trust_non_contextual_uf_pin() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let fx = app(&mut ts, "f", &[x], Sort::Int);
    let lambda = ts.mk_lambda_array(x, fx);
    let three = ts.mk_int(int(3));
    let seven = ts.mk_int(int(7));
    let read = app(&mut ts, "select", &[lambda, three], Sort::Int);
    let eq = app(&mut ts, "=", &[read, seven], Sort::Bool);

    // A per-TermId pin for f(x) is not a value for f(3): accepting it under the
    // beta binding would conflate distinct lambda environments. Fail closed.
    let model = UfStubModel::new().uf(fx, ModelValue::Int(int(7)));
    assert_cannot(&verdict(&ts, &model, &[eq]));
}

#[test]
fn lambda_beta_allows_binder_independent_model_pins() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let five = ts.mk_int(int(5));
    let f_five = app(&mut ts, "f", &[five], Sort::Int);
    let lambda_uf = ts.mk_lambda_array(x, f_five);
    let three = ts.mk_int(int(3));
    let uf_read = app(&mut ts, "select", &[lambda_uf, three], Sort::Int);
    let seven = ts.mk_int(int(7));
    let uf_eq = app(&mut ts, "=", &[uf_read, seven], Sort::Bool);
    let uf_model = UfStubModel::new().uf(f_five, ModelValue::Int(int(7)));
    assert_confirmed(&verdict(&ts, &uf_model, &[uf_eq]));

    let a = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let at_five = app(&mut ts, "select", &[a, five], Sort::Int);
    let lambda_select = ts.mk_lambda_array(x, at_five);
    let select_read = app(&mut ts, "select", &[lambda_select, three], Sort::Int);
    let select_eq = app(&mut ts, "=", &[select_read, seven], Sort::Bool);
    let select_model = UfStubModel::new().sel(at_five, ModelValue::Int(int(7)));
    assert_confirmed(&verdict(&ts, &select_model, &[select_eq]));
}

#[test]
fn lambda_beta_uf_reuses_only_a_value_keyed_graph_entry() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let three = ts.mk_int(int(3));
    let seven = ts.mk_int(int(7));

    // Seed the independent evaluator's graph with the concrete point f(3).
    let f_three = app(&mut ts, "f", &[three], Sort::Int);
    let seed = app(&mut ts, "=", &[f_three, seven], Sort::Bool);

    // The contextual f(x) has no per-TermId model pin. It is nevertheless the
    // same function point after beta reduction, so recursive argument
    // evaluation may soundly reuse the value-keyed f(3) graph entry.
    let f_x = app(&mut ts, "f", &[x], Sort::Int);
    let lambda = ts.mk_lambda_array(x, f_x);
    let read = app(&mut ts, "select", &[lambda, three], Sort::Int);
    let beta = app(&mut ts, "=", &[read, seven], Sort::Bool);
    let model = UfStubModel::new().uf(f_three, ModelValue::Int(int(7)));

    assert_confirmed(&verdict(&ts, &model, &[seed, beta]));
}

#[test]
fn lambda_beta_selector_fallback_rejects_context_free_pins() {
    let mut ts = TermStore::new();
    let pair = Sort::Datatype(DatatypeSort::new(
        "Pair",
        vec![DatatypeConstructor::new(
            "mk",
            vec![DatatypeField::new("fst", Sort::Int)],
        )],
    ));
    let x = ts.mk_var("x", Sort::Int);
    let a = ts.mk_var("a", Sort::array(Sort::Int, pair.clone()));
    let pair_at_x = app(&mut ts, "select", &[a, x], pair);
    let fst_at_x = app(&mut ts, "fst", &[pair_at_x], Sort::Int);
    let lambda = ts.mk_lambda_array(x, fst_at_x);
    let three = ts.mk_int(int(3));
    let read = app(&mut ts, "select", &[lambda, three], Sort::Int);
    let seven = ts.mk_int(int(7));
    let eq = app(&mut ts, "=", &[read, seven], Sort::Bool);

    // Neither commitment is indexed by the beta environment. In particular,
    // the selector fallback must not use the ambient value of select(a, x) to
    // manufacture a value for fst(select(a, 3)).
    let model = UfStubModel::new()
        .sel(
            pair_at_x,
            ModelValue::Datatype {
                ctor: "mk".to_string(),
                args: vec![ModelValue::Int(int(7))],
            },
        )
        .uf(fst_at_x, ModelValue::Int(int(7)));
    assert_cannot(&verdict(&ts, &model, &[eq]));
}

// ---------------------------------------------------------------------------
// S1 REGRESSION (the development design notes) — CLOSED at the gate level.
// UF congruence over equal arrays: (= (select a i) v) ⇒ store(a,i,v) ≡ a ⇒
// f(store(a,i,v)) = f(a), so (not (= (f (store a i v)) (f a))) is UNSAT. The
// independent gate now CATCHES a model that violates this as `ModelViolates`, via
// the congruence rule in `eval_eq` (equalities of same-head applications with
// argument-wise-equal values evaluate to `true`, no interpretation of `f` needed).
// The (unconditional) `ModelViolates` enforcement demotes S1's wrong `sat` to
// `unknown`.
// ---------------------------------------------------------------------------
#[test]
fn s1_uf_congruence_over_equal_arrays_should_violate() {
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a = ts.mk_var("a", asort.clone());
    let i = ts.mk_var("i", Sort::Int);
    let v = ts.mk_var("v", Sort::Int);
    // (= (select a i) v)
    let sel = app(&mut ts, "select", &[a, i], Sort::Int);
    let eq_sel_v = app(&mut ts, "=", &[sel, v], Sort::Bool);
    // (not (= (f (store a i v)) (f a)))  — with select(a,i)=v, store(a,i,v) ≡ a.
    let stored = app(&mut ts, "store", &[a, i, v], asort);
    let f_store = app(&mut ts, "f", &[stored], Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let eq_ff = app(&mut ts, "=", &[f_store, f_a], Sort::Bool);
    let neq_ff = app(&mut ts, "not", &[eq_ff], Sort::Bool);
    // Model: a = const-0 array, i = 0, v = 0  ⇒ select(a,0)=0=v and store(a,0,0) ≡ a.
    let m = StubModel::new()
        .with(
            a,
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![],
            })),
        )
        .with(i, ModelValue::Int(int(0)))
        .with(v, ModelValue::Int(int(0)));
    // TARGET behaviour once the congruence rule lands (today: CannotConfirm ⇒ this fails):
    assert_violates(&verdict(&ts, &m, &[eq_sel_v, neq_ff]));
}

#[test]
fn sat_const_array() {
    // (= (select (const-array 5) 99) 5).
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let five = ts.mk_int(int(5));
    let ca = app(&mut ts, "const-array", &[five], asort);
    let n99 = ts.mk_int(int(99));
    let sel = app(&mut ts, "select", &[ca, n99], Sort::Int);
    let eq = app(&mut ts, "=", &[sel, five], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn sat_seq_prefix_and_len() {
    // (seq.prefixof (seq.unit true) s) with s = [true, false]; and
    // (= (seq.len (seq.++ (seq.unit 1) (seq.unit 2))) 2).
    let mut ts = TermStore::new();
    let sseq = Sort::seq(Sort::Bool);
    let s = ts.mk_var("s", sseq.clone());
    let tt = ts.mk_bool(true);
    let unit_t = app(&mut ts, "seq.unit", &[tt], sseq.clone());
    let pre = app(&mut ts, "seq.prefixof", &[unit_t, s], Sort::Bool);

    let iseq = Sort::seq(Sort::Int);
    let i1 = ts.mk_int(int(1));
    let i2 = ts.mk_int(int(2));
    let u1 = app(&mut ts, "seq.unit", &[i1], iseq.clone());
    let u2 = app(&mut ts, "seq.unit", &[i2], iseq.clone());
    let cat = app(&mut ts, "seq.++", &[u1, u2], iseq);
    let len = app(&mut ts, "seq.len", &[cat], Sort::Int);
    let two = ts.mk_int(int(2));
    let eqlen = app(&mut ts, "=", &[len, two], Sort::Bool);

    let m = StubModel::new().with(
        s,
        ModelValue::Seq(vec![ModelValue::Bool(true), ModelValue::Bool(false)]),
    );
    assert_confirmed(&verdict(&ts, &m, &[pre, eqlen]));
}

#[test]
fn sat_datatype_constructor_selector() {
    // (= (fst (mk 3 4)) 3) for datatype Pair = mk(fst: Int, snd: Int).
    let mut ts = TermStore::new();
    let pair = Sort::Datatype(DatatypeSort::new(
        "Pair",
        vec![DatatypeConstructor::new(
            "mk",
            vec![
                DatatypeField::new("fst", Sort::Int),
                DatatypeField::new("snd", Sort::Int),
            ],
        )],
    ));
    let i3 = ts.mk_int(int(3));
    let i4 = ts.mk_int(int(4));
    let mk = app(&mut ts, "mk", &[i3, i4], pair);
    let fst = app(&mut ts, "fst", &[mk], Sort::Int);
    let eq = app(&mut ts, "=", &[fst, i3], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

// ===========================================================================
// (b) Violating models ⇒ ModelViolates  (caught wrong-`sat`)
// ===========================================================================

#[test]
fn violate_seq_prefix_empty() {
    // BUG ANALOGUE: s = [] (or [false]) under (seq.prefixof (seq.unit true) s).
    let mut ts = TermStore::new();
    let sseq = Sort::seq(Sort::Bool);
    let s = ts.mk_var("s", sseq.clone());
    let tt = ts.mk_bool(true);
    let unit_t = app(&mut ts, "seq.unit", &[tt], sseq);
    let pre = app(&mut ts, "seq.prefixof", &[unit_t, s], Sort::Bool);

    let empty = StubModel::new().with(s, ModelValue::Seq(vec![]));
    assert_violates(&verdict(&ts, &empty, &[pre]));

    let false_only = StubModel::new().with(s, ModelValue::Seq(vec![ModelValue::Bool(false)]));
    assert_violates(&verdict(&ts, &false_only, &[pre]));
}

#[test]
fn violate_array_select() {
    // BUG ANALOGUE: a = const-0 under (= (select a 1) 9).
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a = ts.mk_var("a", asort);
    let one = ts.mk_int(int(1));
    let nine = ts.mk_int(int(9));
    let sel = app(&mut ts, "select", &[a, one], Sort::Int);
    let eq = app(&mut ts, "=", &[sel, nine], Sort::Bool);
    let m = StubModel::new().with(
        a,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: vec![],
        })),
    );
    assert_violates(&verdict(&ts, &m, &[eq]));
}

#[test]
fn violate_datatype_recognizer_and_bool() {
    // BUG ANALOGUE (datatype/Bool): ((_ is Red) c) with c = Green.
    let mut ts = TermStore::new();
    let color = Sort::enum_type("Color", ["Red", "Green"]);
    let c = ts.mk_var("c", color);
    let is_red = app(&mut ts, "is-Red", &[c], Sort::Bool);
    let m = StubModel::new().with(
        c,
        ModelValue::Datatype {
            ctor: "Green".to_string(),
            args: vec![],
        },
    );
    assert_violates(&verdict(&ts, &m, &[is_red]));

    // Plain Bool violation: assert p, model says p = false.
    let mut ts2 = TermStore::new();
    let p = ts2.mk_var("p", Sort::Bool);
    let mp = StubModel::new().with(p, ModelValue::Bool(false));
    assert_violates(&verdict(&ts2, &mp, &[p]));
}

#[test]
fn violate_seq_indexof() {
    // BUG ANALOGUE (indexof): claim "7 is absent" — (= (seq.indexof s [7] 0) -1)
    // — but the model has s = [7], where the true index is 0.
    let mut ts = TermStore::new();
    let iseq = Sort::seq(Sort::Int);
    let s = ts.mk_var("s", iseq.clone());
    let seven = ts.mk_int(int(7));
    let unit7 = app(&mut ts, "seq.unit", &[seven], iseq);
    let zero = ts.mk_int(int(0));
    let idx = app(&mut ts, "seq.indexof", &[s, unit7, zero], Sort::Int);
    let neg1 = ts.mk_int(int(-1));
    let eq = app(&mut ts, "=", &[idx, neg1], Sort::Bool);
    let m = StubModel::new().with(s, ModelValue::Seq(vec![ModelValue::Int(int(7))]));
    assert_violates(&verdict(&ts, &m, &[eq]));
}

#[test]
fn violate_bitvector() {
    // (= (bvadd #b0011 #b0001) #b0000) — actually 0100.
    let mut ts = TermStore::new();
    let a = ts.mk_bitvec(int(3), 4);
    let b = ts.mk_bitvec(int(1), 4);
    let zero = ts.mk_bitvec(int(0), 4);
    let sum = app(&mut ts, "bvadd", &[a, b], Sort::bitvec(4));
    let eq = app(&mut ts, "=", &[sum, zero], Sort::Bool);
    assert_violates(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn violate_one_of_many_assertions() {
    // First assertion holds, second is falsified — gate must report violation.
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let zero = ts.mk_int(int(0));
    let ten = ts.mk_int(int(10));
    let ge = app(&mut ts, ">=", &[x, zero], Sort::Bool); // x >= 0  (true)
    let eq = app(&mut ts, "=", &[x, ten], Sort::Bool); // x = 10  (false)
    let m = StubModel::new().with(x, ModelValue::Int(int(3)));
    assert_violates(&verdict(&ts, &m, &[ge, eq]));
}

// ===========================================================================
// (c) Cannot confirm  (fail closed — never a false ConfirmedSat)
// ===========================================================================

#[test]
fn cannot_unpinned_leaf() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Bool);
    // model pins nothing.
    assert_cannot(&verdict(&ts, &StubModel::new(), &[x]));
}

#[test]
fn cannot_uninterpreted_function() {
    // (= (f 3) 5) where f is an uninterpreted function the gate does not value.
    let mut ts = TermStore::new();
    let i3 = ts.mk_int(int(3));
    let fa = app(&mut ts, "f", &[i3], Sort::Int);
    let five = ts.mk_int(int(5));
    let eq = app(&mut ts, "=", &[fa, five], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn cannot_quantifier() {
    let mut ts = TermStore::new();
    let y = ts.mk_var("y", Sort::Int);
    let zero = ts.mk_int(int(0));
    let body = app(&mut ts, ">=", &[y, zero], Sort::Bool);
    let forall = ts.mk_forall(vec![("y".to_string(), Sort::Int)], body);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[forall]));
}

#[test]
fn cannot_unimplemented_op() {
    // A floating-point op is intentionally not implemented ⇒ unevaluable.
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::FloatingPoint(8, 24));
    let is_nan = app(&mut ts, "fp.isNaN", &[x], Sort::Bool);
    let m = StubModel::new(); // even if pinned, fp.isNaN is unimplemented.
    assert_cannot(&verdict(&ts, &m, &[is_nan]));
}

#[test]
fn cannot_selector_wrong_constructor() {
    // Selector applied to a value built with a different constructor is
    // under-specified ⇒ unevaluable, NOT a fabricated value.
    let mut ts = TermStore::new();
    let dt = DatatypeSort::new(
        "T",
        vec![
            DatatypeConstructor::new("A", vec![DatatypeField::new("geta", Sort::Int)]),
            DatatypeConstructor::new("B", vec![DatatypeField::new("getb", Sort::Int)]),
        ],
    );
    let tsort = Sort::Datatype(dt);
    let x = ts.mk_var("x", tsort.clone());
    // (= (geta x) 0) but x is built with constructor B.
    let geta = app(&mut ts, "geta", &[x], Sort::Int);
    let zero = ts.mk_int(int(0));
    let eq = app(&mut ts, "=", &[geta, zero], Sort::Bool);
    let m = StubModel::new().with(
        x,
        ModelValue::Datatype {
            ctor: "B".to_string(),
            args: vec![ModelValue::Int(int(0))],
        },
    );
    assert_cannot(&verdict(&ts, &m, &[eq]));
}

// ===========================================================================
// Targeted operator-semantics checks
// ===========================================================================

#[test]
fn and_false_with_unevaluable_sibling_is_false() {
    // (and false <unpinned x>) must be Bool(false), not Unevaluable — so an
    // assertion (not (and false x)) is confirmed even though x is unpinned.
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Bool);
    let ff = ts.mk_bool(false);
    let conj = app(&mut ts, "and", &[ff, x], Sort::Bool);
    let neg = ts.mk_not(conj);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[neg]));
}

#[test]
fn or_true_with_unevaluable_sibling_is_true() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Bool);
    let tt = ts.mk_bool(true);
    let disj = app(&mut ts, "or", &[tt, x], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[disj]));
}

#[test]
fn ite_only_evaluates_taken_branch() {
    // (= (ite true 1 <unpinned>) 1): the else branch must not be evaluated.
    let mut ts = TermStore::new();
    let tt = ts.mk_bool(true);
    let one = ts.mk_int(int(1));
    let junk = ts.mk_var("junk", Sort::Int); // unpinned
    let ite = ts.mk_ite(tt, one, junk);
    let eq = app(&mut ts, "=", &[ite, one], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn distinct_detects_duplicate() {
    // (distinct 1 2 1) is false.
    let mut ts = TermStore::new();
    let a = ts.mk_int(int(1));
    let b = ts.mk_int(int(2));
    let c = ts.mk_int(int(1));
    let d = app(&mut ts, "distinct", &[a, b, c], Sort::Bool);
    assert_violates(&verdict(&ts, &StubModel::new(), &[d]));
}

#[test]
fn array_equality_extensional() {
    // (= (store (const-array 0) 1 5) (store (const-array 0) 1 5)) is true;
    // changing one value breaks equality.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let z = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let five = ts.mk_int(int(5));
    let six = ts.mk_int(int(6));
    let ca1 = app(&mut ts, "const-array", &[z], asort.clone());
    let ca2 = app(&mut ts, "const-array", &[z], asort.clone());
    let s1 = app(&mut ts, "store", &[ca1, one, five], asort.clone());
    let s2 = app(&mut ts, "store", &[ca2, one, five], asort.clone());
    let eq = app(&mut ts, "=", &[s1, s2], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));

    let s3 = app(&mut ts, "store", &[ca1, one, six], asort);
    let neq = app(&mut ts, "=", &[s1, s3], Sort::Bool);
    assert_violates(&verdict(&ts, &StubModel::new(), &[neq]));
}

#[test]
fn bool_index_array_differing_defaults_do_not_prove_disequality() {
    // Both arrays denote the constant-zero function over Bool: the left array's
    // two stores cover the complete index domain, so its default `1` is
    // unreachable. A value-only comparator cannot use the differing defaults
    // as evidence for `(distinct left right)` without carrying the index sort.
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Int);
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let false_index = ts.mk_bool(false);
    let true_index = ts.mk_bool(true);
    let one_default = app(&mut ts, "const-array", &[one], array_sort.clone());
    let with_false = app(
        &mut ts,
        "store",
        &[one_default, false_index, zero],
        array_sort.clone(),
    );
    let fully_covered = app(
        &mut ts,
        "store",
        &[with_false, true_index, zero],
        array_sort.clone(),
    );
    let zero_default = app(&mut ts, "const-array", &[zero], array_sort);
    let disequality = app(
        &mut ts,
        "distinct",
        &[fully_covered, zero_default],
        Sort::Bool,
    );

    assert_cannot(&verdict(&ts, &StubModel::new(), &[disequality]));
}

#[test]
fn evaluate_term_exposes_outcome() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let one = ts.mk_int(int(1));
    let sum = app(&mut ts, "+", &[x, one], Sort::Int);
    let m = StubModel::new().with(x, ModelValue::Int(int(41)));
    match evaluate_term(&ts, &m, sum) {
        EvalOutcome::Value(ModelValue::Int(n)) => assert_eq!(n, int(42)),
        other => panic!("expected Int(42), got {other:?}"),
    }
}

// ===========================================================================
// (d) Uninterpreted-function applications — value-keyed function graph
//
// An uninterpreted function is single-valued: two applications whose ARGUMENTS
// evaluate to equal values must return the same value. The gate builds a
// value-keyed graph as it evaluates (`uf_app_value` supplies the committed
// per-application value); the FIRST application to reach a given
// `(name, arg-values)` key fixes the value for every later application with the
// same key. This is what catches the QF_UFLIA / array-select wrong-model class
// where a degenerate integer assignment collapses two distinct applications'
// arguments to the same value while the model pins them to different results.
// ===========================================================================

/// A model implementing only the original one-argument unconstrained hook.
///
/// Its tests protect source compatibility and, more importantly, prove that
/// the new typed default does not silently extend this legacy authority to
/// division-by-zero applications.
struct LegacyUnconstrainedModel {
    leaves: HashMap<TermId, ModelValue>,
    unconstrained_apps: HashMap<TermId, ModelValue>,
    unconstrained_calls: Cell<usize>,
}

impl LegacyUnconstrainedModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            unconstrained_apps: HashMap::new(),
            unconstrained_calls: Cell::new(0),
        }
    }

    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }

    fn unconstrained(mut self, t: TermId, v: ModelValue) -> Self {
        self.unconstrained_apps.insert(t, v);
        self
    }
}

impl ModelView for LegacyUnconstrainedModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }

    fn unconstrained_app_value(&self, t: TermId) -> Option<ModelValue> {
        self.unconstrained_calls
            .set(self.unconstrained_calls.get() + 1);
        self.unconstrained_apps.get(&t).cloned()
    }
}

/// A stub model that also answers `uf_app_value` for whole application terms.
struct UfStubModel {
    leaves: HashMap<TermId, ModelValue>,
    uf_apps: HashMap<TermId, ModelValue>,
    unconstrained_apps: HashMap<TermId, (ProvenUnconstrainedKind, ModelValue)>,
    unconstrained_calls: Cell<usize>,
    selects: HashMap<TermId, ModelValue>,
    projections: HashMap<TermId, usize>,
    projection_errors: HashMap<TermId, String>,
}

impl UfStubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            uf_apps: HashMap::new(),
            unconstrained_apps: HashMap::new(),
            unconstrained_calls: Cell::new(0),
            selects: HashMap::new(),
            projections: HashMap::new(),
            projection_errors: HashMap::new(),
        }
    }
    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
    fn uf(mut self, t: TermId, v: ModelValue) -> Self {
        self.uf_apps.insert(t, v);
        self
    }
    fn unconstrained(mut self, t: TermId, kind: ProvenUnconstrainedKind, v: ModelValue) -> Self {
        self.unconstrained_apps.insert(t, (kind, v));
        self
    }
    fn sel(mut self, t: TermId, v: ModelValue) -> Self {
        self.selects.insert(t, v);
        self
    }
    fn projection(mut self, t: TermId, selected: usize) -> Self {
        self.projections.insert(t, selected);
        self
    }
    fn projection_error(mut self, t: TermId, detail: &str) -> Self {
        self.projection_errors.insert(t, detail.to_string());
        self
    }
}

impl ModelView for UfStubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
    fn projection_argument(&self, t: TermId) -> Result<Option<usize>, ProjectionLookupError> {
        if let Some(detail) = self.projection_errors.get(&t) {
            return Err(ProjectionLookupError::inconsistent_model(detail.clone()));
        }
        Ok(self.projections.get(&t).copied())
    }
    fn uf_app_value(&self, t: TermId) -> Option<ModelValue> {
        self.uf_apps.get(&t).cloned()
    }
    fn proven_unconstrained_app_value(
        &self,
        t: TermId,
        kind: ProvenUnconstrainedKind,
    ) -> Option<ModelValue> {
        self.unconstrained_calls
            .set(self.unconstrained_calls.get() + 1);
        self.unconstrained_apps
            .get(&t)
            .and_then(|(expected, value)| (*expected == kind).then(|| value.clone()))
    }
    fn array_select_value(&self, t: TermId) -> Option<ModelValue> {
        self.selects.get(&t).cloned()
    }
}

#[test]
fn uf_collapsed_arguments_refute_strict_inequality() {
    // The uflia89 shape: `(> (f (* 3 i0)) (f i0))` with `i0 = 0`. Both `(* 3 i0)`
    // and `i0` evaluate to 0, so both applications are `f(0)`; the model pins
    // them to different results (0 and -1). The gate collapses them to one value
    // (first-wins), so `(> v v)` is `false` — a caught wrong witness. (Emitting
    // 0 and -1 for the SAME `f(0)` is exactly the internally-inconsistent model
    // z3 rejects when the scalars are pinned.)
    let mut ts = TermStore::new();
    let i0 = ts.mk_var("i0", Sort::Int);
    let three = ts.mk_int(int(3));
    let mul = app(&mut ts, "*", &[three, i0], Sort::Int);
    let f_hi = app(&mut ts, "f", &[mul], Sort::Int); // f(3*i0)
    let f_lo = app(&mut ts, "f", &[i0], Sort::Int); // f(i0)
    let gt = app(&mut ts, ">", &[f_hi, f_lo], Sort::Bool);
    let m = UfStubModel::new()
        .leaf(i0, ModelValue::Int(int(0)))
        .uf(f_hi, ModelValue::Int(int(0)))
        .uf(f_lo, ModelValue::Int(int(-1)));
    assert_violates(&verdict(&ts, &m, &[gt]));
}

#[test]
fn uf_distinct_arguments_confirm_valid_model() {
    // Distinct arguments (a = 5, b = 7): the two applications key differently and
    // keep their own committed values (f(5) = 1 > f(7) = 0), so the witness is
    // confirmed. The UF handling must NOT over-refute genuine models.
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let f_b = app(&mut ts, "f", &[b], Sort::Int);
    let gt = app(&mut ts, ">", &[f_a, f_b], Sort::Bool);
    let m = UfStubModel::new()
        .leaf(a, ModelValue::Int(int(5)))
        .leaf(b, ModelValue::Int(int(7)))
        .uf(f_a, ModelValue::Int(int(1)))
        .uf(f_b, ModelValue::Int(int(0)));
    assert_confirmed(&verdict(&ts, &m, &[gt]));
}

#[test]
fn uf_congruent_applications_share_one_value() {
    // Two applications with equal arguments (a = b = 5) must denote the same
    // value: `(= (f a) (f b))` holds even though the model pins them to
    // different committed values (the first-seen value, 1, wins for both).
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let f_b = app(&mut ts, "f", &[b], Sort::Int);
    let eq = app(&mut ts, "=", &[f_a, f_b], Sort::Bool);
    let m = UfStubModel::new()
        .leaf(a, ModelValue::Int(int(5)))
        .leaf(b, ModelValue::Int(int(5)))
        .uf(f_a, ModelValue::Int(int(1)))
        .uf(f_b, ModelValue::Int(int(2)));
    // Congruent apps collapse to one value, so equality is TRUE (not a spurious
    // violation): `(= 1 1)`.
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn uf_array_keys_with_finite_domain_coverage_fail_closed() {
    // The two array arguments are extensionally equal over Bool even though
    // their stored defaults differ: the left stores cover both domain values.
    // They therefore denote one UF graph key. Without index-sort evidence the
    // key comparison must remain unresolved, never install two results and
    // confirm the impossible conjunction `f(left) = 7 ∧ f(right) = 8`.
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Int);
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let false_index = ts.mk_bool(false);
    let true_index = ts.mk_bool(true);
    let one_default = app(&mut ts, "const-array", &[one], array_sort.clone());
    let with_false = app(
        &mut ts,
        "store",
        &[one_default, false_index, zero],
        array_sort.clone(),
    );
    let fully_covered = app(
        &mut ts,
        "store",
        &[with_false, true_index, zero],
        array_sort.clone(),
    );
    let zero_default = app(&mut ts, "const-array", &[zero], array_sort);
    let left_app = app(&mut ts, "f", &[fully_covered], Sort::Int);
    let right_app = app(&mut ts, "f", &[zero_default], Sort::Int);
    let seven = ts.mk_int(int(7));
    let eight = ts.mk_int(int(8));
    let left_definition = app(&mut ts, "=", &[left_app, seven], Sort::Bool);
    let right_definition = app(&mut ts, "=", &[right_app, eight], Sort::Bool);
    let model = UfStubModel::new()
        .uf(left_app, ModelValue::Int(int(7)))
        .uf(right_app, ModelValue::Int(int(8)));

    assert_cannot(&verdict(&ts, &model, &[left_definition, right_definition]));
}

#[test]
fn congruence_key_definite_difference_overrides_an_unresolved_component() {
    // A multi-argument graph entry is a definite miss when ANY component is
    // proven different, even if another component's equality is undecidable.
    // The matcher must scan past the algebraic gap rather than failing closed
    // too early and needlessly losing a valid, distinct function point.
    let stored = vec![
        sqrt_two_between(
            BigRational::from_integer(int(1)),
            BigRational::from_integer(int(2)),
        ),
        ModelValue::Int(int(1)),
    ];
    let candidate = vec![
        sqrt_two_between(
            BigRational::new(int(4), int(3)),
            BigRational::new(int(3), int(2)),
        ),
        ModelValue::Int(int(2)),
    ];

    assert!(matches!(
        eval::congruence_keys_equal(&stored, &candidate),
        Ok(false)
    ));
}

#[test]
fn selector_graph_key_matcher_fails_closed_on_nested_algebraic_gap() {
    // Selector fallback keys are committed datatype values. Two equal
    // datatype values can carry equal algebraic fields represented in
    // different extensions, so the recursive `value_eq` gap must propagate;
    // it is not evidence that two selector arguments are distinct.
    let stored = ModelValue::Datatype {
        ctor: "WrongConstructor".to_string(),
        args: vec![sqrt_two_between(
            BigRational::from_integer(int(1)),
            BigRational::from_integer(int(2)),
        )],
    };
    let candidate = ModelValue::Datatype {
        ctor: "WrongConstructor".to_string(),
        args: vec![sqrt_two_between(
            BigRational::new(int(4), int(3)),
            BigRational::new(int(3), int(2)),
        )],
    };

    match eval::congruence_keys_equal(
        std::slice::from_ref(&stored),
        std::slice::from_ref(&candidate),
    ) {
        Err(reason) => assert!(reason.contains("algebraic equality across different extensions")),
        other => panic!("selector key equality gap must remain unresolved, got {other:?}"),
    }
}

#[test]
fn selector_graph_equal_cross_extension_arguments_fail_closed() {
    // Make the selector argument itself unevaluable (its array index is
    // unpinned), while supplying the model's committed value for that exact
    // read. This reaches the selector-specific fallback graph. `get` is
    // under-specified on constructor Bad, but it remains a single-valued
    // function: two equal Bad(sqrt(2)) arguments cannot receive 7 and 8.
    let mut ts = TermStore::new();
    let datatype = Sort::Datatype(DatatypeSort::new(
        "Choice",
        vec![
            DatatypeConstructor::new("Good", vec![DatatypeField::new("get", Sort::Int)]),
            DatatypeConstructor::new("Bad", vec![DatatypeField::new("payload", Sort::Real)]),
        ],
    ));
    let array_sort = Sort::array(Sort::Int, datatype.clone());
    let array = ts.mk_var("choices", array_sort);
    let left_index = ts.mk_var("left-index", Sort::Int); // deliberately unpinned
    let right_index = ts.mk_var("right-index", Sort::Int); // deliberately unpinned
    let left_argument = app(&mut ts, "select", &[array, left_index], datatype.clone());
    let right_argument = app(&mut ts, "select", &[array, right_index], datatype);
    let left_selector = app(&mut ts, "get", &[left_argument], Sort::Int);
    let right_selector = app(&mut ts, "get", &[right_argument], Sort::Int);
    let model = UfStubModel::new()
        .sel(
            left_argument,
            ModelValue::Datatype {
                ctor: "Bad".to_string(),
                args: vec![sqrt_two_between(
                    BigRational::from_integer(int(1)),
                    BigRational::from_integer(int(2)),
                )],
            },
        )
        .sel(
            right_argument,
            ModelValue::Datatype {
                ctor: "Bad".to_string(),
                args: vec![sqrt_two_between(
                    BigRational::new(int(4), int(3)),
                    BigRational::new(int(3), int(2)),
                )],
            },
        )
        .uf(left_selector, ModelValue::Int(int(7)))
        .uf(right_selector, ModelValue::Int(int(8)));
    let evaluator = Evaluator::new(&ts, &model);

    assert!(matches!(
        evaluator.evaluate(left_selector),
        EvalOutcome::Value(ModelValue::Int(value)) if value == int(7)
    ));
    assert!(
        matches!(
            evaluator.evaluate(right_selector),
            EvalOutcome::Unevaluable(_)
        ),
        "an unresolved equality with the existing selector key must fail closed"
    );
}

#[test]
fn projection_reuses_outer_value_keyed_uf_graph() {
    // `1` and `(bvadd 0 1)` are the same argument value, so both `g`
    // applications denote one result even though the supplied per-term pins
    // conflict. The projection must evaluate its selected nested application
    // in the existing Evaluator: a fresh evaluator would forget the first
    // `g(1) = #x10`, adopt `g(0+1) = #x20`, and wrongly confirm `distinct`.
    let mut ts = TermStore::new();
    let bv8 = Sort::bitvec(8);
    let zero = ts.mk_bitvec(int(0), 8);
    let one = ts.mk_bitvec(int(1), 8);
    let dummy = ts.mk_bitvec(int(0xaa), 8);
    let equivalent_one = app(&mut ts, "bvadd", &[zero, one], bv8.clone());
    let g_direct = app(&mut ts, "g", &[one], bv8.clone());
    let g_equivalent = app(&mut ts, "g", &[equivalent_one], bv8.clone());
    let projected = app(&mut ts, "projection", &[dummy, g_equivalent], bv8.clone());
    let distinct = app(&mut ts, "distinct", &[g_direct, projected], Sort::Bool);
    let m = UfStubModel::new()
        .uf(g_direct, ModelValue::bitvec(int(0x10), 8))
        .uf(g_equivalent, ModelValue::bitvec(int(0x20), 8))
        .projection(projected, 1);
    assert_violates(&verdict(&ts, &m, &[distinct]));
}

#[test]
fn projection_metadata_is_validated_before_beta_reduction() {
    let mut ts = TermStore::new();
    let one = ts.mk_int(int(1));
    let out_of_bounds = app(&mut ts, "bad_index", &[one], Sort::Int);
    let wrong_sort = app(&mut ts, "bad_sort", &[one], Sort::Bool);
    let m = UfStubModel::new()
        .uf(out_of_bounds, ModelValue::Int(int(9)))
        .uf(wrong_sort, ModelValue::Bool(true))
        .projection(out_of_bounds, 1)
        .projection(wrong_sort, 0);

    match evaluate_term(&ts, &m, out_of_bounds) {
        EvalOutcome::Unevaluable(reason) => assert!(reason.contains("application arity is 1")),
        other => panic!("invalid projection index must fail closed, got {other:?}"),
    }
    match evaluate_term(&ts, &m, wrong_sort) {
        EvalOutcome::Unevaluable(reason) => assert!(reason.contains("does not match result sort")),
        other => panic!("ill-sorted projection must fail closed, got {other:?}"),
    }
}

#[test]
fn projection_lookup_error_precedes_per_application_uf_value() {
    let mut ts = TermStore::new();
    let one = ts.mk_int(int(1));
    let application = app(&mut ts, "conflicting_projection", &[one], Sort::Int);
    let model = UfStubModel::new()
        .uf(application, ModelValue::Int(int(99)))
        .projection_error(application, "installed and observed signatures differ");

    match evaluate_term(&ts, &model, application) {
        EvalOutcome::Unevaluable(reason) => {
            assert!(reason.contains("inconsistent symbolic projection model"));
            assert!(reason.contains("signatures differ"));
        }
        other => panic!("a projection conflict must not fall through to the UF pin, got {other:?}"),
    }
}

#[test]
fn projections_do_not_reset_the_evaluator_depth_budget() {
    let mut ts = TermStore::new();
    let bv8 = Sort::bitvec(8);
    let dummy = ts.mk_bitvec(int(0), 8);
    let mut nested = ts.mk_bitvec(int(1), 8);
    let mut m = UfStubModel::new();
    // Each layer contributes one projection edge and one ordinary interpreted
    // edge. Resetting depth at projection boundaries would evaluate this whole
    // chain; one continuous evaluator must stop once the shared bound is spent.
    for _ in 0..(MAX_EVAL_DEPTH / 2 + 2) {
        let inverted = app(&mut ts, "bvnot", &[nested], bv8.clone());
        nested = app(&mut ts, "depth_projection", &[dummy, inverted], bv8.clone());
        m = m.projection(nested, 1);
    }
    match evaluate_term(&ts, &m, nested) {
        EvalOutcome::Unevaluable(reason) => assert!(reason.contains("recursion depth limit")),
        other => panic!("projection edges must consume the shared depth budget, got {other:?}"),
    }
}

#[test]
fn projection_evaluator_call_depth_is_restored_between_evaluations() {
    let mut ts = TermStore::new();
    let selected = ts.mk_bool(true);
    let dummy = ts.mk_bool(false);
    let projected = app(
        &mut ts,
        "reused_shallow_projection",
        &[dummy, selected],
        Sort::Bool,
    );
    let model = UfStubModel::new().projection(projected, 1);
    let evaluator = Evaluator::new(&ts, &model);

    // This deliberately crosses the projection-specific active-call bound.
    // Every top-level evaluation must restore the counter to zero; a leaked
    // increment would make the 129th call fail closed despite being shallow.
    for attempt in 0..256 {
        assert!(
            matches!(
                evaluator.evaluate(projected),
                EvalOutcome::Value(ModelValue::Bool(true))
            ),
            "shallow projection failed on top-level evaluation {attempt}"
        );
    }
}

#[test]
fn uf_unpinned_application_cannot_confirm() {
    // If the model does not pin an application value, the application is
    // unevaluable and the gate fails closed (never assumed) — CannotConfirm.
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let zero = ts.mk_int(int(0));
    let gt = app(&mut ts, ">", &[f_a, zero], Sort::Bool);
    let m = UfStubModel::new().leaf(a, ModelValue::Int(int(5))); // no uf pin
    assert_cannot(&verdict(&ts, &m, &[gt]));
}

// ===========================================================================
// (e) Array-`select` reads via the model — value-keyed select graph
//
// `select` over an array is a single-valued function of the index. When the
// gate cannot resolve the array operand to a concrete `(default, finite-store)`
// value (a partial / unreconstructable array leaf), it reads the model's
// committed per-read value (`array_select_value`) but keys reads by
// `(array-term, index-value)` and takes the first committed value per key. Two
// reads of the SAME array at index values that evaluate EQUAL therefore resolve
// to one element — exposing (rather than honouring) a model that pins them to
// different values — and, because the gate evaluates indices itself, a
// degenerate array whose reads contradict an asserted (in)equality evaluates the
// assertion to `false`. This is the array analogue of the UF value-keyed graph
// above, closing the array-`select` wrong-model class (#array-select-collapse)
// at the gate even when the theory's array interpretation is unavailable.
// ===========================================================================

/// A stub model that pins scalar leaves and answers `array_select_value` for
/// whole `(select A i)` application terms — but deliberately does NOT pin the
/// array leaf itself, so the gate must go through the `select`-via-model fallback
/// (mirroring the real gate, whose fallback fires exactly when the theory array
/// interpretation cannot be reconstructed).
struct ArraySelectStubModel {
    leaves: HashMap<TermId, ModelValue>,
    selects: HashMap<TermId, ModelValue>,
}

impl ArraySelectStubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            selects: HashMap::new(),
        }
    }
    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
    fn sel(mut self, t: TermId, v: ModelValue) -> Self {
        self.selects.insert(t, v);
        self
    }
}

impl ModelView for ArraySelectStubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
    fn array_select_value(&self, t: TermId) -> Option<ModelValue> {
        self.selects.get(&t).cloned()
    }
}

#[test]
fn array_select_seed21011_distinct_indices_equal_reads_refute() {
    // The seed-21011 shape: `(< (select A0 idx1) (select A0 idx2))` with DISTINCT
    // index values (idx1 = 0, idx2 = -5) that the model reads to the SAME element
    // (both 1). The array leaf A0 is NOT reconstructable (unpinned), so the gate
    // reads each `select` through the model; the two reads key differently
    // (distinct index values) and keep their committed value 1, so `(< 1 1)` is
    // `false` — a caught wrong witness. Pinning that array model into z3 is
    // UNSAT; the gate demotes the `sat` to `unknown`.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort); // deliberately unpinned as a leaf
    let idx1 = ts.mk_int(int(0));
    let idx2 = ts.mk_int(int(-5));
    let sel1 = app(&mut ts, "select", &[a0, idx1], Sort::Int);
    let sel2 = app(&mut ts, "select", &[a0, idx2], Sort::Int);
    let lt = app(&mut ts, "<", &[sel1, sel2], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .sel(sel1, ModelValue::Int(int(1)))
        .sel(sel2, ModelValue::Int(int(1)));
    assert_violates(&verdict(&ts, &m, &[lt]));
}

#[test]
fn array_select_collapsed_indices_refute_strict_inequality() {
    // Collapse analogue of the UF case: two reads of the SAME array A0 at index
    // values that COINCIDE (i = 0 and 3*i = 0) must denote the same element, yet
    // the model pins them to different values (5 and 7). The gate collapses them
    // to one value (first-wins), so `(> read read)` is `false`. Honouring the
    // per-read pins (7 > 5) would confirm an internally-inconsistent array model;
    // the value-keyed graph exposes it instead.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort); // unpinned leaf
    let i = ts.mk_var("i", Sort::Int);
    let three = ts.mk_int(int(3));
    let mul = app(&mut ts, "*", &[three, i], Sort::Int); // 3*i = 0
    let sel_lo = app(&mut ts, "select", &[a0, i], Sort::Int); // A0[i]
    let sel_hi = app(&mut ts, "select", &[a0, mul], Sort::Int); // A0[3*i]
    let gt = app(&mut ts, ">", &[sel_hi, sel_lo], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(i, ModelValue::Int(int(0)))
        .sel(sel_hi, ModelValue::Int(int(7)))
        .sel(sel_lo, ModelValue::Int(int(5)));
    assert_violates(&verdict(&ts, &m, &[gt]));
}

#[test]
fn array_select_equal_cross_extension_indices_fail_closed() {
    // These two exact algebraic index values both denote +sqrt(2), but their
    // root objects use different isolating intervals. After the first read
    // fixes A[sqrt(2)] = 5, an undecidable representation-level comparison at
    // the second read cannot authorize a separate A[sqrt(2)] = 7 entry.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Real, Sort::Int);
    let array = ts.mk_var("A", asort); // deliberately unreconstructable
    let left_index = ts.mk_var("left-index", Sort::Real);
    let right_index = ts.mk_var("right-index", Sort::Real);
    let left_read = app(&mut ts, "select", &[array, left_index], Sort::Int);
    let right_read = app(&mut ts, "select", &[array, right_index], Sort::Int);
    let model = ArraySelectStubModel::new()
        .leaf(
            left_index,
            sqrt_two_between(
                BigRational::from_integer(int(1)),
                BigRational::from_integer(int(2)),
            ),
        )
        .leaf(
            right_index,
            sqrt_two_between(
                BigRational::new(int(4), int(3)),
                BigRational::new(int(3), int(2)),
            ),
        )
        .sel(left_read, ModelValue::Int(int(5)))
        .sel(right_read, ModelValue::Int(int(7)));
    let evaluator = Evaluator::new(&ts, &model);

    assert!(matches!(
        evaluator.evaluate(left_read),
        EvalOutcome::Value(ModelValue::Int(value)) if value == int(5)
    ));
    match evaluator.evaluate(right_read) {
        EvalOutcome::Unevaluable(reason) => {
            assert!(reason.contains("cannot decide congruence-key equality"));
            assert!(reason.contains("algebraic equality across different extensions"));
        }
        other => panic!("ambiguous second array key must fail closed, got {other:?}"),
    }
}

#[test]
fn array_select_via_model_distinct_reads_confirm_valid_model() {
    // NO OVER-REFUTATION: distinct index values (a = 5, b = 7) key the two reads
    // differently, so each keeps its own committed value (A0[a] = 1 > A0[b] = 0)
    // and the witness is CONFIRMED. The select-via-model fallback must not
    // over-refute a genuinely-valid array model.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let sel_a = app(&mut ts, "select", &[a0, a], Sort::Int);
    let sel_b = app(&mut ts, "select", &[a0, b], Sort::Int);
    let gt = app(&mut ts, ">", &[sel_a, sel_b], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(a, ModelValue::Int(int(5)))
        .leaf(b, ModelValue::Int(int(7)))
        .sel(sel_a, ModelValue::Int(int(1)))
        .sel(sel_b, ModelValue::Int(int(0)));
    assert_confirmed(&verdict(&ts, &m, &[gt]));
}

#[test]
fn array_select_coincident_reads_confirm_when_consistent() {
    // NO OVER-REFUTATION under coincidence: two reads of the same array at
    // coinciding index values (i = 0, 3*i = 0) that the model pins CONSISTENTLY
    // (both 4). `(= A0[i] A0[3*i])` is `(= 4 4)` = true — the single-valuedness
    // collapse yields the shared value, not a spurious violation.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let i = ts.mk_var("i", Sort::Int);
    let three = ts.mk_int(int(3));
    let mul = app(&mut ts, "*", &[three, i], Sort::Int);
    let sel_lo = app(&mut ts, "select", &[a0, i], Sort::Int);
    let sel_hi = app(&mut ts, "select", &[a0, mul], Sort::Int);
    let eq = app(&mut ts, "=", &[sel_lo, sel_hi], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(i, ModelValue::Int(int(0)))
        .sel(sel_lo, ModelValue::Int(int(4)))
        .sel(sel_hi, ModelValue::Int(int(4)));
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn array_select_unpinned_read_cannot_confirm() {
    // If neither the array leaf NOR the per-read value is pinned, the `select` is
    // unevaluable and the gate fails closed (never assumed) — CannotConfirm.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let a = ts.mk_var("a", Sort::Int);
    let sel = app(&mut ts, "select", &[a0, a], Sort::Int);
    let zero = ts.mk_int(int(0));
    let gt = app(&mut ts, ">", &[sel, zero], Sort::Bool);
    let m = ArraySelectStubModel::new().leaf(a, ModelValue::Int(int(5))); // no select pin
    assert_cannot(&verdict(&ts, &m, &[gt]));
}

#[test]
fn array_select_reconstructable_leaf_still_uses_structural_path() {
    // When the array leaf IS reconstructable (pinned as a concrete array value),
    // the structural path handles the read and the model's per-read pins are
    // IGNORED — even a contradictory per-read pin cannot override the real array.
    // `(= (select A0 1) 9)` with A0 = const-0 is `(= 0 9)` = false (structural),
    // regardless of a bogus `array_select_value` pin of 9.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let one = ts.mk_int(int(1));
    let nine = ts.mk_int(int(9));
    let sel = app(&mut ts, "select", &[a0, one], Sort::Int);
    let eq = app(&mut ts, "=", &[sel, nine], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(
            a0,
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![],
            })),
        )
        .sel(sel, ModelValue::Int(int(9))); // bogus pin — must be ignored
    assert_violates(&verdict(&ts, &m, &[eq]));
}

#[test]
fn seed21425_shape_emitted_array_model_is_refuted() {
    // Exact seed-21425 shape (arrays fuzz) with the INVALID array model AY
    // emitted (its get-model output pins UNSAT in z3). Given that emitted model
    // as leaf values, the gate's array-`select` evaluation ground-falsifies AY's
    // own assertion — `(= -5 (select A0 -5))` is `(= -5 0)` under the emitted
    // A0 = store(const 0, -3, 2) — and reports ModelViolates. This localizes the
    // (separate, deeper) AUFLIA residual to model RECONSTRUCTION/COMPLETION: the
    // gate's evaluation is correct; the emitted array's default is simply not
    // present in `array_model` at gate time (see report).
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort.clone());
    let a1 = ts.mk_var("A1", asort.clone());
    let a2 = ts.mk_var("A2", asort.clone());
    let i0 = ts.mk_var("i0", Sort::Int);
    let i1 = ts.mk_var("i1", Sort::Int);
    let i2 = ts.mk_var("i2", Sort::Int);
    let i3 = ts.mk_var("i3", Sort::Int);
    let b0 = ts.mk_var("b0", Sort::Bool);
    let n5 = ts.mk_int(int(-5));
    let n3 = ts.mk_int(int(-3));
    let n2 = ts.mk_int(int(-2));
    let two = ts.mk_int(int(2));
    let five = ts.mk_int(int(5));
    let six = ts.mk_int(int(6));
    let c24 = ts.mk_int(int(24));
    let four = ts.mk_int(int(4));
    // D1 = (< (select (store (store A0 -2 (- i1)) 6 i0) (+ i2 6)) (+ i0 (- i3)))
    let neg_i1 = app(&mut ts, "-", &[i1], Sort::Int);
    let s1 = app(&mut ts, "store", &[a0, n2, neg_i1], asort.clone());
    let s2 = app(&mut ts, "store", &[s1, six, i0], asort.clone());
    let i2p6 = app(&mut ts, "+", &[i2, six], Sort::Int);
    let sel_d1 = app(&mut ts, "select", &[s2, i2p6], Sort::Int);
    let neg_i3 = app(&mut ts, "-", &[i3], Sort::Int);
    let i0mi3 = app(&mut ts, "+", &[i0, neg_i3], Sort::Int);
    let d1 = app(&mut ts, "<", &[sel_d1, i0mi3], Sort::Bool);
    // A2eq = (= -5 (select A0 -5))
    let sel_a0m5 = app(&mut ts, "select", &[a0, n5], Sort::Int);
    let a2eq = app(&mut ts, "=", &[n5, sel_a0m5], Sort::Bool);
    // NEQ = (not (= (select A0 -3) (select (store (store A1 6 2) i0 (ite (<= 24 (+ i1 i3)) -3 i0)) i3)))
    let sel_a0m3 = app(&mut ts, "select", &[a0, n3], Sort::Int);
    let a1s1 = app(&mut ts, "store", &[a1, six, two], asort.clone());
    let i1pi3 = app(&mut ts, "+", &[i1, i3], Sort::Int);
    let le = app(&mut ts, "<=", &[c24, i1pi3], Sort::Bool);
    let ite = ts.mk_ite(le, n3, i0);
    let a1s2 = app(&mut ts, "store", &[a1s1, i0, ite], asort.clone());
    let sel_a1 = app(&mut ts, "select", &[a1s2, i3], Sort::Int);
    let eqn = app(&mut ts, "=", &[sel_a0m3, sel_a1], Sort::Bool);
    let neq = ts.mk_not(eqn);
    // C1 = (< (select A2 (+ i2 2)) (select A2 5))
    let i2p2 = app(&mut ts, "+", &[i2, two], Sort::Int);
    let sel_a2a = app(&mut ts, "select", &[a2, i2p2], Sort::Int);
    let sel_a2b = app(&mut ts, "select", &[a2, five], Sort::Int);
    let c1 = app(&mut ts, "<", &[sel_a2a, sel_a2b], Sort::Bool);
    // C2 = (< (select A2 i3) (select A1 4))
    let sel_a2c = app(&mut ts, "select", &[a2, i3], Sort::Int);
    let sel_a1b = app(&mut ts, "select", &[a1, four], Sort::Int);
    let c2 = app(&mut ts, "<", &[sel_a2c, sel_a1b], Sort::Bool);
    let and = app(&mut ts, "and", &[b0, a2eq, neq, c1, c2], Sort::Bool);
    let asrt = app(&mut ts, "or", &[d1, and], Sort::Bool);
    // AY's INVALID emitted model.
    let arr = |d: i64, kv: &[(i64, i64)]| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(d)),
            store: kv
                .iter()
                .map(|(k, v)| (ModelValue::Int(int(*k)), ModelValue::Int(int(*v))))
                .collect(),
        }))
    };
    let m = StubModel::new()
        .with(a0, arr(0, &[(-3, 2)]))
        .with(a1, arr(1, &[(4, 2)]))
        .with(a2, arr(0, &[(7, -1), (-4, 1)]))
        .with(i0, ModelValue::Int(int(-10)))
        .with(i1, ModelValue::Int(int(0)))
        .with(i2, ModelValue::Int(int(5)))
        .with(i3, ModelValue::Int(int(-4)))
        .with(b0, ModelValue::Bool(true));
    assert_violates(&verdict(&ts, &m, &[asrt]));
}

// ===========================================================================
// (d) The model-INDEPENDENT datatype-congruence NORMALIZER
//     (`is_datatype_tautology_with`): it must PROVE genuine free-datatype
//     tautologies AND REJECT every near-miss non-tautology (soundness).
// ===========================================================================

/// `Option`-like datatype: `None` (nullary) + `Some(value: Int)`.
fn option_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "Opt",
        vec![
            DatatypeConstructor::new("None", vec![]),
            DatatypeConstructor::new("Some", vec![DatatypeField::new("value", Sort::Int)]),
        ],
    ))
}

/// Single-constructor datatype `Box = Mk(fst: Int, snd: Int)`.
fn box_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "Box",
        vec![DatatypeConstructor::new(
            "Mk",
            vec![
                DatatypeField::new("fst", Sort::Int),
                DatatypeField::new("snd", Sort::Int),
            ],
        )],
    ))
}

fn is_taut(ts: &TermStore, t: TermId) -> bool {
    is_datatype_tautology_with(ts, t, &|_| None)
}

#[test]
fn norm_proves_constructor_characterization() {
    // (= (= (Some v) x) (and (is-Some x) (= v (value x)))) — a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let v = ts.mk_var("v", Sort::Int);
    let some_v = app(&mut ts, "Some", &[v], opt.clone());
    let inner = app(&mut ts, "=", &[some_v, x], Sort::Bool);
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let value_x = app(&mut ts, "value", &[x], Sort::Int);
    let feq = app(&mut ts, "=", &[v, value_x], Sort::Bool);
    let conj = app(&mut ts, "and", &[is_some, feq], Sort::Bool);
    let bicond = app(&mut ts, "=", &[inner, conj], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "constructor characterization must be proved"
    );
}

#[test]
fn norm_proves_is_ctor_roundtrip_and_sole_ctor() {
    // (= (is-Mk x) (= x (Mk (fst x) (snd x)))) — round-trip, sole ctor.
    let mut ts = TermStore::new();
    let bx = box_sort();
    let x = ts.mk_var("x", bx.clone());
    let is_mk = app(&mut ts, "is-Mk", &[x], Sort::Bool);
    let fst = app(&mut ts, "fst", &[x], Sort::Int);
    let snd = app(&mut ts, "snd", &[x], Sort::Int);
    let mk = app(&mut ts, "Mk", &[fst, snd], bx.clone());
    let eq = app(&mut ts, "=", &[x, mk], Sort::Bool);
    let bicond = app(&mut ts, "=", &[is_mk, eq], Sort::Bool);
    assert!(is_taut(&ts, bicond), "is-C round-trip must be proved");

    // Sole-constructor tester is a tautology: (is-Mk x).
    assert!(is_taut(&ts, is_mk), "sole-ctor tester must be proved");
}

#[test]
fn norm_proves_nullary_and_none_equality() {
    // None is nullary: (is-None None), (not (is-Some None)),
    // (= (= None x) (is-None x)).
    let mut ts = TermStore::new();
    let opt = option_sort();
    let none = ts.mk_var("None", opt.clone()); // front-end lowering of `(None)`
    let x = ts.mk_var("x", opt.clone());
    let is_none_none = app(&mut ts, "is-None", &[none], Sort::Bool);
    assert!(is_taut(&ts, is_none_none), "is-None(None) must be proved");

    let is_some_none = app(&mut ts, "is-Some", &[none], Sort::Bool);
    let not_is_some = app(&mut ts, "not", &[is_some_none], Sort::Bool);
    assert!(
        is_taut(&ts, not_is_some),
        "(not is-Some(None)) must be proved"
    );

    let none_eq_x = app(&mut ts, "=", &[none, x], Sort::Bool);
    let is_none_x = app(&mut ts, "is-None", &[x], Sort::Bool);
    let bicond = app(&mut ts, "=", &[none_eq_x, is_none_x], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "(= (= None x)(is-None x)) must be proved"
    );
}

#[test]
fn norm_rejects_missing_field_characterization() {
    // SOUNDNESS near-miss: DROP the field equality.
    // (= (= (Some v) x) (is-Some x)) is NOT a tautology (needs v = value x).
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let v = ts.mk_var("v", Sort::Int);
    let some_v = app(&mut ts, "Some", &[v], opt.clone());
    let inner = app(&mut ts, "=", &[some_v, x], Sort::Bool);
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let bad = app(&mut ts, "=", &[inner, is_some], Sort::Bool);
    assert!(
        !is_taut(&ts, bad),
        "dropping the field eq must NOT be proved (unsound)"
    );
}

#[test]
fn norm_rejects_wrong_field_and_bare_constructor_eq() {
    // (= (= (Some a) x) (and (is-Some x) (= b (value x)))) with a != b: NOT valid.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let some_a = app(&mut ts, "Some", &[a], opt.clone());
    let inner = app(&mut ts, "=", &[some_a, x], Sort::Bool);
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let value_x = app(&mut ts, "value", &[x], Sort::Int);
    let feq_b = app(&mut ts, "=", &[b, value_x], Sort::Bool);
    let conj = app(&mut ts, "and", &[is_some, feq_b], Sort::Bool);
    let bad = app(&mut ts, "=", &[inner, conj], Sort::Bool);
    assert!(
        !is_taut(&ts, bad),
        "wrong field var must NOT be proved (unsound)"
    );

    // Bare (= (Some a) x) is NOT a tautology.
    assert!(
        !is_taut(&ts, inner),
        "bare constructor eq must NOT be proved"
    );

    // Injectivity is NOT vacuous: (= (Some a)(Some b)) is NOT a tautology.
    let some_b = app(&mut ts, "Some", &[b], opt.clone());
    let inj = app(&mut ts, "=", &[some_a, some_b], Sort::Bool);
    assert!(
        !is_taut(&ts, inj),
        "(= (Some a)(Some b)) must NOT be proved"
    );
}

#[test]
fn norm_rejects_two_ctor_tester_and_distinctness_confusion() {
    // (is-Some x) for the 2-ctor Opt with x free: NOT a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    assert!(
        !is_taut(&ts, is_some),
        "2-ctor tester on free var must NOT be proved"
    );

    // (= (Some a) None) reduces to false; asserting it is NOT a tautology,
    // but its NEGATION is: (not (= (Some a) None)).
    let a = ts.mk_var("a", Sort::Int);
    let some_a = app(&mut ts, "Some", &[a], opt.clone());
    let none = ts.mk_var("None", opt.clone());
    let eq = app(&mut ts, "=", &[some_a, none], Sort::Bool);
    assert!(
        !is_taut(&ts, eq),
        "(= (Some a) None) must NOT be proved true"
    );
    let neg = app(&mut ts, "not", &[eq], Sort::Bool);
    assert!(
        is_taut(&ts, neg),
        "distinct constructors: negation IS a tautology"
    );
}

#[test]
fn norm_proves_injectivity_biconditional() {
    // (= (= (Some a) (Some b)) (= a b)) — injectivity, a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let some_a = app(&mut ts, "Some", &[a], opt.clone());
    let some_b = app(&mut ts, "Some", &[b], opt.clone());
    let lhs = app(&mut ts, "=", &[some_a, some_b], Sort::Bool);
    let rhs = app(&mut ts, "=", &[a, b], Sort::Bool);
    let bicond = app(&mut ts, "=", &[lhs, rhs], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "injectivity biconditional must be proved"
    );
}

#[test]
fn norm_proves_nested_datatype_field_characterization() {
    // Mirrors g4: PbConstraint_mk(fld_terms: Vec, ...) where Vec is itself a
    // single-ctor datatype. The congruence axiom over a NESTED constructor field
    // must characterize recursively through the selector path.
    let mut ts = TermStore::new();
    let vec_s = Sort::Datatype(DatatypeSort::new(
        "Vec",
        vec![DatatypeConstructor::new(
            "Vmk",
            vec![DatatypeField::new("data", Sort::Int)],
        )],
    ));
    let pc = Sort::Datatype(DatatypeSort::new(
        "PC",
        vec![DatatypeConstructor::new(
            "Pmk",
            vec![
                DatatypeField::new("terms", vec_s.clone()),
                DatatypeField::new("rhs", Sort::Int),
            ],
        )],
    ));
    let x = ts.mk_var("x", pc.clone());
    let d = ts.mk_var("d", Sort::Int);
    let rhs = ts.mk_var("rhs", Sort::Int);
    let vmk = app(&mut ts, "Vmk", &[d], vec_s.clone());
    let pmk = app(&mut ts, "Pmk", &[vmk, rhs], pc.clone());
    let inner = app(&mut ts, "=", &[pmk, x], Sort::Bool);
    // RHS: (and (is-Pmk x) (= (Vmk d) (terms x)) (= rhs (rhs x)))
    let is_pmk = app(&mut ts, "is-Pmk", &[x], Sort::Bool);
    let terms_x = app(&mut ts, "terms", &[x], vec_s.clone());
    let vmk2 = app(&mut ts, "Vmk", &[d], vec_s.clone());
    let eq_terms = app(&mut ts, "=", &[vmk2, terms_x], Sort::Bool);
    let rhs_x = app(&mut ts, "rhs", &[x], Sort::Int);
    let eq_rhs = app(&mut ts, "=", &[rhs, rhs_x], Sort::Bool);
    let conj = app(&mut ts, "and", &[is_pmk, eq_terms, eq_rhs], Sort::Bool);
    let bicond = app(&mut ts, "=", &[inner, conj], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "nested-field constructor characterization must be proved"
    );

    // SOUNDNESS near-miss: swap the nested field var d -> e (e != d).
    let e = ts.mk_var("e", Sort::Int);
    let vmk_e = app(&mut ts, "Vmk", &[e], vec_s.clone());
    let eq_terms_bad = app(&mut ts, "=", &[vmk_e, terms_x], Sort::Bool);
    let conj_bad = app(&mut ts, "and", &[is_pmk, eq_terms_bad, eq_rhs], Sort::Bool);
    let bad = app(&mut ts, "=", &[inner, conj_bad], Sort::Bool);
    assert!(
        !is_taut(&ts, bad),
        "mismatched nested field must NOT be proved (unsound)"
    );
}

#[test]
fn norm_proves_structural_equality_characterization_two_ctor() {
    // (= (= None x) (and (= (is-None x)(is-None None)) (= (is-Some x)(is-Some None))
    //                    (or (not (is-Some None)) (= (value x)(value None)))))
    // — the full 2-ctor structural-equality axiom; a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let none = ts.mk_var("None", opt.clone());
    let x = ts.mk_var("x", opt.clone());
    let none_eq_x = app(&mut ts, "=", &[none, x], Sort::Bool);
    let isn_x = app(&mut ts, "is-None", &[x], Sort::Bool);
    let isn_n = app(&mut ts, "is-None", &[none], Sort::Bool);
    let e1 = app(&mut ts, "=", &[isn_x, isn_n], Sort::Bool);
    let iss_x = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let iss_n = app(&mut ts, "is-Some", &[none], Sort::Bool);
    let e2 = app(&mut ts, "=", &[iss_x, iss_n], Sort::Bool);
    let not_iss_n = app(&mut ts, "not", &[iss_n], Sort::Bool);
    let val_x = app(&mut ts, "value", &[x], Sort::Int);
    let val_n = app(&mut ts, "value", &[none], Sort::Int);
    let e3v = app(&mut ts, "=", &[val_x, val_n], Sort::Bool);
    let e3 = app(&mut ts, "or", &[not_iss_n, e3v], Sort::Bool);
    let big = app(&mut ts, "and", &[e1, e2, e3], Sort::Bool);
    let bicond = app(&mut ts, "=", &[none_eq_x, big], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "2-ctor structural-eq characterization must be proved"
    );
}

#[test]
fn norm_two_ctor_exclusivity_is_not_overreaching() {
    // SOUNDNESS: is-None(x) alone is NOT a tautology; nor is is-Some(x); nor their
    // conjunction; but their disjunction IS (exhaustiveness).
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let isn = app(&mut ts, "is-None", &[x], Sort::Bool);
    let iss = app(&mut ts, "is-Some", &[x], Sort::Bool);
    assert!(!is_taut(&ts, isn), "is-None(x) must NOT be a tautology");
    assert!(!is_taut(&ts, iss), "is-Some(x) must NOT be a tautology");
    let conj = app(&mut ts, "and", &[isn, iss], Sort::Bool);
    assert!(
        !is_taut(&ts, conj),
        "is-None ∧ is-Some must NOT be a tautology"
    );
    let disj = app(&mut ts, "or", &[isn, iss], Sort::Bool);
    assert!(
        is_taut(&ts, disj),
        "is-None ∨ is-Some IS a tautology (exhaustive)"
    );
}

// ===========================================================================
// (e) Residual free-datatype-array joint-satisfiability
//     (#free-dt-array-residual): a residue consisting ONLY of alias
//     equalities and ground element reads over FREE datatype-element arrays
//     confirms iff no two constraints force different values at one
//     (class, index, field) slot. Everything else stays fail-closed.
// ===========================================================================

/// Datatype `S = mk(f: Int, g: Int)` and its array sort `(Array Int S)`.
fn struct_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "S",
        vec![DatatypeConstructor::new(
            "mk",
            vec![
                DatatypeField::new("f", Sort::Int),
                DatatypeField::new("g", Sort::Int),
            ],
        )],
    ))
}

/// `(= <ground-int> (fld (select arr idx)))` — a field read over `arr`.
fn field_read_eq(
    ts: &mut TermStore,
    fld: &str,
    arr: TermId,
    idx: TermId,
    ground: TermId,
) -> TermId {
    let sel = app(ts, "select", &[arr, idx], struct_sort());
    let prj = app(ts, fld, &[sel], Sort::Int);
    app(ts, "=", &[ground, prj], Sort::Bool)
}

#[test]
fn residual_free_dt_array_alias_with_consistent_reads_confirms() {
    // Free a, b : (Array Int S); (= a b); f(a[0]) = 5, g(b[0]) = 7,
    // f(b[0]) = 5 (duplicate, consistent), f(a[1]) = 6 (distinct index).
    // Jointly satisfiable: a = b = [0 -> mk(5,7), 1 -> mk(6,_)] extends the
    // partial model, so the gate must CONFIRM instead of failing closed.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let i1 = ts.mk_int(int(1));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let c7 = ts.mk_int(int(7));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    let r2 = field_read_eq(&mut ts, "g", b, i0, c7);
    let r3 = field_read_eq(&mut ts, "f", b, i0, c5);
    let r4 = field_read_eq(&mut ts, "f", a, i1, c6);
    let m = StubModel::new();
    assert_confirmed(&verdict(&ts, &m, &[alias, r1, r2, r3, r4]));
}

#[test]
fn residual_free_dt_array_conflicting_reads_stay_unknown() {
    // Same shape but f(a[0]) = 5 vs f(b[0]) = 6 with a = b: two constraints
    // force different values at ONE (class, index, field) slot — the residue
    // is NOT jointly satisfiable, so the gate must keep failing closed.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    let r2 = field_read_eq(&mut ts, "f", b, i0, c6);
    let m = StubModel::new();
    assert_cannot(&verdict(&ts, &m, &[alias, r1, r2]));
}

#[test]
fn residual_free_dt_array_symbolic_index_evaluated_under_model() {
    // The read index is a VARIABLE the model pins: i = 0 makes f(a[i]) = 5
    // collide with f(b[0]) = 6 under a = b ⇒ CannotConfirm. With i = 1 the
    // keys are distinct ⇒ ConfirmedSat. (Indices are evaluated, not
    // syntactically compared.)
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i = ts.mk_var("i", Sort::Int);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i, c5);
    let r2 = field_read_eq(&mut ts, "f", b, i0, c6);
    let colliding = StubModel::new().with(i, ModelValue::Int(int(0)));
    assert_cannot(&verdict(&ts, &colliding, &[alias, r1, r2]));
    let disjoint = StubModel::new().with(i, ModelValue::Int(int(1)));
    assert_confirmed(&verdict(&ts, &disjoint, &[alias, r1, r2]));
}

#[test]
fn residual_free_dt_array_whole_element_reads() {
    // Whole-element requirements: (= (select a 0) (mk 1 2)) twice through the
    // alias is consistent ⇒ ConfirmedSat; against (mk 3 4) ⇒ CannotConfirm.
    let mut ts = TermStore::new();
    let ssort = struct_sort();
    let asort = Sort::array(Sort::Int, ssort.clone());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let c1 = ts.mk_int(int(1));
    let c2 = ts.mk_int(int(2));
    let c3 = ts.mk_int(int(3));
    let c4 = ts.mk_int(int(4));
    let mk12 = app(&mut ts, "mk", &[c1, c2], ssort.clone());
    let mk34 = app(&mut ts, "mk", &[c3, c4], ssort.clone());
    let sel_a = app(&mut ts, "select", &[a, i0], ssort.clone());
    let sel_b = app(&mut ts, "select", &[b, i0], ssort);
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let w1 = app(&mut ts, "=", &[sel_a, mk12], Sort::Bool);
    let w2_ok = app(&mut ts, "=", &[sel_b, mk12], Sort::Bool);
    let w2_bad = app(&mut ts, "=", &[sel_b, mk34], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[alias, w1, w2_ok]));
    assert_cannot(&verdict(&ts, &StubModel::new(), &[alias, w1, w2_bad]));
}

#[test]
fn residual_free_dt_array_disequality_stays_unknown() {
    // A DISEQUALITY between free arrays is outside the decided fragment
    // (hard constraint: only eq-alias + element-read shapes) ⇒ CannotConfirm,
    // even though it is trivially satisfiable.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort.clone());
    let c = ts.mk_var("c", asort);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let eq_bc = app(&mut ts, "=", &[b, c], Sort::Bool);
    let diseq = app(&mut ts, "not", &[eq_bc], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[alias, diseq, r1]));
}

#[test]
fn residual_free_dt_array_store_context_stays_unknown() {
    // A free class member occurring inside a `store` is outside the fragment
    // (the store could constrain the array beyond element reads) ⇒ refuse.
    let mut ts = TermStore::new();
    let ssort = struct_sort();
    let asort = Sort::array(Sort::Int, ssort.clone());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort.clone());
    let i0 = ts.mk_int(int(0));
    let c1 = ts.mk_int(int(1));
    let c2 = ts.mk_int(int(2));
    let c5 = ts.mk_int(int(5));
    let mk12 = app(&mut ts, "mk", &[c1, c2], ssort);
    let stored = app(&mut ts, "store", &[a, i0, mk12], asort);
    let eq_store = app(&mut ts, "=", &[b, stored], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq_store, r1]));
}

#[test]
fn residual_free_dt_array_guarded_alias_confirms() {
    // The model-checker-consumer VC shape: the alias sits under an `or` whose other
    // disjunct concretely evaluates FALSE — `(or (not (= x 1)) (= a b))`
    // with x = 1. The guard's value is preserved by the extension, so the
    // alias is still forced and the decision applies.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let x = ts.mk_var("x", Sort::Int);
    let i0 = ts.mk_int(int(0));
    let c1 = ts.mk_int(int(1));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let eq_x1 = app(&mut ts, "=", &[x, c1], Sort::Bool);
    let not_x1 = app(&mut ts, "not", &[eq_x1], Sort::Bool);
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let guarded = app(&mut ts, "or", &[not_x1, alias], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    let r2 = field_read_eq(&mut ts, "f", b, i0, c5);
    let r2_bad = field_read_eq(&mut ts, "f", b, i0, c6);
    let m = || StubModel::new().with(x, ModelValue::Int(int(1)));
    assert_confirmed(&verdict(&ts, &m(), &[guarded, r1, r2]));
    // The guarded alias still JOINS the classes: conflicting reads refuse.
    assert_cannot(&verdict(&ts, &m(), &[guarded, r1, r2_bad]));
}

#[test]
fn residual_free_dt_array_unpinned_scalar_side_stays_unknown() {
    // The ground side of an element read must EVALUATE under the fixed
    // partial model; an unpinned scalar keeps the fail-closed verdict.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort);
    let y = ts.mk_var("y", Sort::Int);
    let i0 = ts.mk_int(int(0));
    let r1 = field_read_eq(&mut ts, "f", a, i0, y);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[r1]));
}

#[test]
fn residual_free_dt_array_pinned_member_not_free() {
    // An "alias" whose side the model PINS is not the free fragment: the
    // pinned side resolves, the equality constrains the free side to a
    // committed value — exactly what the decision must NOT adjudicate.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", b, i0, c5);
    let m = StubModel::new().with(
        a,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Datatype {
                ctor: "mk".to_string(),
                args: vec![ModelValue::Int(int(9)), ModelValue::Int(int(9))],
            },
            store: vec![],
        })),
    );
    assert_cannot(&verdict(&ts, &m, &[alias, r1]));
}

#[test]
fn residual_free_dt_array_whole_plus_field_mix_projects_exactly() {
    // Whole-element AND field requirements at ONE (class, index) reconcile by
    // EXACT constructor projection: f(mk(1,2)) = 1 is consistent ⇒ confirmed;
    // f(mk(1,2)) = 3 contradicts ⇒ fail closed.
    let mut ts = TermStore::new();
    let ssort = struct_sort();
    let asort = Sort::array(Sort::Int, ssort.clone());
    let a = ts.mk_var("a", asort);
    let i0 = ts.mk_int(int(0));
    let c1 = ts.mk_int(int(1));
    let c2 = ts.mk_int(int(2));
    let c3 = ts.mk_int(int(3));
    let mk12 = app(&mut ts, "mk", &[c1, c2], ssort.clone());
    let sel_a = app(&mut ts, "select", &[a, i0], ssort);
    let w1 = app(&mut ts, "=", &[sel_a, mk12], Sort::Bool);
    let r_ok = field_read_eq(&mut ts, "f", a, i0, c1);
    let r_bad = field_read_eq(&mut ts, "f", a, i0, c3);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[w1, r_ok]));
    assert_cannot(&verdict(&ts, &StubModel::new(), &[w1, r_bad]));
}

#[test]
fn residual_reads_only_no_alias_confirms() {
    // Singleton classes (no alias equalities at all) are decided too:
    // consistent reads at distinct indices over ONE free array confirm.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort);
    let i0 = ts.mk_int(int(0));
    let i1 = ts.mk_int(int(1));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    let r2 = field_read_eq(&mut ts, "f", a, i1, c6);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[r1, r2]));
}

#[test]
fn residual_non_dt_element_array_stays_unknown() {
    // The decision is scoped to DATATYPE-element arrays: a free Int-element
    // array read keeps today's fail-closed behaviour.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let sel = app(&mut ts, "select", &[a, i0], Sort::Int);
    let r1 = app(&mut ts, "=", &[c5, sel], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[alias, r1]));
}

// --- seq.last_indexof / seq.replace_all value-level parity (#p0.1-seq) ------
//
// These VALUE-level tests pin the independent-gate evaluator's semantics for
// `seq.last_indexof` and `seq.replace_all` against HAND-COMPUTED SMT-LIB
// results. z3 4.15.4 is deliberately NOT used as the oracle here: it does not
// recognise `seq.replace_all` at all ("unknown constant") and it computes
// WRONG `seq.last_indexof` values (its rightmost-of-[5,5] for [5] is neither 0
// nor 1). The gate must therefore be validated against the specification, and
// its implementation is kept independent of the solver's own evaluator
// (crate::seq uses `match_at`; the solver uses inline loops) so a shared bug
// cannot mutually confirm a wrong `sat`.

fn mvseq_i(xs: &[i64]) -> ModelValue {
    ModelValue::Seq(xs.iter().map(|&n| ModelValue::Int(int(n))).collect())
}

fn li(s: &[i64], sub: &[i64]) -> BigInt {
    match seq::eval("seq.last_indexof", &[mvseq_i(s), mvseq_i(sub)]).unwrap() {
        ModelValue::Int(n) => n,
        other => panic!("expected Int, got {other:?}"),
    }
}

fn ra(s: &[i64], src: &[i64], dst: &[i64]) -> Vec<i64> {
    match seq::eval("seq.replace_all", &[mvseq_i(s), mvseq_i(src), mvseq_i(dst)]).unwrap() {
        ModelValue::Seq(v) => v
            .into_iter()
            .map(|e| match e {
                ModelValue::Int(n) => n.try_into().unwrap(),
                other => panic!("expected Int element, got {other:?}"),
            })
            .collect(),
        other => panic!("expected Seq, got {other:?}"),
    }
}

#[test]
fn seq_last_indexof_semantics() {
    assert_eq!(li(&[5, 5, 5], &[5]), int(2)); // rightmost tie
    assert_eq!(li(&[5, 5], &[5]), int(1)); // z3-4.15.4 gets THIS wrong
    assert_eq!(li(&[9, 1, 2], &[9]), int(0)); // single leftmost occurrence
    assert_eq!(li(&[5, 6], &[9]), int(-1)); // not found
    assert_eq!(li(&[5, 6, 7], &[]), int(3)); // empty needle -> |s|
    assert_eq!(li(&[], &[]), int(0)); // empty haystack + empty needle
    assert_eq!(li(&[1], &[1, 1]), int(-1)); // needle longer than haystack
    assert_eq!(li(&[1, 1, 1], &[1, 1]), int(1)); // rightmost multi-element match
}

// ---------------------------------------------------------------------------
// Higher-order combinators (#ho-seq).
//
// The function operand is a FUNCTION-AS-ARRAY, curried exactly as
// `Z3_mk_seq_map` / `Z3_mk_seq_foldl` build it. Before these, the gate reported
// `unsupported sequence operator seq.map` for EVERY assertion mentioning one,
// so a genuine `sat` over a ground `seq.map` could never be confirmed and
// always degraded to `unknown`. Values are hand-computed from the combinator
// definitions; the fail-closed corners (non-array function operand, an
// unevaluable curried layer) are pinned alongside.

/// An `(Array Int Int)` value from explicit `index -> value` pins.
fn mvarr_i(default: i64, pins: &[(i64, i64)]) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Int(int(default)),
        store: pins
            .iter()
            .map(|&(k, v)| (ModelValue::Int(int(k)), ModelValue::Int(int(v))))
            .collect(),
    }))
}

/// An `(Array Int (Array Int Int))` value from a default inner array plus pins.
fn mvarr2_i(default_inner: ModelValue, pins: &[(i64, ModelValue)]) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: default_inner,
        store: pins
            .iter()
            .map(|(k, v)| (ModelValue::Int(int(*k)), v.clone()))
            .collect(),
    }))
}

fn int_of(value: &ModelValue) -> BigInt {
    match value {
        ModelValue::Int(n) => n.clone(),
        other => panic!("expected Int, got {other:?}"),
    }
}

fn ints_of(value: &ModelValue) -> Vec<i64> {
    match value {
        ModelValue::Seq(v) => v
            .iter()
            .map(|e| match e {
                ModelValue::Int(n) => n.try_into().unwrap(),
                other => panic!("expected Int element, got {other:?}"),
            })
            .collect(),
        other => panic!("expected Seq, got {other:?}"),
    }
}

#[test]
fn seq_map_applies_the_function_as_array_pointwise() {
    let f = mvarr_i(0, &[(1, 3), (2, 4)]);
    let mapped = seq::eval("seq.map", &[f.clone(), mvseq_i(&[1, 2])]).unwrap();
    assert_eq!(ints_of(&mapped), vec![3, 4]);
    // The default covers indices with no pin.
    let mapped = seq::eval("seq.map", &[f, mvseq_i(&[1, 7])]).unwrap();
    assert_eq!(ints_of(&mapped), vec![3, 0]);
    // Length is preserved, so the empty sequence maps to the empty sequence.
    let empty = seq::eval("seq.map", &[mvarr_i(5, &[]), mvseq_i(&[])]).unwrap();
    assert_eq!(ints_of(&empty), Vec::<i64>::new());
    // A non-array function operand is unevaluable, never a guessed value.
    assert!(seq::eval("seq.map", &[ModelValue::Int(int(1)), mvseq_i(&[1])]).is_err());
}

#[test]
fn seq_mapi_curries_the_index_outermost() {
    // f[i][e]: at index 0 add 10, at index 1 add 20.
    let f = mvarr2_i(
        mvarr_i(0, &[]),
        &[(0, mvarr_i(0, &[(5, 15)])), (1, mvarr_i(0, &[(6, 26)]))],
    );
    let mapped = seq::eval(
        "seq.mapi",
        &[f.clone(), ModelValue::Int(int(0)), mvseq_i(&[5, 6])],
    )
    .unwrap();
    assert_eq!(ints_of(&mapped), vec![15, 26]);
    // The index operand is the BASE, so it offsets every element position.
    let shifted = seq::eval("seq.mapi", &[f, ModelValue::Int(int(1)), mvseq_i(&[6])]).unwrap();
    assert_eq!(ints_of(&shifted), vec![26]);
}

#[test]
fn seq_foldl_chains_the_accumulator_outermost() {
    // f[acc][e] = acc + e, pinned over exactly the reachable pairs.
    let f = mvarr2_i(
        mvarr_i(0, &[]),
        &[
            (0, mvarr_i(0, &[(1, 1), (2, 2)])),
            (1, mvarr_i(0, &[(2, 3)])),
            (3, mvarr_i(0, &[(4, 7)])),
        ],
    );
    let folded = seq::eval(
        "seq.foldl",
        &[f.clone(), ModelValue::Int(int(0)), mvseq_i(&[1, 2, 4])],
    )
    .unwrap();
    assert_eq!(int_of(&folded), int(7));
    // Over the EMPTY sequence the fold IS the accumulator — `f` is never
    // applied, so it need not even be well-shaped beyond being an array.
    let identity = seq::eval("seq.foldl", &[f, ModelValue::Int(int(42)), mvseq_i(&[])]).unwrap();
    assert_eq!(int_of(&identity), int(42));
    // A curried layer that is not an array fails closed.
    assert!(seq::eval(
        "seq.foldl",
        &[
            mvarr_i(0, &[(0, 9)]),
            ModelValue::Int(int(0)),
            mvseq_i(&[1])
        ],
    )
    .is_err());
}

#[test]
fn seq_foldli_chains_index_then_accumulator() {
    // f[i][acc][e]: only the (i=0, acc=0, e=5) and (i=1, acc=5, e=6) steps.
    let inner0 = mvarr2_i(mvarr_i(0, &[]), &[(0, mvarr_i(0, &[(5, 5)]))]);
    let inner1 = mvarr2_i(mvarr_i(0, &[]), &[(5, mvarr_i(0, &[(6, 11)]))]);
    let f = ModelValue::Array(Box::new(ArrayValue {
        default: inner0.clone(),
        store: vec![
            (ModelValue::Int(int(0)), inner0),
            (ModelValue::Int(int(1)), inner1),
        ],
    }));
    let folded = seq::eval(
        "seq.foldli",
        &[
            f,
            ModelValue::Int(int(0)),
            ModelValue::Int(int(0)),
            mvseq_i(&[5, 6]),
        ],
    )
    .unwrap();
    assert_eq!(int_of(&folded), int(11));
}

#[test]
fn seq_replace_all_semantics() {
    assert_eq!(ra(&[1, 2, 1], &[1], &[9]), vec![9, 2, 9]); // both occurrences
    assert_eq!(ra(&[1, 1, 1], &[1, 1], &[0]), vec![0, 1]); // non-overlapping l-to-r
    assert_eq!(ra(&[1, 2], &[], &[9]), vec![1, 2]); // empty src -> unchanged
    assert_eq!(ra(&[1, 2], &[3], &[9]), vec![1, 2]); // not found -> unchanged
    assert_eq!(ra(&[1, 2], &[1], &[8, 8]), vec![8, 8, 2]); // expanding dst
    assert_eq!(ra(&[1, 2, 1], &[1], &[]), vec![2]); // deleting dst
    assert_eq!(ra(&[1, 1], &[1, 1], &[9]), vec![9]); // whole-sequence match
}

// ===========================================================================
// str.replace_re / str.replace_re_all
//
// SMT-LIB 2.6 Unicode Strings decomposes `s = x ++ w ++ z` with `w` in `[[r]]`,
// `|x|` minimal and THEN `|w|` minimal (leftmost, then shortest).
// `str.replace_re` rewrites that one occurrence; `str.replace_re_all` recurses
// on `z`, under the extra `w != ""` side condition. A regex that accepts the
// empty word is where the two clauses come apart, and this gate deliberately
// fails closed there — see `crate::regex::replace`.
//
// Every case below is fully ground, so the verdict is decided entirely by this
// crate's evaluator and its own interval matcher.
// ===========================================================================

fn re_lit(ts: &mut TermStore, text: &str) -> TermId {
    let s = ts.mk_string(text.to_string());
    app(ts, "str.to_re", &[s], Sort::RegLan)
}

fn re_range(ts: &mut TermStore, lo: &str, hi: &str) -> TermId {
    let lo = ts.mk_string(lo.to_string());
    let hi = ts.mk_string(hi.to_string());
    app(ts, "re.range", &[lo, hi], Sort::RegLan)
}

/// Gate `(= (<op> <subject> <regex> <replacement>) <expected>)`.
fn replace_re_verdict(
    op: &str,
    build_regex: impl FnOnce(&mut TermStore) -> TermId,
    subject: &str,
    replacement: &str,
    expected: &str,
) -> GateVerdict {
    let mut ts = TermStore::new();
    let regex = build_regex(&mut ts);
    let s = ts.mk_string(subject.to_string());
    let t = ts.mk_string(replacement.to_string());
    let call = app(&mut ts, op, &[s, regex, t], Sort::String);
    let want = ts.mk_string(expected.to_string());
    let eq = app(&mut ts, "=", &[call, want], Sort::Bool);
    verdict(&ts, &StubModel::new(), &[eq])
}

// ── the shape the group_strings regression exercised: a union pattern ──

#[test]
fn replace_re_union_replaces_the_leftmost_match() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let a = re_lit(ts, "a");
            let b = re_lit(ts, "b");
            app(ts, "re.union", &[a, b], Sort::RegLan)
        },
        "abc",
        "X",
        "Xbc",
    ));
}

#[test]
fn replace_re_union_skips_to_the_first_position_that_matches() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let one = re_lit(ts, "1");
            let two = re_lit(ts, "2");
            app(ts, "re.union", &[one, two], Sort::RegLan)
        },
        "a1b2c",
        "X",
        "aXb2c",
    ));
}

#[test]
fn replace_re_all_union_replaces_every_match() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| {
            let one = re_lit(ts, "1");
            let two = re_lit(ts, "2");
            app(ts, "re.union", &[one, two], Sort::RegLan)
        },
        "a1b2c",
        "X",
        "aXbXc",
    ));
}

// ── the two halves of "leftmost, THEN shortest" ──

#[test]
fn replace_re_takes_the_shortest_match_at_the_leftmost_position() {
    // `(re.union (str.to_re "ab") (str.to_re "a"))` matches both "ab" and "a"
    // at position 0. The clause minimizes |w| there, so "a" is replaced and
    // "bc" survives. A longest-match (PCRE-style greedy) reading would yield
    // "Xc" instead.
    let build = |ts: &mut TermStore| {
        let ab = re_lit(ts, "ab");
        let a = re_lit(ts, "a");
        app(ts, "re.union", &[ab, a], Sort::RegLan)
    };
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        build,
        "abc",
        "X",
        "Xbc",
    ));
    assert_violates(&replace_re_verdict(
        "str.replace_re",
        build,
        "abc",
        "X",
        "Xc",
    ));
}

#[test]
fn replace_re_prefers_a_leftmost_long_match_over_a_later_short_one() {
    // In "xab" the union matches "ab" at 1 and "b" at 2. `|x|` is minimized
    // FIRST, so the length-2 match at position 1 wins over the length-1 match
    // at position 2 — shortness only breaks ties within one position.
    let build = |ts: &mut TermStore| {
        let ab = re_lit(ts, "ab");
        let b = re_lit(ts, "b");
        app(ts, "re.union", &[ab, b], Sort::RegLan)
    };
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        build,
        "xab",
        "X",
        "xX",
    ));
    assert_violates(&replace_re_verdict(
        "str.replace_re",
        build,
        "xab",
        "X",
        "xaX",
    ));
}

#[test]
fn replace_re_plus_takes_the_shortest_repetition() {
    // `(re.+ (re.range "0" "9"))` matches "1", "12" and "123" at position 1;
    // the shortest is the one replaced.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let d = re_range(ts, "0", "9");
            app(ts, "re.+", &[d], Sort::RegLan)
        },
        "a123b",
        "N",
        "aN23b",
    ));
}

#[test]
fn replace_re_all_plus_takes_the_shortest_repetition_each_time() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| {
            let d = re_range(ts, "0", "9");
            app(ts, "re.+", &[d], Sort::RegLan)
        },
        "a12b34",
        "N",
        "aNNbNN",
    ));
}

// ── first-only vs all, and the no-rescan rule ──

#[test]
fn replace_re_rewrites_only_the_first_occurrence() {
    let build = |ts: &mut TermStore| re_lit(ts, "X");
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        build,
        "aXbXc",
        "Y",
        "aYbXc",
    ));
    // The wrong-answer class this gate exists to catch: claiming replace_re
    // behaves like replace_re_all must be REFUTED, not merely unconfirmed.
    assert_violates(&replace_re_verdict(
        "str.replace_re",
        build,
        "aXbXc",
        "Y",
        "aYbYc",
    ));
}

#[test]
fn replace_re_all_rewrites_every_occurrence() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_lit(ts, "X"),
        "aXbXc",
        "Y",
        "aYbYc",
    ));
}

#[test]
fn replace_re_all_matches_are_non_overlapping_left_to_right() {
    // "aaa" has an "aa" at 0 and at 1; the recursion continues on the SUFFIX
    // after the first match, so only one replacement fires.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_lit(ts, "aa"),
        "aaa",
        "X",
        "Xa",
    ));
}

#[test]
fn replace_re_all_never_rescans_the_text_it_just_inserted() {
    // The clause recurses on `z`, never on `t ++ z`. Rescanning would not
    // terminate here; it must produce "aab", not diverge or over-replace.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_lit(ts, "a"),
        "ab",
        "aa",
        "aab",
    ));
}

// ── no match, empty subject, and char (not byte) indexing ──

#[test]
fn replace_re_without_a_match_returns_the_subject() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let x = re_lit(ts, "x");
            let z = re_lit(ts, "z");
            app(ts, "re.union", &[x, z], Sort::RegLan)
        },
        "hello",
        "Q",
        "hello",
    ));
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| {
            let x = re_lit(ts, "x");
            let z = re_lit(ts, "z");
            app(ts, "re.union", &[x, z], Sort::RegLan)
        },
        "hello",
        "Q",
        "hello",
    ));
}

#[test]
fn replace_re_on_the_empty_subject_is_the_identity() {
    // With a non-nullable regex the empty string admits no decomposition.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| re_lit(ts, "a"),
        "",
        "X",
        "",
    ));
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_lit(ts, "a"),
        "",
        "X",
        "",
    ));
}

#[test]
fn replace_re_splices_at_code_point_boundaries_not_byte_boundaries() {
    // Every character here is multi-byte, so a byte-indexed splice would cut a
    // code point in half or land on the wrong one.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| re_lit(ts, "\u{3b2}"),
        "\u{3b1}\u{3b2}\u{3b3}",
        "X",
        "\u{3b1}X\u{3b3}",
    ));
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_range(ts, "\u{3b1}", "\u{3b2}"),
        "\u{3b1}\u{3b2}\u{3b3}",
        "-",
        "--\u{3b3}",
    ));
}

#[test]
fn replace_re_reads_its_subject_from_the_model() {
    // Not ground: the subject is a leaf the model pins, which is the shape the
    // gate actually meets when re-checking a solver model.
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::String);
    let digit = re_range(&mut ts, "0", "9");
    let regex = app(&mut ts, "re.+", &[digit], Sort::RegLan);
    let t = ts.mk_string("#".to_string());
    let call = app(&mut ts, "str.replace_re_all", &[x, regex, t], Sort::String);
    let want = ts.mk_string("a#b#".to_string());
    let eq = app(&mut ts, "=", &[call, want], Sort::Bool);

    let satisfying = StubModel::new().with(x, ModelValue::Str("a1b2".to_string()));
    assert_confirmed(&verdict(&ts, &satisfying, &[eq]));

    let violating = StubModel::new().with(x, ModelValue::Str("a1b".to_string()));
    assert_violates(&verdict(&ts, &violating, &[eq]));

    // An unpinned subject must not be guessed.
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq]));
}

// ── deliberately fail-closed shapes ──────────────────────────────────────
//
// Each of these returns CannotConfirm. That is a completeness cost only: the
// gate never assumes an assertion it cannot compute, so a refusal can only
// leave a verdict at `unknown`, never publish a wrong `sat`.

#[test]
fn replace_re_fails_closed_on_a_star_regex() {
    // `re.*` accepts the empty word. `str.replace_re`'s clause has no
    // `w != ""` side condition and `str.replace_re_all`'s does, so the two
    // disagree about what the empty match means; the gate declines both.
    for op in ["str.replace_re", "str.replace_re_all"] {
        assert_cannot(&replace_re_verdict(
            op,
            |ts| {
                let a = re_lit(ts, "a");
                app(ts, "re.*", &[a], Sort::RegLan)
            },
            "bbb",
            "X",
            "Xbbb",
        ));
    }
}

#[test]
fn replace_re_fails_closed_on_an_empty_literal_regex() {
    for op in ["str.replace_re", "str.replace_re_all"] {
        assert_cannot(&replace_re_verdict(
            op,
            |ts| re_lit(ts, ""),
            "abc",
            "X",
            "Xabc",
        ));
    }
}

#[test]
fn replace_re_fails_closed_on_re_all_and_re_opt() {
    for op in ["str.replace_re", "str.replace_re_all"] {
        assert_cannot(&replace_re_verdict(
            op,
            |ts| app(ts, "re.all", &[], Sort::RegLan),
            "abc",
            "X",
            "Xabc",
        ));
        assert_cannot(&replace_re_verdict(
            op,
            |ts| {
                let a = re_lit(ts, "a");
                app(ts, "re.opt", &[a], Sort::RegLan)
            },
            "abc",
            "X",
            "Xabc",
        ));
    }
}

#[test]
fn replace_re_detects_nullability_below_the_top_level() {
    // The union is nullable only because one alternative is; the check is a
    // real emptiness probe of the whole regex, not a syntactic top-level test.
    assert_cannot(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let a = re_lit(ts, "a");
            let eps = re_lit(ts, "");
            app(ts, "re.union", &[a, eps], Sort::RegLan)
        },
        "bab",
        "X",
        "Xbab",
    ));
}

#[test]
fn replace_re_fails_closed_on_an_unsupported_regex_operator() {
    assert_cannot(&replace_re_verdict(
        "str.replace_re",
        |ts| app(ts, "re.future", &[], Sort::RegLan),
        "abc",
        "X",
        "Xbc",
    ));
}

#[test]
fn replace_re_fails_closed_on_a_non_reglan_pattern_argument() {
    let mut ts = TermStore::new();
    let s = ts.mk_string("abc".to_string());
    let pattern = ts.mk_string("a".to_string());
    let t = ts.mk_string("X".to_string());
    let call = app(&mut ts, "str.replace_re", &[s, pattern, t], Sort::String);
    let want = ts.mk_string("Xbc".to_string());
    let eq = app(&mut ts, "=", &[call, want], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn replace_re_fails_closed_outside_the_smtlib_alphabet() {
    // U+30000 is above the SMT-LIB Unicode Strings alphabet bound (0x2FFFF).
    // Both the subject and the spliced-in replacement are held to it, so the
    // gate can never confirm a value it would refuse to read back.
    assert_cannot(&replace_re_verdict(
        "str.replace_re",
        |ts| re_lit(ts, "a"),
        "\u{30000}a",
        "X",
        "\u{30000}X",
    ));
    assert_cannot(&replace_re_verdict(
        "str.replace_re",
        |ts| re_lit(ts, "a"),
        "za",
        "\u{30000}",
        "z\u{30000}",
    ));
}

#[test]
fn replace_re_fails_closed_on_wrong_arity() {
    let mut ts = TermStore::new();
    let s = ts.mk_string("abc".to_string());
    let regex = re_lit(&mut ts, "a");
    let call = app(&mut ts, "str.replace_re", &[s, regex], Sort::String);
    let want = ts.mk_string("abc".to_string());
    let eq = app(&mut ts, "=", &[call, want], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq]));
}
