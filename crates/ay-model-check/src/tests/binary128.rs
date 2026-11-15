// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const WITNESS: u128 = 0x3fff_8000_0000_0000_0000_0000_0000_0001;
const FRACTION: u128 = (1u128 << 111) + 1;

#[test]
fn all_admitted_raw_formats_have_one_nan_and_distinct_signed_zeros_and_infinities() {
    for eb in [63, 64] {
        for sb in [65, 129] {
            let mut terms = TermStore::new();
            let sort = Sort::FloatingPoint(eb, sb);
            let x = terms.mk_var("x", sort.clone());
            let y = terms.mk_var("y", sort);
            let equality = app(&mut terms, "=", &[x, y], Sort::Bool);
            let distinct = app(&mut terms, "distinct", &[x, y], Sort::Bool);
            let maximum = if eb == 64 { u64::MAX } else { (1u64 << eb) - 1 };
            let value = |(sign, exponent, significand)| ModelValue::FloatingPoint {
                sign,
                exponent,
                significand,
                exponent_bits: eb,
                significand_bits: sb,
            };
            for (a, b, equal) in [
                ((false, maximum, 1), (true, maximum, 2), true),
                ((false, 0, 0), (true, 0, 0), false),
                ((false, maximum, 0), (true, maximum, 0), false),
                ((false, maximum, 1), (false, maximum, 0), false),
            ] {
                let model = StubModel::new().with(x, value(a)).with(y, value(b));
                if equal {
                    // A false confirmation here is a wrong SAT certificate,
                    // not merely failure to simplify an equality.
                    assert_violates(&verdict(&terms, &model, &[distinct]));
                    assert_confirmed(&verdict(&terms, &model, &[equality]));
                } else {
                    assert_violates(&verdict(&terms, &model, &[equality]));
                    assert_confirmed(&verdict(&terms, &model, &[distinct]));
                }
            }
        }
    }
}

fn quad(sign: bool, exponent: u64, significand: u128) -> ModelValue {
    ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits: 15,
        significand_bits: 113,
    }
}

fn cast(terms: &mut TermStore, bits: TermId, eb: u32, sb: u32) -> TermId {
    terms.mk_app(
        Symbol::Indexed("to_fp".into(), vec![eb, sb]),
        &[bits],
        Sort::FloatingPoint(eb, sb),
    )
}

#[test]
fn complete_raw_fields_preserve_the_u64_data_envelope_without_granting_arithmetic() {
    for eb in [63, 64] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("raw_fields", Sort::FloatingPoint(eb, 129));
        let exponent = if eb == 64 {
            u64::MAX - 1
        } else {
            (1u64 << eb) - 2
        };
        let value = ModelValue::FloatingPoint {
            sign: true,
            exponent,
            significand: u128::MAX,
            exponent_bits: eb,
            significand_bits: 129,
        };
        let bits = (BigInt::from(1) << (eb + 128))
            | (BigInt::from(exponent) << 128u32)
            | BigInt::from(u128::MAX);
        let raw = terms.mk_bitvec(bits, eb + 129);
        let reinterpreted = cast(&mut terms, raw, eb, 129);
        if eb == 64 {
            assert!(crate::fp::Fp::from_value(&value).is_err());
        }
        let model = StubModel::new().with(x, value);
        for term in [x, reinterpreted] {
            let EvalOutcome::Value(ModelValue::FloatingPoint {
                sign,
                exponent: actual_exp,
                significand,
                exponent_bits,
                significand_bits,
            }) = evaluate_term(&terms, &model, term)
            else {
                panic!("raw fields refused")
            };
            assert_eq!(
                (
                    sign,
                    actual_exp,
                    significand,
                    exponent_bits,
                    significand_bits
                ),
                (true, exponent, u128::MAX, eb, 129)
            );
        }
    }
}

fn witness_claims(terms: &mut TermStore, x: TermId) -> [TermId; 2] {
    let real = app(terms, "fp.to_real", &[x], Sort::Real);
    let expected = terms.mk_rational(BigRational::new(
        BigInt::from(3) * (BigInt::from(1) << 111usize) + 1,
        BigInt::from(1) << 112usize,
    ));
    let exact_real = app(terms, "=", &[real, expected], Sort::Bool);
    let bits = app(terms, "fp.to_ieee_bv", &[x], Sort::bitvec(128));
    let expected = terms.mk_bitvec(BigInt::from(WITNESS), 128);
    let exact_bits = app(terms, "=", &[bits, expected], Sort::Bool);
    [exact_real, exact_bits]
}

#[test]
fn binary128_literal_reinterpret_and_to_real_confirm_exact_witness() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("quad", Sort::FloatingPoint(15, 113));
    let claims = witness_claims(&mut terms, x);
    let sign = terms.mk_bitvec(BigInt::from(0), 1);
    let exponent = terms.mk_bitvec(BigInt::from(0x3fff), 15);
    let fraction = terms.mk_bitvec(BigInt::from(FRACTION), 112);
    let literal = app(
        &mut terms,
        "fp",
        &[sign, exponent, fraction],
        Sort::FloatingPoint(15, 113),
    );
    let bits = terms.mk_bitvec(BigInt::from(WITNESS), 128);
    let reinterpreted = cast(&mut terms, bits, 15, 113);
    let literal_equal = app(&mut terms, "=", &[x, literal], Sort::Bool);
    let reinterpreted_equal = app(&mut terms, "=", &[x, reinterpreted], Sort::Bool);
    let previous_bits = terms.mk_bitvec(BigInt::from(WITNESS - 1), 128);
    let previous = cast(&mut terms, previous_bits, 15, 113);
    let next_bits = terms.mk_bitvec(BigInt::from(WITNESS + 1), 128);
    let next = cast(&mut terms, next_bits, 15, 113);
    let increasing = app(&mut terms, "fp.lt", &[previous, x, next], Sort::Bool);
    let normal = app(&mut terms, "fp.isNormal", &[x], Sort::Bool);
    let model = StubModel::new().with(x, quad(false, 0x3fff, FRACTION));
    assert_confirmed(&verdict(
        &terms,
        &model,
        &[
            claims[0],
            claims[1],
            literal_equal,
            reinterpreted_equal,
            increasing,
            normal,
        ],
    ));

    // The special-value decoder also uses the new format without exposing a
    // NaN payload as a uniquely specified IEEE result.
    let nan = terms.mk_app(
        Symbol::Indexed("NaN".into(), vec![15, 113]),
        &[],
        Sort::FloatingPoint(15, 113),
    );
    let is_nan = app(&mut terms, "fp.isNaN", &[nan], Sort::Bool);
    assert_confirmed(&verdict(&terms, &model, &[is_nan]));
}

#[test]
fn binary128_model_mutations_are_independently_refuted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("quad", Sort::FloatingPoint(15, 113));
    let claims = witness_claims(&mut terms, x);
    assert_confirmed(&verdict(
        &terms,
        &StubModel::new().with(x, quad(false, 0x3fff, FRACTION)),
        &claims,
    ));
    for wrong in [
        quad(false, 0x3fff, 0), // former loss of the full stored fraction
        quad(false, 0x3fff, FRACTION ^ (1u128 << 111)),
        quad(false, 0x3fff, FRACTION ^ 1),
        quad(false, 0x3fff, FRACTION ^ (1u128 << 64)),
        quad(false, 0x4000, FRACTION),
        quad(true, 0x3fff, FRACTION),
    ] {
        let model = StubModel::new().with(x, wrong);
        match verdict(&terms, &model, &claims) {
            GateVerdict::ModelViolates { assertion } => assert!(claims.contains(&assertion)),
            other => panic!(
                "a well-formed wrong binary128 value must violate the original query: {other:?}"
            ),
        }
    }
}

struct AppPins {
    leaves: HashMap<TermId, ModelValue>,
    applications: HashMap<TermId, ModelValue>,
    calls: Cell<usize>,
}

impl ModelView for AppPins {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.leaves
            .get(&term)
            .or_else(|| self.applications.get(&term))
            .cloned()
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.calls.set(self.calls.get() + 1);
        self.applications.get(&term).cloned()
    }
}

#[test]
fn binary128_interpreted_results_cannot_adopt_lying_applications() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(15, 113);
    let x = terms.mk_var("one", sort.clone());
    let y = terms.mk_var("three", sort.clone());
    let result = terms.mk_var("third", sort.clone());
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let division = app(&mut terms, "fp.div", &[rm, x, y], sort.clone());
    let third_fraction = ((1u128 << 112) - 1) / 3;
    let exact = quad(false, 0x3ffd, third_fraction);
    let wrong = quad(false, 0x3ffd, third_fraction + 1);
    let one_third = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(3)));
    let conversion = terms.mk_app(
        Symbol::Indexed("to_fp".into(), vec![15, 113]),
        &[rm, one_third],
        sort,
    );
    let div_eq = app(&mut terms, "=", &[result, division], Sort::Bool);
    let conv_eq = app(&mut terms, "fp.eq", &[result, conversion], Sort::Bool);
    for (returned, valid) in [(exact, true), (wrong.clone(), false)] {
        let model = AppPins {
            leaves: HashMap::from([
                (x, quad(false, 0x3fff, 0)),
                (y, quad(false, 0x4000, 1u128 << 111)),
                (result, returned),
            ]),
            applications: HashMap::from([
                (division, wrong.clone()),
                (conversion, wrong.clone()),
                (div_eq, ModelValue::Bool(true)),
                (conv_eq, ModelValue::Bool(true)),
            ]),
            calls: Cell::new(0),
        };
        for claim in [div_eq, conv_eq] {
            let result = verdict(&terms, &model, &[claim]);
            if valid {
                assert_confirmed(&result);
            } else {
                assert_violates(&result);
            }
        }
        assert_eq!(
            model.calls.get(),
            0,
            "interpreted FP operators must not consult committed application values"
        );
    }
}

#[test]
fn binary128_malformed_and_wrong_sort_values_never_confirm() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("quad", Sort::FloatingPoint(15, 113));
    let claims = witness_claims(&mut terms, x);
    for bad in [
        quad(false, 0x3fff, 1u128 << 112),
        quad(false, 0x8000, 0),
        ModelValue::FloatingPoint {
            sign: false,
            exponent: 0,
            significand: 0,
            exponent_bits: 11,
            significand_bits: 53,
        },
        ModelValue::FloatingPoint {
            sign: false,
            exponent: 0,
            significand: 0,
            exponent_bits: 15,
            significand_bits: 129,
        },
        ModelValue::Bool(false),
    ] {
        assert_cannot(&verdict(
            &terms,
            &StubModel::new().with(x, bad),
            &[claims[0]],
        ));
    }
    let bits = terms.mk_var("malformed-bits", Sort::bitvec(128));
    let reinterpreted = cast(&mut terms, bits, 15, 113);
    let real = app(&mut terms, "fp.to_real", &[reinterpreted], Sort::Real);
    let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0)));
    let claim = app(&mut terms, "=", &[real, zero], Sort::Bool);
    for bad in [
        ModelValue::BitVec {
            value: BigInt::from(-1),
            width: 128,
        },
        ModelValue::BitVec {
            value: BigInt::from(1) << 128usize,
            width: 128,
        },
        ModelValue::BitVec {
            value: BigInt::from(0),
            width: 127,
        },
    ] {
        assert_cannot(&verdict(
            &terms,
            &StubModel::new().with(bits, bad),
            &[claim],
        ));
    }

    // Real typed aggregate equality traverses both distinct leaves. The old
    // sb65 exception cannot admit a now-representable out-of-width fraction.
    let array_sort = Sort::array(Sort::Bool, Sort::FloatingPoint(8, 65));
    let a = terms.mk_var("a", array_sort.clone());
    let b = terms.mk_var("b", array_sort);
    let equal = app(&mut terms, "=", &[a, b], Sort::Bool);
    for (fraction, valid) in [(u128::from(u64::MAX), true), (1u128 << 64, false)] {
        let array = ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::FloatingPoint {
                sign: false,
                exponent: 1,
                significand: fraction,
                exponent_bits: 8,
                significand_bits: 65,
            },
            store: Vec::new(),
        }));
        let model = StubModel::new().with(a, array.clone()).with(b, array);
        let result = verdict(&terms, &model, &[equal]);
        if valid {
            assert_confirmed(&result);
        } else {
            assert_cannot(&result);
        }
    }
    let nan = terms.mk_var("nan", Sort::FloatingPoint(15, 113));
    let ieee = app(&mut terms, "fp.to_ieee_bv", &[nan], Sort::bitvec(128));
    let model = AppPins {
        leaves: HashMap::from([(nan, quad(false, 0x7fff, 1))]),
        applications: HashMap::from([(ieee, ModelValue::Bool(true))]),
        calls: Cell::new(0),
    };
    assert!(matches!(
        evaluate_term(&terms, &model, ieee),
        EvalOutcome::Unevaluable(_)
    ));
    assert_eq!(
        model.calls.get(),
        1,
        "the typed NaN residue must reject the actual offered wrong-sort value"
    );
}
