// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `fp.to_ubv`/`fp.to_sbv` where SMT-LIB leaves the result unspecified (NaN,
//! the infinities, out of range): the gate adopts the model's value, keyed for
//! congruence on the mode, the width and the argument (D7, 2026-09-23 hunt).

use super::*;

/// Leaf values plus per-application pins, like a solver model that recorded
/// the value it chose for each conversion.
struct Pins {
    leaves: HashMap<TermId, ModelValue>,
    applications: HashMap<TermId, ModelValue>,
}

impl ModelView for Pins {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.leaves.get(&term).cloned()
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.applications.get(&term).cloned()
    }
}

fn nan() -> ModelValue {
    ModelValue::FloatingPoint {
        sign: false,
        exponent: 0b111,
        significand: 0b101,
        exponent_bits: 3,
        significand_bits: 4,
    }
}

fn to_ubv3(terms: &mut TermStore, rm: TermId, x: TermId) -> TermId {
    terms.mk_app(
        Symbol::Indexed("fp.to_ubv".into(), vec![3]),
        &[rm, x],
        Sort::bitvec(3),
    )
}

#[test]
fn unspecified_conversion_adopts_one_value_per_mode_and_argument() {
    let mut terms = TermStore::new();
    let fp = Sort::FloatingPoint(3, 4);
    let x = terms.mk_var("x", fp.clone());
    let y = terms.mk_var("y", fp);
    let rne = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let rtz = terms.mk_app(
        Symbol::named("RTZ"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let at_rne = to_ubv3(&mut terms, rne, x);
    let at_rtz = to_ubv3(&mut terms, rtz, x);
    let at_rne_y = to_ubv3(&mut terms, rne, y);
    let differ = app(&mut terms, "=", &[at_rne, at_rtz], Sort::Bool);
    let differ = app(&mut terms, "not", &[differ], Sort::Bool);
    let five = ModelValue::bitvec(BigInt::from(5), 3);
    let six = ModelValue::bitvec(BigInt::from(6), 3);

    // (RNE, NaN) and (RTZ, NaN) are different arguments: two values confirm.
    let model = Pins {
        leaves: HashMap::from([(x, nan()), (y, nan())]),
        applications: HashMap::from([(at_rne, five.clone()), (at_rtz, six.clone())]),
    };
    assert_confirmed(&verdict(&terms, &model, &[differ]));

    // (RNE, x) and (RNE, y) at one NaN are ONE argument: the value adopted
    // for the first application binds the second, so a model claiming they
    // differ is refuted rather than confirmed.
    let same = app(&mut terms, "=", &[at_rne, at_rne_y], Sort::Bool);
    let same_differs = app(&mut terms, "not", &[same], Sort::Bool);
    let model = Pins {
        leaves: HashMap::from([(x, nan()), (y, nan())]),
        applications: HashMap::from([(at_rne, five.clone()), (at_rne_y, six)]),
    };
    assert!(!matches!(
        verdict(&terms, &model, &[same_differs]),
        GateVerdict::ConfirmedSat
    ));

    // A value of the wrong width is not a conversion result.
    let model = Pins {
        leaves: HashMap::from([(x, nan()), (y, nan())]),
        applications: HashMap::from([
            (at_rne, ModelValue::bitvec(BigInt::from(5), 4)),
            (at_rtz, five),
        ]),
    };
    assert_cannot(&verdict(&terms, &model, &[differ]));
}

#[test]
fn unspecified_conversion_keeps_distinct_source_formats_separate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(3, 5));
    let y = terms.mk_var("y", Sort::FloatingPoint(4, 4));
    let rne = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let left = to_ubv3(&mut terms, rne, x);
    let right = to_ubv3(&mut terms, rne, y);
    let equal = app(&mut terms, "=", &[left, right], Sort::Bool);
    let distinct = app(&mut terms, "not", &[equal], Sort::Bool);
    let model = Pins {
        leaves: HashMap::from([
            (
                x,
                ModelValue::FloatingPoint {
                    sign: false,
                    exponent: 7,
                    significand: 1,
                    exponent_bits: 3,
                    significand_bits: 5,
                },
            ),
            (
                y,
                ModelValue::FloatingPoint {
                    sign: false,
                    exponent: 15,
                    significand: 1,
                    exponent_bits: 4,
                    significand_bits: 4,
                },
            ),
        ]),
        applications: HashMap::from([
            (left, ModelValue::bitvec(BigInt::from(5), 3)),
            (right, ModelValue::bitvec(BigInt::from(6), 3)),
        ]),
    };
    assert_confirmed(&verdict(&terms, &model, &[distinct]));
}
