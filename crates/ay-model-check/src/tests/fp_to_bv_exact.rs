// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use num_bigint::BigUint;

fn conversion(terms: &mut TermStore, x: TermId, mode: &str, signed: bool) -> TermId {
    let rm = terms.mk_app(
        Symbol::named(mode),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    terms.mk_app(
        Symbol::Indexed(
            if signed { "fp.to_sbv" } else { "fp.to_ubv" }.into(),
            vec![8],
        ),
        &[rm, x],
        Sort::bitvec(8),
    )
}

#[test]
fn fp_to_bv_exact_midpoint_neighbors_all_modes_and_signs() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    for (delta, nearest) in [(-1, 1), (0, 2), (1, 2)] {
        let half = BigUint::from(1u8) << 198usize;
        let fraction = if delta < 0 {
            half - 1u8
        } else {
            half + delta as u8
        };
        for negative in [false, true] {
            let value =
                ModelValue::floating_point_exact(negative, 127u8.into(), fraction.clone(), 8, 200)
                    .unwrap();
            let model = StubModel::new().with(x, value);
            for (mode, magnitude) in [
                ("RNE", nearest),
                ("RNA", nearest),
                ("RTZ", 1),
                ("RTP", if negative { 1 } else { 2 }),
                ("RTN", if negative { 2 } else { 1 }),
            ] {
                let converted = conversion(&mut terms, x, mode, true);
                let expected = if negative { 256 - magnitude } else { magnitude };
                assert!(
                    matches!(evaluate_term(&terms, &model, converted),
                    EvalOutcome::Value(ModelValue::BitVec { value, width: 8 }) if value == int(expected)),
                    "{mode} delta={delta} sign={negative}"
                );
                let wrong = terms.mk_bitvec(int((expected + 1) % 256), 8);
                let claim = app(&mut terms, "=", &[converted, wrong], Sort::Bool);
                assert_violates(&verdict(&terms, &model, &[claim]));
            }
        }
    }
    let fraction = BigUint::from(1u8) << 197usize; // 2.5, exponent 1
    let model = StubModel::new().with(
        x,
        ModelValue::floating_point_exact(false, 128u8.into(), fraction, 8, 200).unwrap(),
    );
    for (mode, expected) in [("RNE", 2), ("RNA", 3)] {
        let converted = conversion(&mut terms, x, mode, false);
        assert!(matches!(evaluate_term(&terms, &model, converted),
            EvalOutcome::Value(ModelValue::BitVec { value, .. }) if value == int(expected)));
    }
}

#[test]
fn fp_to_bv_exact_subnormal_zero_sparse_integer_and_type_refusals() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    for negative in [false, true] {
        for fraction in [0u8, 1] {
            let model = StubModel::new().with(
                x,
                ModelValue::floating_point_exact(negative, 0u8.into(), fraction.into(), 8, 200)
                    .unwrap(),
            );
            for mode in ["RNE", "RNA", "RTZ", "RTP", "RTN"] {
                let converted = conversion(&mut terms, x, mode, true);
                let expected =
                    if fraction == 1 && (mode == "RTP" && !negative || mode == "RTN" && negative) {
                        if negative {
                            255
                        } else {
                            1
                        }
                    } else {
                        0
                    };
                assert!(matches!(evaluate_term(&terms, &model, converted),
                    EvalOutcome::Value(ModelValue::BitVec { value, .. }) if value == int(expected)));
            }
        }
    }
    let huge = terms.mk_var("sparse", Sort::FloatingPoint(8, 1 << 20));
    let sparse = StubModel::new().with(
        huge,
        ModelValue::floating_point_exact(false, 127u8.into(), 0u8.into(), 8, 1 << 20).unwrap(),
    );
    let converted = conversion(&mut terms, huge, "RNE", false);
    assert!(
        matches!(evaluate_term(&terms, &sparse, converted), EvalOutcome::Value(ModelValue::BitVec { value, .. }) if value == int(1))
    );
    let bad = StubModel::new().with(
        x,
        ModelValue::floating_point_exact(false, 127u8.into(), 0u8.into(), 8, 201).unwrap(),
    );
    let converted = conversion(&mut terms, x, "RNE", false);
    assert!(matches!(
        evaluate_term(&terms, &bad, converted),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn fp_to_bv_exact_nonfinite_and_out_of_range_keep_typed_committed_choices() {
    struct Pins {
        x: TermId,
        value: ModelValue,
        result: ModelValue,
    }
    impl ModelView for Pins {
        fn leaf_value(&self, id: TermId) -> Option<ModelValue> {
            (id == self.x).then(|| self.value.clone())
        }
        fn uf_app_value(&self, _: TermId) -> Option<ModelValue> {
            Some(self.result.clone())
        }
    }
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    let converted = conversion(&mut terms, x, "RNE", false);
    for (exponent, fraction) in [(255u8, 0u8), (255, 1), (135, 0)] {
        let model = Pins {
            x,
            value: ModelValue::floating_point_exact(
                false,
                exponent.into(),
                fraction.into(),
                8,
                200,
            )
            .unwrap(),
            result: ModelValue::bitvec(int(73), 8),
        };
        assert!(
            matches!(evaluate_term(&terms, &model, converted), EvalOutcome::Value(ModelValue::BitVec { value, width: 8 }) if value == int(73))
        );
        let wrong_sort = Pins {
            result: ModelValue::Bool(true),
            ..model
        };
        assert!(matches!(
            evaluate_term(&terms, &wrong_sort, converted),
            EvalOutcome::Unevaluable(_)
        ));
    }
}

#[test]
fn fp_to_bv_exact_nan_choices_remain_congruent_within_the_source_format() {
    struct Pins {
        leaves: HashMap<TermId, ModelValue>,
        apps: HashMap<TermId, ModelValue>,
    }
    impl ModelView for Pins {
        fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
            self.leaves.get(&t).cloned()
        }
        fn uf_app_value(&self, t: TermId) -> Option<ModelValue> {
            self.apps.get(&t).cloned()
        }
    }
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    let y = terms.mk_var("y", Sort::FloatingPoint(8, 200));
    let a = conversion(&mut terms, x, "RNE", false);
    let b = conversion(&mut terms, y, "RNE", false);
    let seven = terms.mk_bitvec(int(7), 8);
    let eight = terms.mk_bitvec(int(8), 8);
    let claims = [
        app(&mut terms, "=", &[a, seven], Sort::Bool),
        app(&mut terms, "=", &[b, eight], Sort::Bool),
    ];
    let nan = ModelValue::floating_point_exact(false, 255u8.into(), 1u8.into(), 8, 200).unwrap();
    let model = Pins {
        leaves: HashMap::from([(x, nan.clone()), (y, nan)]),
        apps: HashMap::from([
            (a, ModelValue::bitvec(int(7), 8)),
            (b, ModelValue::bitvec(int(8), 8)),
        ]),
    };
    assert_violates(&verdict(&terms, &model, &claims));
}

#[test]
fn fp_to_bv_exact_cancellation_after_work_acceptance_cannot_publish_a_value() {
    struct Cancel {
        value: ModelValue,
        stop: Cell<bool>,
        threshold: usize,
    }
    impl ModelView for Cancel {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(self.value.clone())
        }
        fn charge_functional_array_work(&self, work: usize) -> Result<(), String> {
            if work >= self.threshold {
                self.stop.set(true);
            }
            Ok(())
        }
        fn exact_fp_interrupted(&self) -> bool {
            self.stop.get()
        }
    }
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    let converted = conversion(&mut terms, x, "RNE", true);
    let value = ModelValue::floating_point_exact(false, 127u8.into(), 1u8.into(), 8, 200).unwrap();
    let threshold = crate::fp_exact::bv_plan(
        &value,
        8,
        crate::fp_exact::BvSignedness::Signed,
        crate::fp::RoundingMode::Rne,
    )
    .unwrap()
    .work;
    let model = Cancel {
        value,
        stop: Cell::new(false),
        threshold,
    };
    assert!(matches!(
        evaluate_term(&terms, &model, converted),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(model.stop.get());
}

#[test]
fn fp_to_bv_exact_signed_minimum_is_a_value_not_wrapped_overflow() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("boundary", Sort::FloatingPoint(8, 200));
    let signed = conversion(&mut terms, x, "RNE", true);
    for negative in [false, true] {
        let model = StubModel::new().with(
            x,
            ModelValue::floating_point_exact(negative, 134u8.into(), 0u8.into(), 8, 200).unwrap(),
        );
        if negative {
            assert!(
                matches!(evaluate_term(&terms, &model, signed), EvalOutcome::Value(ModelValue::BitVec { value, width: 8 }) if value == int(128))
            );
        } else {
            assert!(
                matches!(
                    evaluate_term(&terms, &model, signed),
                    EvalOutcome::Unevaluable(_)
                ),
                "positive128 is unspecified, with no committed choice"
            );
        }
    }
}

#[test]
fn fp_to_bv_exact_dense_fraction_prices_actual_scans_not_a_fictional_denominator() {
    let mut terms = TermStore::new();
    let sb = 1 << 20;
    let x = terms.mk_var("dense_fraction", Sort::FloatingPoint(8, sb));
    let fraction = (BigUint::from(1u8) << (sb - 2)) + BigUint::from(1u8);
    let value = ModelValue::floating_point_exact(false, 127u8.into(), fraction, 8, sb).unwrap();
    let model = StubModel::new().with(x, value);
    let converted = conversion(&mut terms, x, "RNE", false);
    assert!(matches!(evaluate_term(&terms, &model, converted),
        EvalOutcome::Value(ModelValue::BitVec { value, width: 8 }) if value == int(2)));
}
