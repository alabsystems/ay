// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_bigint::BigUint;

fn rounded(terms: &mut TermStore, x: TermId, mode: &str) -> TermId {
    let rm = terms.mk_app(
        Symbol::named(mode),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    terms.mk_app(
        Symbol::named("fp.roundToIntegral"),
        &[rm, x],
        terms.sort(x).clone(),
    )
}

fn exact(sign: bool, exponent: BigUint, fraction: BigUint, eb: u32, sb: u32) -> ModelValue {
    ModelValue::floating_point_exact(sign, exponent, fraction, eb, sb).unwrap()
}

#[test]
fn rounding_names_cannot_confirm_a_model_with_the_wrong_rounding_result() {
    struct RoundingModel(StubModel);
    impl ModelView for RoundingModel {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            self.0.leaf_value(term)
        }
        fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
            self.0.leaf_value(term)
        }
    }
    for declared in [false, true] {
        let mut terms = TermStore::new();
        let sort = Sort::FloatingPoint(8, 24);
        let rm_sort = Sort::Uninterpreted("RoundingMode".into());
        let mode = if declared {
            let term = terms.mk_app(Symbol::named("RNE"), [], rm_sort);
            terms.register_declared_function("RNE");
            term
        } else {
            terms.mk_var("RNE", rm_sort)
        };
        let input = terms.mk_var("input", sort.clone());
        let output = terms.mk_var("output", sort.clone());
        let rounded = terms.mk_app(Symbol::named("fp.roundToIntegral"), [mode, input], sort);
        let claim = terms.mk_eq(rounded, output);
        // Input=2.5, actual mode=RTP, claimed result=2. The claim is false:
        // RTP rounds this to 3, irrespective of the variable's display name.
        let model = RoundingModel(
            StubModel::new()
                .with(mode, ModelValue::Uninterpreted("RTP".into()))
                .with(
                    input,
                    exact(false, 128u8.into(), (1u32 << 21).into(), 8, 24),
                )
                .with(output, exact(false, 128u8.into(), 0u8.into(), 8, 24)),
        );
        assert!(
            matches!(
                verdict(&terms, &model, &[claim]),
                GateVerdict::ModelViolates { .. }
            ),
            "registered={declared}"
        );
        let correct = RoundingModel(model.0.with(
            output,
            exact(false, 128u8.into(), (1u32 << 22).into(), 8, 24),
        ));
        assert_confirmed(&verdict(&terms, &correct, &[claim]));
    }
}

#[test]
fn rounding_names_at_wrong_sorts_or_indexed_heads_cannot_confirm_models() {
    for indexed in [false, true] {
        let mut terms = TermStore::new();
        let mode = if indexed {
            terms.mk_app(
                Symbol::indexed("RNE", vec![0]),
                [],
                Sort::Uninterpreted("RoundingMode".into()),
            )
        } else {
            terms.mk_app(Symbol::named("RNE"), [], Sort::Bool)
        };
        let sort = Sort::FloatingPoint(8, 24);
        let input = terms.mk_var("input", sort.clone());
        let rounded = terms.mk_app(Symbol::named("fp.roundToIntegral"), [mode, input], sort);
        let claim = terms.mk_eq(rounded, input);
        let model = StubModel::new().with(input, exact(false, 127u8.into(), 0u8.into(), 8, 24));
        assert!(
            matches!(
                verdict(&terms, &model, &[claim]),
                GateVerdict::CannotConfirm { .. }
            ),
            "indexed={indexed}"
        );
    }
}

#[test]
fn fp_round_integral_exact_midpoints_and_carry() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    let half = BigUint::from(1u8) << 198usize;
    for (fraction, nearest) in [
        (&half - 1u8, 127u8),
        (half.clone(), 128),
        (&half + 1u8, 128),
    ] {
        for sign in [false, true] {
            let model =
                StubModel::new().with(x, exact(sign, 127u8.into(), fraction.clone(), 8, 200));
            for (rm, exponent) in [
                ("RNE", nearest),
                ("RTZ", 127),
                ("RTP", if sign { 127 } else { 128 }),
                ("RTN", if sign { 128 } else { 127 }),
            ] {
                let root = rounded(&mut terms, x, rm);
                assert!(matches!(evaluate_term(&terms, &model, root),
                    EvalOutcome::Value(ModelValue::FloatingPointExact { sign: s, exponent: e, significand: f, .. })
                    if s == sign && *e == BigUint::from(exponent) && f.bits() == 0));
            }
        }
    }
    let model = StubModel::new().with(x, exact(false, 128u8.into(), &half >> 1usize, 8, 200));
    for (rm, fraction) in [("RNE", BigUint::from(0u8)), ("RNA", half.clone())] {
        let root = rounded(&mut terms, x, rm);
        assert!(matches!(evaluate_term(&terms, &model, root),
            EvalOutcome::Value(ModelValue::FloatingPointExact { exponent: e, significand: f, .. })
            if *e == BigUint::from(128u8) && *f == fraction));
    }
}

#[test]
fn fp_round_integral_exact_dense_carry_needs_no_fraction_output() {
    let mut terms = TermStore::new();
    let sb = 1 << 20;
    let x = terms.mk_var("dense", Sort::FloatingPoint(8, sb));
    let fraction = (BigUint::from(1u8) << (sb - 2)) + 1u8;
    let model = StubModel::new().with(x, exact(false, 127u8.into(), fraction, 8, sb));
    let root = rounded(&mut terms, x, "RNE");
    assert!(matches!(evaluate_term(&terms, &model, root),
        EvalOutcome::Value(ModelValue::FloatingPointExact { exponent, significand, .. })
        if *exponent == BigUint::from(128u8) && significand.bits() == 0));
}

#[test]
fn fp_round_integral_exact_sparse_huge_and_tiny_overflow() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("large", Sort::FloatingPoint(256, 1 << 20));
    let e = (BigUint::from(1u8) << 255usize) + (BigUint::from(1u8) << 64usize);
    let original = exact(true, e.clone(), 1u8.into(), 256, 1 << 20);
    let model = StubModel::new().with(x, original);
    let root = rounded(&mut terms, x, "RNE");
    assert!(matches!(evaluate_term(&terms, &model, root),
        EvalOutcome::Value(ModelValue::FloatingPointExact { sign: true, exponent, significand, .. })
        if *exponent == e && *significand == BigUint::from(1u8)));

    let tiny = terms.mk_var("tiny", Sort::FloatingPoint(2, 4));
    let root = rounded(&mut terms, tiny, "RNE");
    let model = StubModel::new().with(tiny, exact(false, 2u8.into(), 7u8.into(), 2, 4));
    assert!(matches!(evaluate_term(&terms, &model, root),
        EvalOutcome::Value(ModelValue::FloatingPointExact { exponent, significand, .. })
        if *exponent == BigUint::from(3u8) && significand.bits() == 0));
    let model = StubModel::new().with(tiny, exact(true, 0u8.into(), 3u8.into(), 2, 4));
    assert!(matches!(evaluate_term(&terms, &model, root),
        EvalOutcome::Value(ModelValue::FloatingPointExact { sign: true, exponent, significand, .. })
        if exponent.bits() == 0 && significand.bits() == 0));
}
