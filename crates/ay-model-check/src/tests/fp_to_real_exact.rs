// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_bigint::BigUint;

fn exact(sign: bool, exponent: u32, fraction: BigUint, eb: u32, sb: u32) -> ModelValue {
    ModelValue::floating_point_exact(sign, exponent.into(), fraction, eb, sb).unwrap()
}

#[test]
fn fp_to_real_exact_preserves_high_and_low_bits_and_rejects_wrong_reals() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    let converted = app(&mut terms, "fp.to_real", &[x], Sort::Real);
    let fraction = (BigUint::from(1u8) << 198usize) + BigUint::from(1u8);
    let denominator = BigInt::from(1u8) << 199usize;
    let expected = BigRational::new((BigInt::from(3u8) << 198usize) + 1, denominator);
    for negative in [false, true] {
        let model = StubModel::new().with(x, exact(negative, 127, fraction.clone(), 8, 200));
        let want = if negative {
            -&expected
        } else {
            expected.clone()
        };
        let real = terms.mk_rational(want.clone());
        let claim = app(&mut terms, "=", &[converted, real], Sort::Bool);
        assert_confirmed(&verdict(&terms, &model, &[claim]));
        let truncated =
            terms.mk_rational(BigRational::new(int(if negative { -3 } else { 3 }), int(2)));
        let wrong = app(&mut terms, "=", &[converted, truncated], Sort::Bool);
        assert_violates(&verdict(&terms, &model, &[wrong]));
        assert!(matches!(evaluate_term(&terms, &model, converted),
            EvalOutcome::Value(ModelValue::Real(value)) if value == want));
    }
}

#[test]
fn fp_to_real_exact_subnormal_signed_zero_and_extreme_formats() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    let converted = app(&mut terms, "fp.to_real", &[x], Sort::Real);
    for negative in [false, true] {
        let model = StubModel::new().with(x, exact(negative, 0, 1u8.into(), 8, 200));
        let expected = BigRational::new(
            int(if negative { -1 } else { 1 }),
            BigInt::from(1u8) << 325usize,
        );
        assert!(matches!(evaluate_term(&terms, &model, converted),
            EvalOutcome::Value(ModelValue::Real(value)) if value == expected));
        let model = StubModel::new().with(x, exact(negative, 0, 0u8.into(), 8, 200));
        assert!(matches!(evaluate_term(&terms, &model, converted),
            EvalOutcome::Value(ModelValue::Real(value)) if value == BigRational::from_integer(int(0))));
    }
    let huge = terms.mk_var("huge", Sort::FloatingPoint(u32::MAX, 200));
    let huge_real = app(&mut terms, "fp.to_real", &[huge], Sort::Real);
    let model = StubModel::new().with(huge, exact(false, 1, 1u8.into(), u32::MAX, 200));
    assert!(matches!(
        evaluate_term(&terms, &model, huge_real),
        EvalOutcome::Unevaluable(_)
    ));
    let sparse = terms.mk_var("sparse", Sort::FloatingPoint(2, u32::MAX));
    let sparse_real = app(&mut terms, "fp.to_real", &[sparse], Sort::Real);
    let model = StubModel::new().with(sparse, exact(false, 0, 1u8.into(), 2, u32::MAX));
    assert!(matches!(
        evaluate_term(&terms, &model, sparse_real),
        EvalOutcome::Unevaluable(_)
    ));
    let wrong = StubModel::new().with(x, exact(false, 127, 1u8.into(), 8, 201));
    assert!(matches!(
        evaluate_term(&terms, &wrong, converted),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn fp_to_real_exact_sparse_precision_normalizes_before_dense_allocation() {
    struct Owner {
        x: TermId,
        value: ModelValue,
        used: Cell<usize>,
        limit: usize,
    }
    impl ModelView for Owner {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            (term == self.x).then(|| self.value.clone())
        }
        fn charge_functional_array_work(&self, work: usize) -> Result<(), String> {
            let used = self
                .used
                .get()
                .checked_add(work)
                .ok_or("original work overflow")?;
            self.used.set(used);
            if used > self.limit {
                Err("original owner work exhausted".into())
            } else {
                Ok(())
            }
        }
    }
    let mut terms = TermStore::new();
    let sb = 1 << 20;
    let x = terms.mk_var("wide_one", Sort::FloatingPoint(8, sb));
    let real = app(&mut terms, "fp.to_real", &[x], Sort::Real);
    for negative in [false, true] {
        let model = Owner {
            x,
            value: exact(negative, 127, 0u8.into(), 8, sb),
            used: Cell::new(0),
            limit: 4096,
        };
        assert!(matches!(evaluate_term(&terms, &model, real),
            EvalOutcome::Value(ModelValue::Real(value)) if value == BigRational::from_integer(int(if negative { -1 } else { 1 }))));
        assert!(
            model.used.get() > 0 && model.used.get() < 4096,
            "original occupied input and reduced result are cheap, despite declared precision"
        );

        let fraction = BigUint::from(1u8) << (sb - 2) as usize;
        let model = Owner {
            x,
            value: exact(negative, 127, fraction, 8, sb),
            used: Cell::new(0),
            limit: MODEL_DATA_WORK_LIMIT,
        };
        let want = BigRational::new(int(if negative { -3 } else { 3 }), int(2));
        assert!(
            matches!(evaluate_term(&terms, &model, real), EvalOutcome::Value(ModelValue::Real(value)) if value == want)
        );
        assert!(
            model.used.get() >= (sb as usize - 1).div_ceil(8),
            "normalization must still pay the actual occupied fraction scan"
        );
    }
    let subnormal = terms.mk_var("wide_half", Sort::FloatingPoint(2, sb));
    let half = app(&mut terms, "fp.to_real", &[subnormal], Sort::Real);
    let fraction = BigUint::from(1u8) << (sb - 2) as usize;
    let model = StubModel::new().with(subnormal, exact(false, 0, fraction, 2, sb));
    assert!(
        matches!(evaluate_term(&terms, &model, half), EvalOutcome::Value(ModelValue::Real(value)) if value == BigRational::new(int(1), int(2)))
    );

    // The low bit forbids cancellation. Refusing its genuinely huge rational
    // is mandatory; returning the nearby integer would lose model data.
    let model = StubModel::new().with(x, exact(false, 127, 1u8.into(), 8, sb));
    assert!(matches!(
        evaluate_term(&terms, &model, real),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn fp_to_real_exact_original_owner_can_refuse_or_cancel_before_dense_work() {
    struct Owner {
        x: TermId,
        value: ModelValue,
        cancel: bool,
        stopped: Cell<bool>,
    }
    impl ModelView for Owner {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            (term == self.x).then(|| self.value.clone())
        }
        fn functional_array_interrupted(&self) -> bool {
            self.stopped.get()
        }
        fn charge_functional_array_work(&self, work: usize) -> Result<(), String> {
            if work > 100 {
                self.stopped.set(true);
                if !self.cancel {
                    return Err("original owner refuses dyadic conversion".into());
                }
            }
            Ok(())
        }
    }
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    let real = app(&mut terms, "fp.to_real", &[x], Sort::Real);
    for cancel in [false, true] {
        let owner = Owner {
            x,
            value: exact(false, 127, 1u8.into(), 8, 200),
            cancel,
            stopped: Cell::new(false),
        };
        assert!(matches!(
            evaluate_term(&terms, &owner, real),
            EvalOutcome::Unevaluable(_)
        ));
        assert!(
            owner.stopped.get(),
            "actual original conversion admission was consulted"
        );
    }
}

#[test]
fn fp_to_real_exact_nonfinite_choices_keep_sort_and_congruence() {
    struct Choices {
        leaves: StubModel,
        first: TermId,
        second: TermId,
        disagree: bool,
        wrong_sort: bool,
    }
    impl ModelView for Choices {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            self.leaves.leaf_value(term)
        }
        fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
            if term != self.first && term != self.second {
                return None;
            }
            if self.wrong_sort {
                return Some(ModelValue::Bool(false));
            }
            Some(ModelValue::Real(BigRational::from_integer(int(
                if term == self.second && self.disagree {
                    8
                } else {
                    7
                },
            ))))
        }
    }
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("nonfinite_x", sort.clone());
    let y = terms.mk_var("nonfinite_y", sort);
    let a = app(&mut terms, "fp.to_real", &[x], Sort::Real);
    let b = app(&mut terms, "fp.to_real", &[y], Sort::Real);
    let equal = app(&mut terms, "=", &[a, b], Sort::Bool);
    let seven = terms.mk_rational(BigRational::from_integer(int(7)));
    let eight = terms.mk_rational(BigRational::from_integer(int(8)));
    let first_choice = app(&mut terms, "=", &[a, seven], Sort::Bool);
    let conflicting_choice = app(&mut terms, "=", &[b, eight], Sort::Bool);
    for nan in [false, true] {
        let left = exact(false, 255, BigUint::from(u8::from(nan)), 8, 200);
        let right = if nan {
            exact(true, 255, BigUint::from(1u8) << 198usize, 8, 200)
        } else {
            left.clone()
        };
        let mut model = Choices {
            leaves: StubModel::new().with(x, left).with(y, right),
            first: a,
            second: b,
            disagree: false,
            wrong_sort: false,
        };
        assert_confirmed(&verdict(&terms, &model, &[equal]));
        model.disagree = true;
        // A graph hit deliberately keeps the first selected value; a second
        // raw application pin does not override that functional interpretation.
        // The conflicting actual assertion must therefore be false.
        assert_violates(&verdict(
            &terms,
            &model,
            &[first_choice, conflicting_choice],
        ));
        model.disagree = false;
        model.wrong_sort = true;
        assert!(matches!(
            evaluate_term(&terms, &model, a),
            EvalOutcome::Unevaluable(_)
        ));
    }
}
