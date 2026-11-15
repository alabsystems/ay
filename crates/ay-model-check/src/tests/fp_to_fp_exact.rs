// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use num_bigint::BigUint;
use num_traits::{One, Zero};

fn operation(terms: &mut TermStore, x: TermId, mode: &str, name: &str, eb: u32, sb: u32) -> TermId {
    let rm = terms.mk_app(
        Symbol::named(mode),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    terms.mk_app(
        Symbol::Indexed(name.into(), vec![eb, sb]),
        &[rm, x],
        Sort::FloatingPoint(eb, sb),
    )
}
fn exact(sign: bool, exponent: u64, fraction: BigUint) -> ModelValue {
    ModelValue::floating_point_exact(sign, exponent.into(), fraction, 8, 200).unwrap()
}

#[test]
fn fp_to_fp_exact_numeric_halfway_all_modes_and_signs() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let unit = BigInt::one() << 201usize;
    // 1 + half an SB200 ulp, and its immediate rational neighbors.
    for delta in [-1, 0, 1] {
        for negative in [false, true] {
            let numerator: BigInt = &unit + 2 + delta;
            let rational =
                BigRational::new(if negative { -numerator } else { numerator }, unit.clone());
            let model = StubModel::new().with(x, ModelValue::Real(rational));
            for mode in ["RNE", "RNA", "RTZ", "RTP", "RTN"] {
                let up = match mode {
                    "RNE" => delta > 0,
                    "RNA" => delta >= 0,
                    "RTP" => !negative,
                    "RTN" => negative,
                    _ => false,
                };
                let result = operation(&mut terms, x, mode, "to_fp", 8, 200);
                let EvalOutcome::Value(actual) = evaluate_term(&terms, &model, result) else {
                    panic!("conversion refused")
                };
                assert!(
                    crate::fp::same_element(&actual, &exact(negative, 127, u8::from(up).into())),
                    "{mode} {delta} {negative}"
                );
            }
        }
    }
}

#[test]
fn fp_to_fp_exact_integer_signed_unsigned_and_sparse_word() {
    let mut terms = TermStore::new();
    let integer = terms.mk_var("i", Sort::Int);
    let bits = terms.mk_var("b", Sort::bitvec(8));
    let sparse = terms.mk_var("s", Sort::bitvec(1 << 20));
    let model = StubModel::new()
        .with(integer, ModelValue::Int(4.into()))
        .with(
            bits,
            ModelValue::BitVec {
                value: 255.into(),
                width: 8,
            },
        )
        .with(
            sparse,
            ModelValue::BitVec {
                value: 1.into(),
                width: 1 << 20,
            },
        );
    for (input, name, expected) in [
        (integer, "to_fp", exact(false, 129, 0u8.into())),
        (bits, "to_fp", exact(true, 127, 0u8.into())),
        (
            bits,
            "to_fp_unsigned",
            exact(false, 134, BigUint::from(127u8) << 192usize),
        ),
        (sparse, "to_fp", exact(false, 127, 0u8.into())),
    ] {
        let result = operation(&mut terms, input, "RNE", name, 8, 200);
        assert!(
            matches!(evaluate_term(&terms,&model,result), EvalOutcome::Value(actual) if crate::fp::same_element(&actual,&expected))
        );
    }
    let invalid = operation(&mut terms, integer, "RNE", "to_fp_unsigned", 8, 200);
    assert!(matches!(
        evaluate_term(&terms, &model, invalid),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn fp_to_fp_exact_format_conversion_preserves_specials_and_low_bits() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    for value in [
        exact(true, 0, 0u8.into()),
        exact(false, 255, 0u8.into()),
        exact(true, 255, 0u8.into()),
        exact(false, 255, 1u8.into()),
        exact(false, 127, (BigUint::from(1u8) << 198usize) + 1u8),
    ] {
        let model = StubModel::new().with(x, value.clone());
        let result = operation(&mut terms, x, "RNE", "to_fp", 8, 200);
        assert!(
            matches!(evaluate_term(&terms,&model,result),EvalOutcome::Value(actual) if crate::fp::same_element(&actual,&value))
        );
    }
    let source = exact(false, 127, (BigUint::from(1u8) << 198usize) + 1u8);
    let model = StubModel::new().with(x, source);
    let result = operation(&mut terms, x, "RNE", "to_fp", 11, 220);
    let expected = ModelValue::floating_point_exact(
        false,
        1023u16.into(),
        (BigUint::from(1u8) << 218usize) + (BigUint::from(1u8) << 20usize),
        11,
        220,
    )
    .unwrap();
    assert!(
        matches!(evaluate_term(&terms,&model,result),EvalOutcome::Value(actual) if crate::fp::same_element(&actual,&expected))
    );
}

#[test]
fn fp_to_fp_exact_original_owner_refusal_cumulative_and_cancel() {
    use std::cell::Cell;
    struct Owner {
        input: TermId,
        work: Cell<usize>,
        limit: Cell<usize>,
        cancel: Cell<bool>,
        interrupted: Cell<bool>,
    }
    impl ModelView for Owner {
        fn has_evaluation_admission(&self) -> bool {
            true
        }
        fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
            (t == self.input).then(|| ModelValue::Int(4.into()))
        }
        fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
            let total = self.work.get().checked_add(work).ok_or("overflow")?;
            self.work.set(total);
            if total > self.limit.get() {
                return Err("original conversion owner refused".into());
            }
            if bytes > 1024 && self.cancel.get() {
                self.interrupted.set(true);
            }
            Ok(())
        }
        fn functional_array_interrupted(&self) -> bool {
            self.interrupted.get()
        }
    }
    let mut terms = TermStore::new();
    let x = terms.mk_var("owned", Sort::Int);
    let first = operation(&mut terms, x, "RNE", "to_fp", 8, 200);
    let second = operation(&mut terms, x, "RTZ", "to_fp", 8, 200);
    let owner = Owner {
        input: x,
        work: Cell::new(0),
        limit: Cell::new(usize::MAX),
        cancel: Cell::new(false),
        interrupted: Cell::new(false),
    };
    let evaluator = Evaluator::new(&terms, &owner);
    assert!(matches!(evaluator.evaluate(first), EvalOutcome::Value(_)));
    owner.limit.set(owner.work.get());
    assert!(matches!(
        evaluator.evaluate(second),
        EvalOutcome::Unevaluable(_)
    ));
    owner.work.set(0);
    owner.limit.set(usize::MAX);
    owner.cancel.set(true);
    assert!(matches!(
        Evaluator::new(&terms, &owner).evaluate(first),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(owner.interrupted.get());
}

#[test]
fn fp_to_fp_exact_sparse_zero_and_native_carrier_remain_data() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("zero", Sort::Int);
    let model = StubModel::new().with(x, ModelValue::Int(0.into()));
    let wide = operation(&mut terms, x, "RNE", "to_fp", 8, 1 << 20);
    assert!(
        matches!(evaluate_term(&terms,&model,wide),EvalOutcome::Value(ModelValue::FloatingPointExact { exponent,significand,.. }) if exponent.is_zero() && significand.is_zero())
    );
    let narrow = operation(&mut terms, x, "RNE", "to_fp", 8, 24);
    assert!(matches!(
        evaluate_term(&terms, &model, narrow),
        EvalOutcome::Value(ModelValue::FloatingPoint {
            exponent: 0,
            significand: 0,
            ..
        })
    ));
    let wrong = StubModel::new().with(
        x,
        ModelValue::BitVec {
            value: 1.into(),
            width: 8,
        },
    );
    assert!(matches!(
        evaluate_term(&terms, &wrong, narrow),
        EvalOutcome::Unevaluable(_)
    ));
    let malformed = terms.mk_var("bad", Sort::bitvec(8));
    let bad = StubModel::new().with(
        malformed,
        ModelValue::BitVec {
            value: 256.into(),
            width: 8,
        },
    );
    let conversion = operation(&mut terms, malformed, "RNE", "to_fp", 8, 200);
    assert!(matches!(
        evaluate_term(&terms, &bad, conversion),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn fp_to_fp_exact_integer_real_carrier_and_malformed_rational() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("real", Sort::Real);
    let result = operation(&mut terms, x, "RNE", "to_fp", 8, 200);
    let model = StubModel::new().with(x, ModelValue::Int(4.into()));
    assert!(
        matches!(evaluate_term(&terms,&model,result),EvalOutcome::Value(actual) if crate::fp::same_element(&actual,&exact(false,129,0u8.into())))
    );
    for denominator in [0, -1] {
        let malformed = StubModel::new().with(
            x,
            ModelValue::Real(BigRational::new_raw(1.into(), denominator.into())),
        );
        assert!(matches!(
            evaluate_term(&terms, &malformed, result),
            EvalOutcome::Unevaluable(_)
        ));
    }
}
