// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use num_bigint::BigUint;
use std::cell::Cell;

fn exact(sign: bool, exponent: u32, fraction: BigUint, eb: u32, sb: u32) -> ModelValue {
    ModelValue::floating_point_exact(sign, exponent.into(), fraction, eb, sb).unwrap()
}

#[test]
fn ieee_199_bit_fields_are_computed_independently_and_preserve_both_ends() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    let ieee = app(&mut terms, "fp.to_ieee_bv", &[x], Sort::bitvec(208));
    let fraction = (BigUint::from(1u8) << 198usize) | BigUint::from(1u8);
    for (negative, exponent, fraction) in [
        (true, 127u32, fraction),
        (false, 0, BigUint::from(1u8)),
        (true, 0, BigUint::from(0u8)),
        (false, 255, BigUint::from(0u8)),
    ] {
        let value = exact(negative, exponent, fraction.clone(), 8, 200);
        let expected = BigInt::from(fraction)
            | (BigInt::from(exponent) << 199usize)
            | (BigInt::from(u8::from(negative)) << 207usize);
        let model = StubModel::new()
            .with(x, value)
            .with(ieee, ModelValue::bitvec(int(0), 208));
        assert!(matches!(evaluate_term(&terms, &model, ieee),
            EvalOutcome::Value(ModelValue::BitVec { width: 208, value }) if value == expected));
        let wrong = terms.mk_bitvec(&expected ^ int(1), 208);
        let assertion = app(&mut terms, "=", &[ieee, wrong], Sort::Bool);
        assert_violates(&verdict(&terms, &model, &[assertion]));
    }
    let malformed = app(&mut terms, "fp.to_ieee_bv", &[x], Sort::bitvec(207));
    assert!(matches!(
        evaluate_term(
            &terms,
            &StubModel::new().with(x, exact(false, 127, BigUint::from(1u8), 8, 200)),
            malformed
        ),
        EvalOutcome::Unevaluable(_)
    ));
}

struct EncodingPin {
    input: TermId,
    value: ModelValue,
    encoding: ModelValue,
}
impl ModelView for EncodingPin {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        (term == self.input).then(|| self.value.clone())
    }
    fn uf_app_value_at(&self, _: TermId, _: &[ModelValue]) -> Option<ModelValue> {
        Some(self.encoding.clone())
    }
}

#[test]
fn wide_nan_adopts_only_a_same_format_nan_encoding() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("nan", Sort::FloatingPoint(8, 200));
    let ieee = app(&mut terms, "fp.to_ieee_bv", &[x], Sort::bitvec(208));
    let exponent = BigInt::from(255) << 199usize;
    for (bits, width, valid) in [
        (&exponent | int(1), 208, true),
        (
            &exponent | (int(1) << 207usize) | (int(1) << 198usize),
            208,
            true,
        ),
        (int(0), 208, false),
        (exponent.clone(), 208, false),
        (&exponent | int(1), 209, false),
        (int(-1), 208, false),
        ((int(1) << 208usize) | &exponent | int(1), 208, false),
    ] {
        let model = EncodingPin {
            input: x,
            value: exact(false, 255, BigUint::from(1u8), 8, 200),
            // Preserve malicious data rather than normalizing it in the fixture.
            encoding: ModelValue::BitVec {
                value: bits.clone(),
                width,
            },
        };
        let outcome = evaluate_term(&terms, &model, ieee);
        if valid {
            assert!(
                matches!(outcome, EvalOutcome::Value(ModelValue::BitVec { width: 208, value }) if value == bits)
            );
        } else {
            assert!(matches!(outcome, EvalOutcome::Unevaluable(_)));
        }
    }
}

#[test]
fn sparse_declared_width_stays_sparse_but_dense_output_and_owner_refusal_stop() {
    let mut terms = TermStore::new();
    let sb = u32::MAX - 2;
    let x = terms.mk_var("sparse", Sort::FloatingPoint(2, sb));
    let ieee = app(&mut terms, "fp.to_ieee_bv", &[x], Sort::bitvec(u32::MAX));
    let sparse = exact(false, 0, BigUint::from(1u8), 2, sb);
    assert!(
        matches!(evaluate_term(&terms, &StubModel::new().with(x, sparse.clone()), ieee),
        EvalOutcome::Value(ModelValue::BitVec { width: u32::MAX, value }) if value == int(1))
    );
    for value in [
        exact(true, 0, 0u8.into(), 2, sb),
        exact(false, 1, 0u8.into(), 2, sb),
    ] {
        assert!(matches!(
            evaluate_term(&terms, &StubModel::new().with(x, value), ieee),
            EvalOutcome::Unevaluable(_)
        ));
    }
    struct Owner {
        input: TermId,
        value: ModelValue,
        refused_output: Cell<bool>,
    }
    impl ModelView for Owner {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            (term == self.input).then(|| self.value.clone())
        }
        fn charge_functional_array_work(&self, work: usize) -> Result<(), String> {
            // Permit small shared field reads, but refuse the requested live
            // packing/output envelope before the conversion allocates it.
            if work > 64 {
                self.refused_output.set(true);
                return Err("original owner refuses output work".into());
            }
            Ok(())
        }
    }
    let owner = Owner {
        input: x,
        value: sparse,
        refused_output: Cell::new(false),
    };
    assert!(matches!(
        evaluate_term(&terms, &owner, ieee),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(owner.refused_output.get());
}

#[test]
fn owner_cancellation_during_output_admission_cannot_publish_an_encoding() {
    struct Cancels {
        input: TermId,
        value: ModelValue,
        cancelled: Cell<bool>,
    }
    impl ModelView for Cancels {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            (term == self.input).then(|| self.value.clone())
        }
        fn functional_array_interrupted(&self) -> bool {
            self.cancelled.get()
        }
        fn charge_functional_array_work(&self, work: usize) -> Result<(), String> {
            if work > 64 {
                self.cancelled.set(true);
            }
            Ok(())
        }
    }
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 200));
    let ieee = app(&mut terms, "fp.to_ieee_bv", &[x], Sort::bitvec(208));
    let owner = Cancels {
        input: x,
        value: exact(false, 127, 1u8.into(), 8, 200),
        cancelled: Cell::new(false),
    };
    assert!(matches!(
        evaluate_term(&terms, &owner, ieee),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(owner.cancelled.get());
}
