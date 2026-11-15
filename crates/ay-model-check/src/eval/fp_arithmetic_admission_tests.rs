// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::Evaluator;
use crate::{EvalOutcome, ModelValue, ModelView};
use ay_core::{Sort, Symbol, TermId, TermStore};
use std::cell::Cell;

fn one(sb: u32) -> ModelValue {
    ModelValue::floating_point_exact(false, 127u8.into(), 0u8.into(), 8, sb).unwrap()
}
struct Values(ModelValue);
impl ModelView for Values {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        Some(self.0.clone())
    }
}
fn operations(terms: &mut TermStore) -> (TermId, TermId) {
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    (
        terms.mk_app(Symbol::named("fp.add"), vec![rm, x, x], sort.clone()),
        terms.mk_app(Symbol::named("fp.add"), vec![rm, y, y], sort),
    )
}

#[test]
fn exact_fp_remainder_special_fields_do_not_materialize_unneeded_dyadics() {
    use std::sync::Arc;
    let exact = |sign, exponent: u64, fraction: u8, eb| {
        ModelValue::floating_point_exact(sign, exponent.into(), fraction.into(), eb, 200).unwrap()
    };
    let huge = exact(true, u64::from(u32::MAX - 1), 1, 32);
    let infinity = exact(false, u64::from(u32::MAX), 0, 32);
    let nan = exact(false, u64::from(u32::MAX), 1, 32);
    let positive_zero = exact(false, 0, 0, 32);
    let negative_zero = exact(true, 0, 0, 32);
    assert!(crate::fp_exact::real_plan(&huge).is_err());
    for dividend in [&huge, &positive_zero, &negative_zero] {
        let operands = [dividend.clone(), infinity.clone()];
        let result =
            crate::fp_exact::arithmetic_plan("fp.rem", crate::fp::RoundingMode::Rne, &operands)
                .unwrap()
                .materialize()
                .unwrap();
        assert!(crate::fp_exact::same_element(dividend, &result).unwrap());
        let (
            ModelValue::FloatingPointExact {
                exponent: a,
                significand: b,
                ..
            },
            ModelValue::FloatingPointExact {
                exponent: c,
                significand: d,
                ..
            },
        ) = (dividend, &result)
        else {
            panic!("exact dividend DATA was not retained")
        };
        assert!(Arc::ptr_eq(a, c) && Arc::ptr_eq(b, d));
    }
    for (a, b) in [
        (&nan, &huge),
        (&huge, &nan),
        (&infinity, &huge),
        (&huge, &positive_zero),
        (&positive_zero, &negative_zero),
    ] {
        let operands = [a.clone(), b.clone()];
        let result =
            crate::fp_exact::arithmetic_plan("fp.rem", crate::fp::RoundingMode::Rne, &operands)
                .unwrap()
                .materialize()
                .unwrap();
        assert!(crate::fp_exact::same_element(&nan, &result).unwrap());
    }
    for zero in [&positive_zero, &negative_zero] {
        let operands = [zero.clone(), huge.clone()];
        let result =
            crate::fp_exact::arithmetic_plan("fp.rem", crate::fp::RoundingMode::Rne, &operands)
                .unwrap()
                .materialize()
                .unwrap();
        assert!(crate::fp_exact::same_element(zero, &result).unwrap());
    }
    let malformed = ModelValue::FloatingPointExact {
        sign: false,
        exponent: Arc::new((1u64 << 32).into()),
        significand: Arc::new(0u8.into()),
        exponent_bits: 32,
        significand_bits: 200,
    };
    for bad in [malformed, exact(false, 127, 0, 8)] {
        assert!(crate::fp_exact::arithmetic_plan(
            "fp.rem",
            crate::fp::RoundingMode::Rne,
            &[nan.clone(), bad]
        )
        .is_err());
    }
}

#[test]
fn exact_fp_callback_cannot_disable_storage_admission_or_publish_after_activation_change() {
    struct Owner {
        enabled: Cell<bool>,
        refused: Cell<bool>,
        storage_calls: Cell<usize>,
        plan_work: usize,
        reject_storage: bool,
    }
    impl ModelView for Owner {
        fn has_evaluation_admission(&self) -> bool {
            self.enabled.get()
        }
        fn refuse_evaluation_work(&self, _: &str) {
            self.refused.set(true);
        }
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(one(200))
        }
        fn charge_exact_fp_work(&self, work: usize) -> Result<(), String> {
            if work == self.plan_work {
                self.enabled.set(false);
            }
            Ok(())
        }
        fn admit_evaluation_work(&self, _: usize, bytes: usize) -> Result<(), String> {
            if !self.enabled.get() && bytes > 0 {
                self.storage_calls.set(self.storage_calls.get() + 1);
                if self.reject_storage {
                    return Err("original storage owner refused".into());
                }
            }
            Ok(())
        }
    }
    let mut terms = TermStore::new();
    let (addition, _) = operations(&mut terms);
    let values = [one(200), one(200)];
    let plan =
        crate::fp_exact::arithmetic_plan("fp.add", crate::fp::RoundingMode::Rne, &values).unwrap();
    for reject_storage in [false, true] {
        let owner = Owner {
            enabled: Cell::new(true),
            refused: Cell::new(false),
            storage_calls: Cell::new(0),
            plan_work: plan.work,
            reject_storage,
        };
        let evaluator = Evaluator::new(&terms, &owner);
        assert!(evaluator.eval(addition, 0).is_err());
        assert_eq!(owner.storage_calls.get(), 1);
        assert!(owner.refused.get());
        assert!(evaluator.eval(addition, 0).is_err());
        assert_eq!(owner.storage_calls.get(), 1, "refusal stays terminal");
    }
}

#[test]
fn wide_fp_sqrt_retains_cumulative_admission_and_original_owner() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let a = terms.mk_app(Symbol::named("fp.sqrt"), vec![rm, x], sort.clone());
    let b = terms.mk_app(Symbol::named("fp.sqrt"), vec![rm, y], sort);
    let values = [one(200)];
    let plan =
        crate::fp_exact::arithmetic_plan("fp.sqrt", crate::fp::RoundingMode::Rne, &values).unwrap();
    let model = Values(one(200));
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.plan_bytes_left.set(plan.storage);
    assert!(evaluator.eval(a, 0).is_ok());
    assert!(
        evaluator.eval(b, 0).is_err(),
        "storage is shared across roots"
    );
    assert!(
        evaluator.eval(b, 0).is_err(),
        "refusal cannot refund storage"
    );
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.functional_work_left.set(plan.work - 1);
    assert!(evaluator.eval(a, 0).is_err());
    assert!(Evaluator::new(&terms, &Values(one(201)))
        .eval(a, 0)
        .is_err());
    struct Owner {
        boundaries: Cell<usize>,
        stop: usize,
    }
    impl ModelView for Owner {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(one(200))
        }
        fn charge_exact_fp_work(&self, work: usize) -> Result<(), String> {
            if work > 10_000 {
                self.boundaries.set(1);
            } else if work == 1 && self.boundaries.get() > 0 {
                let n = self.boundaries.get() + 1;
                self.boundaries.set(n);
                if n == self.stop {
                    return Err("original square-root owner refused".into());
                }
            }
            Ok(())
        }
    }
    for stop in [2, 3] {
        let owner = Owner {
            boundaries: Cell::new(0),
            stop,
        };
        assert!(matches!(
            crate::evaluate_term(&terms, &owner, a),
            EvalOutcome::Unevaluable(_)
        ));
        assert_eq!(
            owner.boundaries.get(),
            stop,
            "refuse before or after the kernel"
        );
    }
    assert!(matches!(
        crate::fp_exact::arithmetic_plan("fp.sqrt", crate::fp::RoundingMode::Rne, &[one(1 << 20)]),
        Ok(large) if large.work > crate::MODEL_DATA_WORK_LIMIT
    ));
}

#[test]
fn wide_fp_arithmetic_retains_original_cumulative_storage_and_work() {
    let mut terms = TermStore::new();
    let (a, b) = operations(&mut terms);
    let values = [one(200), one(200)];
    let storage = crate::fp_exact::arithmetic_plan("fp.add", crate::fp::RoundingMode::Rne, &values)
        .unwrap()
        .storage;
    let model = Values(one(200));
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.plan_bytes_left.set(storage);
    let before = evaluator.functional_work_left.get();
    assert!(evaluator.eval(a, 0).is_ok());
    let spent = before - evaluator.functional_work_left.get();
    assert!(spent > 0);
    assert!(
        evaluator.eval(b, 0).is_err(),
        "same original storage cannot be renewed"
    );
    assert!(
        evaluator.eval(b, 0).is_err(),
        "a refusal must not refund the original plan"
    );
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.functional_work_left.set(spent);
    assert!(evaluator.eval(a, 0).is_ok());
    assert!(
        evaluator.eval(b, 0).is_err(),
        "different operands share original work"
    );
    assert!(Evaluator::new(&terms, &model).eval(b, 0).is_ok());
}

#[test]
fn wide_fp_remainder_spends_the_original_work_and_storage_across_operands() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("remainder_x", sort.clone());
    let y = terms.mk_var("remainder_y", sort.clone());
    let a = terms.mk_app(Symbol::named("fp.rem"), [x, x], sort.clone());
    let b = terms.mk_app(Symbol::named("fp.rem"), [y, y], sort);
    let values = [one(200), one(200)];
    let storage = crate::fp_exact::arithmetic_plan("fp.rem", crate::fp::RoundingMode::Rne, &values)
        .unwrap()
        .storage;
    let model = Values(one(200));
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.plan_bytes_left.set(storage);
    let before = evaluator.functional_work_left.get();
    assert!(evaluator.eval(a, 0).is_ok());
    let spent = before - evaluator.functional_work_left.get();
    assert!(spent > 0);
    assert!(evaluator.eval(b, 0).is_err());
    assert!(evaluator.eval(b, 0).is_err());
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.functional_work_left.set(spent);
    assert!(evaluator.eval(a, 0).is_ok());
    assert!(evaluator.eval(b, 0).is_err());
    assert!(Evaluator::new(&terms, &model).eval(b, 0).is_ok());
}

#[test]
fn wide_fp_arithmetic_checks_original_cancel_before_and_after_materialization() {
    struct Owner {
        large: Cell<bool>,
        tiny: Cell<usize>,
        stop: usize,
        cancelled: Cell<bool>,
    }
    impl ModelView for Owner {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(one(200))
        }
        fn exact_fp_interrupted(&self) -> bool {
            self.cancelled.get()
        }
        fn charge_exact_fp_work(&self, work: usize) -> Result<(), String> {
            if work > 10_000 {
                self.large.set(true);
            }
            if self.large.get() && work == 1 {
                self.tiny.set(self.tiny.get() + 1);
                if self.tiny.get() == self.stop {
                    self.cancelled.set(true);
                }
            }
            Ok(())
        }
    }
    let mut terms = TermStore::new();
    let (a, _) = operations(&mut terms);
    for stop in [1, 2] {
        let model = Owner {
            large: Cell::new(false),
            tiny: Cell::new(0),
            stop,
            cancelled: Cell::new(false),
        };
        assert!(matches!(
            crate::evaluate_term(&terms, &model, a),
            EvalOutcome::Unevaluable(_)
        ));
        assert_eq!(
            model.tiny.get(),
            stop,
            "must reach the intended original-owner boundary"
        );
    }
    struct Refused;
    impl ModelView for Refused {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(one(200))
        }
        fn charge_exact_fp_work(&self, work: usize) -> Result<(), String> {
            if work > 10_000 {
                Err("original owner refuses arithmetic".into())
            } else {
                Ok(())
            }
        }
    }
    assert!(matches!(
        crate::evaluate_term(&terms, &Refused, a),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn wide_fp_arithmetic_declines_unadmitted_dense_precision_and_wrong_sorts() {
    let mut terms = TermStore::new();
    let huge = Sort::FloatingPoint(8, 1 << 20);
    let x = terms.mk_var("x", huge.clone());
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let add = terms.mk_app(Symbol::named("fp.add"), vec![rm, x, x], huge);
    assert!(matches!(
        crate::evaluate_term(&terms, &Values(one(1 << 20)), add),
        EvalOutcome::Unevaluable(_)
    ));
    let (a, _) = operations(&mut terms);
    assert!(matches!(
        crate::evaluate_term(&terms, &Values(one(201)), a),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn wide_fp_arithmetic_fresh_evaluators_cannot_renew_original_owner_work() {
    struct Owner {
        used: Cell<usize>,
        limit: usize,
    }
    impl ModelView for Owner {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(one(200))
        }
        fn charge_exact_fp_work(&self, work: usize) -> Result<(), String> {
            let used = self
                .used
                .get()
                .checked_add(work)
                .ok_or("original owner work overflow")?;
            self.used.set(used);
            if used > self.limit {
                Err("original owner work exhausted".into())
            } else {
                Ok(())
            }
        }
    }
    let mut terms = TermStore::new();
    let (a, b) = operations(&mut terms);
    let measured = Owner {
        used: Cell::new(0),
        limit: usize::MAX,
    };
    assert!(matches!(
        crate::evaluate_term(&terms, &measured, a),
        EvalOutcome::Value(_)
    ));
    let model = Owner {
        used: Cell::new(0),
        limit: measured.used.get(),
    };
    assert!(matches!(
        crate::evaluate_term(&terms, &model, a),
        EvalOutcome::Value(_)
    ));
    for _ in 0..2 {
        assert!(
            matches!(
                crate::evaluate_term(&terms, &model, b),
                EvalOutcome::Unevaluable(_)
            ),
            "a new evaluator cannot mint another original owner's allowance"
        );
    }
}
