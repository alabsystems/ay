// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use num_bigint::BigUint;
use num_traits::Zero;
use std::sync::Arc;

fn exact(sign: bool, exponent: BigUint, fraction: BigUint, eb: u32, sb: u32) -> ModelValue {
    ModelValue::floating_point_exact(sign, exponent, fraction, eb, sb).unwrap()
}

#[test]
fn exact_min_max_checks_low_bits_negative_order_and_nan_selection() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let high = BigUint::from(1u8) << 198usize;
    for (negative, low_wins_min) in [(false, true), (true, false)] {
        let low = exact(negative, 127u32.into(), high.clone(), 8, 200);
        let high_value = exact(negative, 127u32.into(), &high + BigUint::from(1u8), 8, 200);
        for name in ["fp.min", "fp.max"] {
            let result = app(&mut terms, name, &[x, y], sort.clone());
            let selected = if low_wins_min == (name == "fp.min") {
                x
            } else {
                y
            };
            let wrong = if selected == x { y } else { x };
            let claim = app(&mut terms, "=", &[result, selected], Sort::Bool);
            let false_claim = app(&mut terms, "=", &[result, wrong], Sort::Bool);
            let model = StubModel::new()
                .with(x, low.clone())
                .with(y, high_value.clone());
            assert_confirmed(&verdict(&terms, &model, &[claim]));
            assert_violates(&verdict(&terms, &model, &[false_claim]));
        }
    }
    let finite = exact(false, 127u32.into(), high, 8, 200);
    let nan = exact(true, 255u32.into(), 1u32.into(), 8, 200);
    for name in ["fp.min", "fp.max"] {
        for args in [[nan.clone(), finite.clone()], [finite.clone(), nan.clone()]] {
            let selected = fp::min_max(name, &args).unwrap().unwrap();
            assert!(fp::same_element(&selected, &finite));
        }
        assert!(fp::min_max(name, &[finite.clone()]).is_err());
        assert!(fp::min_max(
            name,
            &[
                finite.clone(),
                exact(false, 127u32.into(), 0u32.into(), 8, 201)
            ]
        )
        .is_err());
    }
}

#[test]
fn exact_min_max_zero_choice_rejects_nonzero_and_wrong_format() {
    let positive = exact(false, 0u32.into(), 0u32.into(), 8, 200);
    let negative = exact(true, 0u32.into(), 0u32.into(), 8, 200);
    let operands = [positive.clone(), negative.clone()];
    struct Choice {
        inputs: StubModel,
        application: TermId,
        value: ModelValue,
    }
    impl ModelView for Choice {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            self.inputs.leaf_value(term)
        }
        fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
            (term == self.application).then(|| self.value.clone())
        }
    }
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("zero_x", sort.clone());
    let y = terms.mk_var("zero_y", sort.clone());
    for name in ["fp.min", "fp.max"] {
        assert!(fp::min_max_unspecified(name, &operands));
        assert_eq!(
            fp::min_max(name, &operands).unwrap_err(),
            fp::UNDERSPECIFIED
        );
        let application = app(&mut terms, name, &[x, y], sort.clone());
        let claim = app(&mut terms, "fp.isZero", &[application], Sort::Bool);
        for value in &operands {
            let model = Choice {
                inputs: StubModel::new()
                    .with(x, positive.clone())
                    .with(y, negative.clone()),
                application,
                value: value.clone(),
            };
            assert_confirmed(&verdict(&terms, &model, &[claim]));
        }
        for value in [
            exact(false, 127u32.into(), 0u32.into(), 8, 200),
            exact(false, 0u32.into(), 0u32.into(), 8, 201),
        ] {
            let model = Choice {
                inputs: StubModel::new()
                    .with(x, positive.clone())
                    .with(y, negative.clone()),
                application,
                value,
            };
            assert_cannot(&verdict(&terms, &model, &[claim]));
        }
    }
    for allowed in [positive, negative] {
        assert!(fp::check_min_max_choice(&operands, &allowed).is_ok());
    }
    for invalid in [
        exact(false, 127u32.into(), 0u32.into(), 8, 200),
        exact(false, 0u32.into(), 0u32.into(), 8, 201),
        exact(false, 255u32.into(), 1u32.into(), 8, 200),
    ] {
        assert!(fp::check_min_max_choice(&operands, &invalid).is_err());
    }
}

#[test]
fn exact_fp_owner_cancellation_during_accepted_admission_refuses_publication() {
    use std::cell::Cell;
    struct CancelsWhileAccepting {
        value: ModelValue,
        interrupted: Cell<bool>,
    }
    impl ModelView for CancelsWhileAccepting {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(self.value.clone())
        }
        fn functional_array_interrupted(&self) -> bool {
            self.interrupted.get()
        }
        fn charge_functional_array_work(&self, _: usize) -> Result<(), String> {
            self.interrupted.set(true);
            Ok(())
        }
    }
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("cancelling_min_input", sort.clone());
    let model = CancelsWhileAccepting {
        value: exact(
            false,
            127u32.into(),
            (BigUint::from(1u8) << 198usize) + BigUint::from(1u8),
            8,
            200,
        ),
        interrupted: Cell::new(false),
    };
    assert!(matches!(
        evaluate_term(&terms, &model, x),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(model.interrupted.get());
}

#[test]
fn exact_fp_retained_memo_obeys_original_owner_and_fresh_request_recovers() {
    use std::cell::Cell;
    struct Owner {
        value: ModelValue,
        stopped: Cell<bool>,
    }
    impl ModelView for Owner {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(self.value.clone())
        }
        fn functional_array_interrupted(&self) -> bool {
            self.stopped.get()
        }
    }
    let mut terms = TermStore::new();
    let x = terms.mk_var("retained_exact_value", Sort::FloatingPoint(8, 200));
    let owner = Owner {
        value: exact(
            false,
            127u32.into(),
            (BigUint::from(1u8) << 198usize) + BigUint::from(1u8),
            8,
            200,
        ),
        stopped: Cell::new(false),
    };
    let evaluator = Evaluator::new(&terms, &owner);
    assert!(matches!(evaluator.evaluate(x), EvalOutcome::Value(_)));
    owner.stopped.set(true);
    assert!(matches!(evaluator.evaluate(x), EvalOutcome::Unevaluable(_)));
    let fresh = Owner {
        value: owner.value.clone(),
        stopped: Cell::new(false),
    };
    assert!(matches!(
        evaluate_term(&terms, &fresh, x),
        EvalOutcome::Value(_)
    ));
}

#[test]
fn symbolic_199_bit_witness_refutes_high_low_exponent_and_sign_mutations() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("x", sort.clone());
    let fraction = (BigUint::from(1u8) << 198usize) | BigUint::from(1u8);
    let sign = terms.mk_bitvec(BigInt::from(0), 1);
    let exponent = terms.mk_bitvec(BigInt::from(127), 8);
    let stored = terms.mk_bitvec(BigInt::from(fraction.clone()), 199);
    let literal = app(&mut terms, "fp", &[sign, exponent, stored], sort.clone());
    let claim = app(&mut terms, "=", &[x, literal], Sort::Bool);
    let classification = app(&mut terms, "fp.isNormal", &[x], Sort::Bool);
    let shared_exponent = Arc::new(BigUint::from(127u32));
    let shared_fraction = Arc::new(fraction.clone());
    let correct = ModelValue::floating_point_exact_shared(
        false,
        Arc::clone(&shared_exponent),
        Arc::clone(&shared_fraction),
        8,
        200,
    )
    .unwrap();
    let ModelValue::FloatingPointExact {
        exponent: captured_exponent,
        significand,
        ..
    } = &correct
    else {
        panic!("exact data required");
    };
    assert!(Arc::ptr_eq(captured_exponent, &shared_exponent));
    assert!(Arc::ptr_eq(significand, &shared_fraction));
    assert_confirmed(&verdict(
        &terms,
        &StubModel::new().with(x, correct.clone()),
        &[claim],
    ));
    for value in [
        exact(false, 127u32.into(), 1u32.into(), 8, 200),
        exact(false, 127u32.into(), &fraction - BigUint::from(1u8), 8, 200),
        exact(false, 128u32.into(), fraction.clone(), 8, 200),
        exact(true, 127u32.into(), fraction.clone(), 8, 200),
    ] {
        assert_violates(&verdict(&terms, &StubModel::new().with(x, value), &[claim]));
    }
    for (exponent, fraction, sb) in [
        (256u32.into(), fraction.clone(), 200),
        (127u32.into(), BigUint::from(1u8) << 199usize, 200),
        (127u32.into(), fraction.clone(), 201),
    ] {
        let forged = ModelValue::FloatingPointExact {
            sign: false,
            exponent: Arc::new(exponent),
            significand: Arc::new(fraction),
            exponent_bits: 8,
            significand_bits: sb,
        };
        assert_cannot(&verdict(
            &terms,
            &StubModel::new().with(x, forged.clone()),
            &[claim],
        ));
        assert_cannot(&verdict(
            &terms,
            &StubModel::new().with(x, forged),
            &[classification],
        ));
    }
    let wrong_native = ModelValue::FloatingPoint {
        sign: false,
        exponent: 127,
        significand: 1,
        exponent_bits: 8,
        significand_bits: 24,
    };
    assert_cannot(&verdict(
        &terms,
        &StubModel::new().with(x, wrong_native),
        &[classification],
    ));
    struct FalseConstructor(ModelValue);
    impl ModelView for FalseConstructor {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
        fn uf_app_value(&self, _: TermId) -> Option<ModelValue> {
            Some(self.0.clone())
        }
    }
    let malformed = app(&mut terms, "fp", &[sign, exponent], sort.clone());
    let malformed_classification = app(&mut terms, "fp.isNormal", &[malformed], Sort::Bool);
    assert_cannot(&verdict(
        &terms,
        &FalseConstructor(correct.clone()),
        &[malformed_classification],
    ));
    let mode = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let add = app(&mut terms, "fp.add", &[mode, x, x], sort);
    let arithmetic = app(&mut terms, "=", &[add, x], Sort::Bool);
    assert_violates(&verdict(
        &terms,
        &StubModel::new().with(x, correct),
        &[arithmetic],
    ));
}

#[test]
fn exact_ieee_split_classification_and_numeric_order_use_every_fraction_bit() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let fraction = (BigUint::from(1u8) << 198usize) | BigUint::from(1u8);
    let bits = (BigUint::from(127u32) << 199usize) | &fraction;
    let raw = terms.mk_bitvec(BigInt::from(bits), 208);
    let cast = terms.mk_app(Symbol::indexed("to_fp", vec![8, 200]), [raw], sort);
    let equal = app(&mut terms, "=", &[x, cast], Sort::Bool);
    let normal = app(&mut terms, "fp.isNormal", &[x], Sort::Bool);
    let smaller = app(&mut terms, "fp.lt", &[y, x], Sort::Bool);
    let model = StubModel::new()
        .with(x, exact(false, 127u32.into(), fraction.clone(), 8, 200))
        .with(
            y,
            exact(false, 127u32.into(), fraction - BigUint::from(1u8), 8, 200),
        );
    assert_confirmed(&verdict(&terms, &model, &[equal, normal, smaller]));
}

#[test]
fn arbitrary_exponent_nan_and_signed_zero_keep_both_equality_relations() {
    for (a_sign, b_sign, exponent, a_fraction, b_fraction, structural, ieee) in [
        (
            false,
            true,
            (BigUint::from(1u8) << 80usize) - BigUint::from(1u8),
            BigUint::from(1u8),
            BigUint::from(1u8) << 198usize,
            true,
            false,
        ),
        (
            false,
            true,
            BigUint::zero(),
            BigUint::zero(),
            BigUint::zero(),
            false,
            true,
        ),
    ] {
        let mut terms = TermStore::new();
        let sort = Sort::FloatingPoint(80, 200);
        let x = terms.mk_var("x", sort.clone());
        let y = terms.mk_var("y", sort);
        let equality = app(&mut terms, "=", &[x, y], Sort::Bool);
        let numeric = app(&mut terms, "fp.eq", &[x, y], Sort::Bool);
        let distinct = app(&mut terms, "distinct", &[x, y], Sort::Bool);
        let model = StubModel::new()
            .with(x, exact(a_sign, exponent.clone(), a_fraction, 80, 200))
            .with(y, exact(b_sign, exponent, b_fraction, 80, 200));
        for (claim, expected) in [
            (equality, structural),
            (numeric, ieee),
            (distinct, !structural),
        ] {
            let outcome = verdict(&terms, &model, &[claim]);
            if expected {
                assert_confirmed(&outcome);
            } else {
                assert_violates(&outcome);
            }
        }
    }
}

#[test]
fn sparse_declared_formats_do_not_allocate_a_declared_width_mask() {
    let mut terms = TermStore::new();
    let (eb, sb) = (2, u32::MAX - 2);
    let sort = Sort::FloatingPoint(eb, sb);
    let x = terms.mk_var("x", sort.clone());
    let bits = terms.mk_var("bits", Sort::bitvec(u32::MAX));
    let cast = terms.mk_app(Symbol::indexed("to_fp", vec![eb, sb]), [bits], sort);
    let equal = app(&mut terms, "=", &[x, cast], Sort::Bool);
    let model = StubModel::new()
        .with(x, exact(false, BigUint::zero(), 1u32.into(), eb, sb))
        .with(bits, ModelValue::bitvec(BigInt::from(1), u32::MAX));
    assert_confirmed(&verdict(&terms, &model, &[equal]));
}

#[test]
fn exact_nan_keys_cannot_bypass_array_or_uf_congruence() {
    struct Pins {
        model: StubModel,
        apps: HashMap<TermId, ModelValue>,
    }
    impl ModelView for Pins {
        fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
            self.model.leaf_value(t)
        }
        fn uf_app_value(&self, t: TermId) -> Option<ModelValue> {
            self.apps.get(&t).cloned()
        }
    }
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(80, 200);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let exponent = (BigUint::from(1u8) << 80usize) - BigUint::from(1u8);
    let a = exact(false, exponent.clone(), 1u32.into(), 80, 200);
    let b = exact(true, exponent, BigUint::from(1u8) << 198usize, 80, 200);
    let array = terms.mk_var("array", Sort::array(sort, Sort::Int));
    let read = app(&mut terms, "select", &[array, y], Sort::Int);
    let seven = terms.mk_int(int(7));
    let eight = terms.mk_int(int(8));
    let read_claim = app(&mut terms, "=", &[read, seven], Sort::Bool);
    let fx = app(&mut terms, "f", &[x], Sort::Int);
    let fy = app(&mut terms, "f", &[y], Sort::Int);
    let fx_claim = app(&mut terms, "=", &[fx, seven], Sort::Bool);
    let fy_claim = app(&mut terms, "=", &[fy, eight], Sort::Bool);
    let mut model = Pins {
        model: StubModel::new().with(x, a.clone()).with(y, b).with(
            array,
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![(a, ModelValue::Int(int(7)))],
            })),
        ),
        apps: HashMap::from([(fx, ModelValue::Int(int(7))), (fy, ModelValue::Int(int(8)))]),
    };
    assert_confirmed(&verdict(&terms, &model, &[read_claim, fx_claim]));
    assert_violates(&verdict(&terms, &model, &[fx_claim, fy_claim]));
    // Equal aggregate keys must use the same typed, metered comparison as
    // ordinary equality, including the abstract NaN keys nested in the array.
    let other_array = terms.mk_var("other_array", terms.sort(array).clone());
    model
        .model
        .leaves
        .insert(other_array, model.model.leaves[&array].clone());
    let ga = app(&mut terms, "g", &[array], Sort::Int);
    let gb = app(&mut terms, "g", &[other_array], Sort::Int);
    model.apps.insert(ga, ModelValue::Int(int(7)));
    model.apps.insert(gb, ModelValue::Int(int(8)));
    let ga_claim = app(&mut terms, "=", &[ga, seven], Sort::Bool);
    let gb_claim = app(&mut terms, "=", &[gb, eight], Sort::Bool);
    assert_violates(&verdict(&terms, &model, &[ga_claim, gb_claim]));
}

#[test]
fn original_owner_interruption_refuses_before_exact_input_allocation() {
    struct Interrupted;
    impl ModelView for Interrupted {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
        fn functional_array_interrupted(&self) -> bool {
            true
        }
    }
    struct RefusesWork;
    impl ModelView for RefusesWork {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
        fn charge_functional_array_work(&self, _: usize) -> Result<(), String> {
            Err("original owner exhausted".into())
        }
    }
    let mut terms = TermStore::new();
    let bits = terms.mk_bitvec(BigInt::from(1), 208);
    let cast = terms.mk_app(
        Symbol::indexed("to_fp", vec![8, 200]),
        [bits],
        Sort::FloatingPoint(8, 200),
    );
    assert!(matches!(
        evaluate_term(&terms, &Interrupted, cast),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(matches!(
        evaluate_term(&terms, &RefusesWork, cast),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn cached_aggregate_field_consumption_uses_dedicated_original_fp_owner() {
    use std::cell::Cell;
    struct Owner {
        value: ModelValue,
        stopped: Cell<bool>,
        charged: Cell<usize>,
    }
    impl ModelView for Owner {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(self.value.clone())
        }
        // Deliberately leave generic array/legacy interruption absent. Exact
        // DATA must use its dedicated hook even inside an aggregate.
        fn exact_fp_interrupted(&self) -> bool {
            self.stopped.get()
        }
        fn charge_exact_fp_work(&self, amount: usize) -> Result<(), String> {
            if self.stopped.get() {
                return Err("original exact owner stopped".into());
            }
            self.charged.set(self.charged.get() + amount);
            Ok(())
        }
    }
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Int, Sort::FloatingPoint(8, 200));
    let array = terms.mk_var("nested_exact_retention", sort);
    let zero = terms.mk_int(BigInt::from(0));
    let selected = app(
        &mut terms,
        "select",
        &[array, zero],
        Sort::FloatingPoint(8, 200),
    );
    let owner = Owner {
        value: ModelValue::Array(Box::new(ArrayValue {
            default: exact(
                false,
                127u32.into(),
                (BigUint::from(1u8) << 198usize) + 1u8,
                8,
                200,
            ),
            store: Vec::new(),
        })),
        stopped: Cell::new(false),
        charged: Cell::new(0),
    };
    let evaluator = Evaluator::new(&terms, &owner);
    assert!(matches!(
        evaluator.evaluate(array),
        EvalOutcome::Value(ModelValue::Array(_))
    ));
    assert_eq!(
        owner.charged.get(),
        0,
        "retaining DATA is not field consumption"
    );
    assert!(matches!(
        evaluator.evaluate(selected),
        EvalOutcome::Value(ModelValue::FloatingPointExact { .. })
    ));
    assert!(
        owner.charged.get() > 0,
        "actual field consumption paid the exact hook"
    );
    owner.stopped.set(true);
    let before = owner.charged.get();
    assert!(matches!(
        evaluator.evaluate(selected),
        EvalOutcome::Unevaluable(_)
    ));
    let fresh = Evaluator::new(&terms, &owner);
    assert!(
        matches!(
            fresh.evaluate(array),
            EvalOutcome::Value(ModelValue::Array(_))
        ),
        "unconsumed aggregate DATA alone is not an FP grant"
    );
    assert!(matches!(
        fresh.evaluate(selected),
        EvalOutcome::Unevaluable(_)
    ));
    assert_eq!(
        owner.charged.get(),
        before,
        "no admitted work after refusal"
    );
}

#[test]
fn exact_callback_reentry_obeys_shared_admission_guard_before_memo_access() {
    use std::cell::Cell;
    struct Owner<'a> {
        evaluator: Cell<Option<&'a Evaluator<'a>>>,
        value: ModelValue,
        other: TermId,
        trigger: Cell<bool>,
        reentries: Cell<usize>,
        leaves: Cell<usize>,
    }
    impl ModelView for Owner<'_> {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            self.leaves.set(self.leaves.get() + 1);
            Some(self.value.clone())
        }
        fn charge_exact_fp_work(&self, _: usize) -> Result<(), String> {
            if self.trigger.replace(false) {
                self.reentries.set(self.reentries.get() + 1);
                assert!(matches!(
                    self.evaluator.get().unwrap().evaluate(self.other),
                    EvalOutcome::Unevaluable(_)
                ));
            }
            Ok(())
        }
    }
    for warm_memo in [false, true] {
        let mut terms = TermStore::new();
        let root = terms.mk_var("exact_callback_root", Sort::FloatingPoint(8, 200));
        let other = terms.mk_var("exact_callback_other", Sort::FloatingPoint(8, 200));
        let owner = Owner {
            evaluator: Cell::new(None),
            value: exact(
                false,
                127u32.into(),
                (BigUint::from(1u8) << 198usize) + 1u8,
                8,
                200,
            ),
            other,
            trigger: Cell::new(false),
            reentries: Cell::new(0),
            leaves: Cell::new(0),
        };
        let evaluator = Evaluator::new(&terms, &owner);
        owner.evaluator.set(Some(&evaluator));
        if warm_memo {
            assert!(matches!(evaluator.evaluate(root), EvalOutcome::Value(_)));
        }
        let before = owner.leaves.get();
        owner.trigger.set(true);
        assert!(matches!(
            evaluator.evaluate(root),
            EvalOutcome::Unevaluable(_)
        ));
        assert_eq!(owner.reentries.get(), 1);
        assert_eq!(
            owner.leaves.get(),
            before + usize::from(!warm_memo),
            "reentry refuses before nested lookup or RefCell mutation"
        );
        assert!(
            matches!(evaluator.evaluate(root), EvalOutcome::Unevaluable(_)),
            "this evaluator cannot revive after the callback returned"
        );
    }
}
