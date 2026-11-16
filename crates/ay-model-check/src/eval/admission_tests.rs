// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::rc::Rc;

#[derive(Default)]
struct Ledger {
    work: Cell<usize>,
    bytes: Cell<usize>,
    refused: Cell<bool>,
    calls: Cell<usize>,
}

impl Ledger {
    fn new(work: usize, bytes: usize) -> Rc<Self> {
        Rc::new(Self {
            work: Cell::new(work),
            bytes: Cell::new(bytes),
            ..Self::default()
        })
    }

    fn admit(&self, work: usize, bytes: usize) -> Result<(), String> {
        self.calls.set(self.calls.get() + 1);
        if self.refused.get() {
            return Err("owner ledger previously refused".to_owned());
        }
        match (
            self.work.get().checked_sub(work),
            self.bytes.get().checked_sub(bytes),
        ) {
            (Some(work), Some(bytes)) => {
                self.work.set(work);
                self.bytes.set(bytes);
                Ok(())
            }
            _ => {
                self.refused.set(true);
                Err("owner ledger exhausted".to_owned())
            }
        }
    }
}

struct Metered {
    ledger: Rc<Ledger>,
    values: HashMap<TermId, ModelValue>,
    leaf_calls: Cell<usize>,
    projection_calls: Cell<usize>,
}

impl Metered {
    fn new(ledger: Rc<Ledger>) -> Self {
        Self {
            ledger,
            values: HashMap::new(),
            leaf_calls: Cell::new(0),
            projection_calls: Cell::new(0),
        }
    }
}

impl ModelView for Metered {
    fn has_evaluation_admission(&self) -> bool {
        true
    }
    fn refuse_evaluation_work(&self, _: &str) {
        self.ledger.refused.set(true);
    }
    fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
        self.ledger.admit(work, bytes)
    }

    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.leaf_calls.set(self.leaf_calls.get() + 1);
        let value = self.values.get(&term)?;
        if crate::admit_model_value_work(value, &mut |work, bytes| self.ledger.admit(work, bytes))
            .is_err()
        {
            self.ledger.refused.set(true);
            return None;
        }
        Some(value.clone())
    }

    fn projection_argument(
        &self,
        _: TermId,
    ) -> Result<Option<usize>, crate::ProjectionLookupError> {
        self.projection_calls.set(self.projection_calls.get() + 1);
        Ok(None)
    }
}

fn unevaluable(value: EvalOutcome) {
    assert!(matches!(&value, EvalOutcome::Unevaluable(_)), "{value:?}");
}

#[test]
fn regex_scratch_borrows_the_original_model_ledger_and_keeps_its_refusal() {
    let mut terms = TermStore::new();
    let text = terms.mk_string("abcdefgh".into());
    let all = terms.mk_app_structural(Symbol::named("re.all"), &[], Sort::RegLan);
    let root = terms.mk_app_structural(Symbol::named("str.in_re"), &[text, all], Sort::Bool);
    let ample = Metered::new(Ledger::new(1_000_000, 1 << 20));
    assert!(matches!(
        Evaluator::new(&terms, &ample).evaluate(root),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    let used = (1 << 20) - ample.ledger.bytes.get();
    let limited = Metered::new(Ledger::new(1_000_000, used - 1));
    let refused = Evaluator::new(&terms, &limited).evaluate(root);
    assert!(
        matches!(refused, EvalOutcome::Unevaluable(reason) if reason.contains("owner ledger exhausted"))
    );
    assert!(limited.ledger.refused.get());
    unevaluable(Evaluator::new(&terms, &limited).evaluate(root));
}

#[test]
fn default_view_keeps_exact_evaluation_and_memo_behavior() {
    struct DefaultView;
    impl ModelView for DefaultView {
        fn admit_evaluation_work(&self, _: usize, _: usize) -> Result<(), String> {
            panic!("default-absent view must not call admission")
        }
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(ModelValue::Bool(true))
        }
    }
    let mut terms = TermStore::new();
    let variable = terms.mk_var("p", Sort::Bool);
    let negated = terms.mk_not_raw(variable);
    let evaluator = Evaluator::new(&terms, &DefaultView);
    for _ in 0..2 {
        assert!(matches!(
            evaluator.evaluate(negated),
            EvalOutcome::Value(ModelValue::Bool(false))
        ));
    }
    assert!(evaluator.memo.borrow().contains_key(&variable));
    assert!(evaluator.memo.borrow().contains_key(&negated));

    struct DeepDefault(ModelValue);
    impl ModelView for DeepDefault {
        fn admit_evaluation_work(&self, _: usize, _: usize) -> Result<(), String> {
            panic!("default-absent view must not perform payload admission")
        }
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(self.0.clone())
        }
    }
    let mut value = ModelValue::Bool(true);
    let mut sort = Sort::Bool;
    for _ in 0..257 {
        value = ModelValue::Seq(vec![value]);
        sort = Sort::seq(sort);
    }
    let mut terms = TermStore::new();
    let term = terms.mk_var("deep", sort);
    let model = DeepDefault(value);
    assert!(matches!(
        Evaluator::new(&terms, &model).evaluate(term),
        EvalOutcome::Value(ModelValue::Seq(_))
    ));
}

#[test]
fn fp_to_real_original_admission_prepays_conversion_and_stays_cumulative() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("owned_fp", Sort::FloatingPoint(8, 200));
    let converted = terms.mk_app(Symbol::named("fp.to_real"), vec![x], Sort::Real);
    let value = ModelValue::floating_point_exact(false, 127u8.into(), 1u8.into(), 8, 200).unwrap();
    let plan = crate::fp_exact::real_plan(&value).unwrap();
    let positive = Ledger::new(10_000, 65_536);
    let mut model = Metered::new(Rc::clone(&positive));
    model.values.insert(x, value.clone());
    let expected = BigRational::new(
        (BigInt::from(1u8) << 199usize) + 1,
        BigInt::from(1u8) << 199usize,
    );
    assert!(matches!(Evaluator::new(&terms, &model).evaluate(converted),
        EvalOutcome::Value(ModelValue::Real(result)) if result == expected));
    assert!(positive.work.get() < 10_000 && positive.bytes.get() < 65_536);

    for refuse_storage in [false, true] {
        let original = Ledger::new(10_000, 65_536);
        let mut model = Metered::new(Rc::clone(&original));
        model.values.insert(x, value.clone());
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.evaluate(x),
            EvalOutcome::Value(ModelValue::FloatingPointExact { .. })
        ));
        // Prior retained work on this SAME owner leaves less than the
        // conversion requires. Reading the immutable Arc-backed leaf itself
        // was admitted; materializing the dyadic must still obtain custody.
        if refuse_storage {
            original.bytes.set(plan.storage - 1);
        } else {
            original.work.set(plan.work - 1);
        }
        unevaluable(evaluator.evaluate(converted));
        assert!(original.refused.get());
        assert!(!evaluator.memo.borrow().contains_key(&converted));
        let leaves = model.leaf_calls.get();
        // A nested/fresh evaluator must not mint a new grant for this owner.
        unevaluable(Evaluator::new(&terms, &model).evaluate(converted));
        assert_eq!(model.leaf_calls.get(), leaves);
    }
}

#[test]
fn fp_to_bv_exact_original_admission_is_cumulative_and_precedes_rounding() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("fp_integer_owned", Sort::FloatingPoint(8, 200));
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let converted = terms.mk_app(
        Symbol::Indexed("fp.to_sbv".into(), vec![8]),
        &[rm, x],
        Sort::bitvec(8),
    );
    let value = ModelValue::floating_point_exact(false, 127u8.into(), 1u8.into(), 8, 200).unwrap();
    let plan = crate::fp_exact::bv_plan(
        &value,
        8,
        crate::fp_exact::BvSignedness::Signed,
        crate::fp::RoundingMode::Rne,
    )
    .unwrap();
    let original = Ledger::new(100_000, 65_536);
    let mut positive = Metered::new(Rc::clone(&original));
    positive.values.insert(x, value.clone());
    assert!(
        matches!(Evaluator::new(&terms, &positive).evaluate(converted), EvalOutcome::Value(ModelValue::BitVec { value, width: 8 }) if value == BigInt::from(1))
    );
    assert!(original.work.get() < 100_000 && original.bytes.get() < 65_536);
    for storage in [false, true] {
        let original = Ledger::new(100_000, 65_536);
        let mut model = Metered::new(Rc::clone(&original));
        model.values.insert(x, value.clone());
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.evaluate(x),
            EvalOutcome::Value(ModelValue::FloatingPointExact { .. })
        ));
        if storage {
            original.bytes.set(plan.storage - 1);
        } else {
            original.work.set(plan.work - 1);
        }
        unevaluable(evaluator.evaluate(converted));
        assert!(original.refused.get());
        assert!(!evaluator.memo.borrow().contains_key(&converted));
        let calls = model.leaf_calls.get();
        unevaluable(Evaluator::new(&terms, &model).evaluate(converted));
        assert_eq!(model.leaf_calls.get(), calls);
    }
}

#[test]
fn fp_round_integral_exact_refuses_without_original_output_storage() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 200);
    let x = terms.mk_var("integral_input", sort.clone());
    let rm = terms.mk_app(
        Symbol::named("RNA"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let root = terms.mk_app(Symbol::named("fp.roundToIntegral"), &[rm, x], sort);
    let value = ModelValue::floating_point_exact(
        false,
        128u8.into(),
        num_bigint::BigUint::from(1u8) << 197usize,
        8,
        200,
    )
    .unwrap();
    let storage = crate::fp_exact::integral_plan(&value, crate::fp::RoundingMode::Rna)
        .unwrap()
        .storage;
    let original = Ledger::new(10_000, 65_536);
    let mut model = Metered::new(Rc::clone(&original));
    model.values.insert(x, value.clone());
    assert!(matches!(Evaluator::new(&terms, &model).evaluate(root),
        EvalOutcome::Value(ModelValue::FloatingPointExact { significand, .. })
        if significand.bits() == 199));

    let original = Ledger::new(10_000, 65_536);
    let mut model = Metered::new(Rc::clone(&original));
    model.values.insert(x, value);
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.evaluate(x),
        EvalOutcome::Value(ModelValue::FloatingPointExact { .. })
    ));
    original.bytes.set(storage - 1);
    unevaluable(evaluator.evaluate(root));
    assert!(original.refused.get());
    assert!(!evaluator.memo.borrow().contains_key(&root));
    let calls = model.leaf_calls.get();
    unevaluable(Evaluator::new(&terms, &model).evaluate(root));
    assert_eq!(model.leaf_calls.get(), calls);
}

#[test]
fn recursive_entry_and_app_edges_are_admitted_before_lookup() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("p", Sort::Bool);
    let negated = terms.mk_not_raw(variable);
    let mut model = Metered::new(Ledger::new(1, usize::MAX));
    model.values.insert(variable, ModelValue::Bool(true));
    let evaluator = Evaluator::new(&terms, &model);
    unevaluable(evaluator.evaluate(negated));
    assert_eq!(
        model.leaf_calls.get(),
        0,
        "child entry must fail before lookup"
    );
    assert!(evaluator.memo.borrow().is_empty());

    let application = terms.mk_app(Symbol::named("f"), &[variable; 32], Sort::Bool);
    let model = Metered::new(Ledger::new(2, usize::MAX));
    unevaluable(Evaluator::new(&terms, &model).evaluate(application));
    assert_eq!(
        model.projection_calls.get(),
        0,
        "fanout is admitted before application dispatch"
    );
    assert_eq!(model.leaf_calls.get(), 0);
}

#[test]
fn memo_hits_and_insertions_admit_payload_before_copying() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("p", Sort::Bool);
    let ledger = Ledger::new(1_000, 1_000_000);
    let mut model = Metered::new(Rc::clone(&ledger));
    model.values.insert(variable, ModelValue::Bool(true));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.evaluate(variable),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert!(evaluator.memo.borrow().contains_key(&variable));
    let reads = model.leaf_calls.get();
    ledger.bytes.set(0);
    unevaluable(evaluator.evaluate(variable));
    assert_eq!(
        model.leaf_calls.get(),
        reads,
        "the failed copy came from a memo hit"
    );
    assert!(ledger.refused.get());

    // Allow exactly the producer copy and returned-value preflight. The next
    // copy is the memo insertion, which must fail before installing an entry.
    let value = ModelValue::Bool(true);
    let mut payload_bytes = 0usize;
    crate::admit_model_value_work(&value, &mut |_, bytes| {
        payload_bytes += bytes;
        Ok(())
    })
    .unwrap();
    let ledger = Ledger::new(usize::MAX, 2 * payload_bytes);
    let mut model = Metered::new(Rc::clone(&ledger));
    model.values.insert(variable, value);
    let evaluator = Evaluator::new(&terms, &model);
    unevaluable(evaluator.evaluate(variable));
    assert_eq!(model.leaf_calls.get(), 1);
    assert!(ledger.refused.get());
    assert!(evaluator.memo.borrow().is_empty());
}

struct Forward<'a>(&'a dyn ModelView);
impl ModelView for Forward<'_> {
    fn has_evaluation_admission(&self) -> bool {
        self.0.has_evaluation_admission()
    }
    fn refuse_evaluation_work(&self, reason: &str) {
        self.0.refuse_evaluation_work(reason);
    }
    fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
        self.0.admit_evaluation_work(work, bytes)
    }
    fn exact_fp_interrupted(&self) -> bool {
        self.0.exact_fp_interrupted()
    }
    fn charge_exact_fp_work(&self, amount: usize) -> Result<(), String> {
        self.0.charge_exact_fp_work(amount)
    }
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.0.leaf_value(term)
    }
}

#[test]
fn fresh_nested_evaluators_and_forwarding_views_share_owner_refusal() {
    struct Nested<'a> {
        terms: &'a TermStore,
        outer: TermId,
        child: TermId,
        ledger: Rc<Ledger>,
        nested_calls: Cell<usize>,
    }
    impl ModelView for Nested<'_> {
        fn has_evaluation_admission(&self) -> bool {
            true
        }
        fn refuse_evaluation_work(&self, _: &str) {
            self.ledger.refused.set(true);
        }
        fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
            self.ledger.admit(work, bytes)
        }
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            if term == self.outer {
                self.nested_calls.set(self.nested_calls.get() + 1);
                // A fresh evaluator and a wrapper must not obtain a fresh allowance.
                let view = Forward(self);
                let outcome = Evaluator::new(self.terms, &view).evaluate(self.child);
                assert!(matches!(outcome, EvalOutcome::Unevaluable(_)));
                // Even an erroneous adapter returning a decisive value after
                // nested refusal cannot make the outer evaluator publish it.
                Some(ModelValue::Bool(false))
            } else {
                Some(ModelValue::Bool(true))
            }
        }
    }
    let mut terms = TermStore::new();
    let outer = terms.mk_var("outer", Sort::Bool);
    let child = terms.mk_var("child", Sort::Bool);
    let ledger = Ledger::new(1, usize::MAX);
    let model = Nested {
        terms: &terms,
        outer,
        child,
        ledger: Rc::clone(&ledger),
        nested_calls: Cell::new(0),
    };
    unevaluable(Evaluator::new(&terms, &model).evaluate(outer));
    assert_eq!(model.nested_calls.get(), 1);
    assert!(ledger.refused.get());
    unevaluable(Evaluator::new(&terms, &Forward(&model)).evaluate(child));
}

#[test]
fn admission_failure_is_sticky_and_never_a_decisive_boolean() {
    struct OneShot {
        armed: Cell<bool>,
        failed: Cell<bool>,
    }
    impl ModelView for OneShot {
        fn has_evaluation_admission(&self) -> bool {
            true
        }
        fn admit_evaluation_work(&self, _: usize, _: usize) -> Result<(), String> {
            if self.armed.replace(false) && !self.failed.replace(true) {
                Err("stop once".to_owned())
            } else {
                Ok(())
            }
        }
        fn projection_argument(
            &self,
            _: TermId,
        ) -> Result<Option<usize>, crate::ProjectionLookupError> {
            // Arm at the parent dispatch. Its first recursive child will fail;
            // a nonsticky implementation could then return false from arm two.
            self.armed.set(true);
            Ok(None)
        }
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            panic!("refused before leaf lookup")
        }
    }
    let mut terms = TermStore::new();
    let variable = terms.mk_var("p", Sort::Bool);
    let no = terms.mk_bool(false);
    let conjunction = terms.mk_app(Symbol::named("and"), &[variable, no], Sort::Bool);
    let model = OneShot {
        armed: Cell::new(false),
        failed: Cell::new(false),
    };
    let evaluator = Evaluator::new(&terms, &model);
    unevaluable(evaluator.evaluate(conjunction));
    unevaluable(evaluator.evaluate(no));
    assert!(evaluator.memo.borrow().is_empty());
}

#[test]
fn oversized_constant_and_aggregate_payloads_decline_without_memo_install() {
    let mut terms = TermStore::new();
    let text = terms.mk_string("x".repeat(4096));
    let wide = terms.mk_bitvec(BigInt::from(1u8) << 32_767, 32_768);
    for term in [text, wide] {
        let model = Metered::new(Ledger::new(100, 512));
        let evaluator = Evaluator::new(&terms, &model);
        unevaluable(evaluator.evaluate(term));
        assert!(evaluator.memo.borrow().is_empty());
        assert_eq!(model.leaf_calls.get(), 0);
    }
    let aggregate = ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Datatype {
            ctor: "C".to_owned(),
            args: vec![ModelValue::Bool(false)],
        },
        store: vec![(
            ModelValue::Int(BigInt::from(0)),
            ModelValue::Seq(vec![ModelValue::Str("x".repeat(4096))]),
        )],
    }));
    let ledger = Ledger::new(1_000, 1024);
    assert!(
        crate::admit_model_value_work(&aggregate, &mut |work, bytes| ledger.admit(work, bytes))
            .is_err()
    );
    assert!(ledger.refused.get());
}

#[test]
fn sparse_wide_constant_admits_only_its_occupied_payload() {
    let mut terms = TermStore::new();
    let wide = terms.mk_bitvec(BigInt::from(0), 32_768);
    let model = Metered::new(Ledger::new(100, 1024));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.evaluate(wide),
        EvalOutcome::Value(ModelValue::BitVec { width: 32_768, value })
            if value == BigInt::from(0)
    ));
    assert!(!model.ledger.refused.get());
    assert!(model.ledger.bytes.get() < 1024);
}

#[test]
fn raw_bitvector_normalization_admits_scratch_before_reduction() {
    let terms = TermStore::new();
    for (value, width, expected) in [
        (BigInt::from(-1), 65, (BigInt::from(1u8) << 65usize) - 1),
        ((BigInt::from(1u8) << 200usize) + 3, 8, BigInt::from(3)),
    ] {
        let model = Metered::new(Ledger::new(100, 4096));
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval_const(&Constant::BitVec { value, width }),
            Ok(ModelValue::BitVec { value, width: actual_width })
                if actual_width == width && value == expected
        ));
        assert!(!model.ledger.refused.get());
    }
    let model = Metered::new(Ledger::new(100, 4096));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.eval_const(&Constant::BitVec {
            value: BigInt::from(1u8) << 100_000usize,
            width: 8,
        }),
        Err(EvalError::Resource { .. })
    ));
    assert!(model.ledger.refused.get());
}

#[test]
fn borrowed_preflight_covers_all_payload_shapes_and_bounds_copy_depth() {
    let rational = |value: i32| BigRational::from_integer(BigInt::from(value));
    let algebraic = crate::algebraic::Algebraic::root_of(
        vec![rational(-2), rational(0), rational(1)],
        rational(1),
        rational(2),
    )
    .unwrap();
    let shapes = [
        ModelValue::Bool(true),
        ModelValue::Int(BigInt::from(7)),
        ModelValue::Real(BigRational::new(BigInt::from(1), BigInt::from(3))),
        ModelValue::bitvec(BigInt::from(3), 8),
        ModelValue::FloatingPoint {
            sign: false,
            exponent: 0,
            significand: 0,
            exponent_bits: 8,
            significand_bits: 24,
        },
        ModelValue::floating_point_exact(
            false,
            num_bigint::BigUint::from(127u8),
            (num_bigint::BigUint::from(1u8) << 198usize) + num_bigint::BigUint::from(1u8),
            8,
            200,
        )
        .unwrap(),
        ModelValue::Str("text".to_owned()),
        ModelValue::Uninterpreted("element".to_owned()),
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Bool(false),
            store: Vec::new(),
        })),
        ModelValue::Seq(vec![ModelValue::Bool(true)]),
        ModelValue::Algebraic(Box::new(algebraic)),
        ModelValue::Datatype {
            ctor: "C".to_owned(),
            args: vec![ModelValue::Bool(true)],
        },
    ];
    for value in &shapes {
        let ledger = Ledger::new(10_000, 1_000_000);
        crate::admit_model_value_work(value, &mut |work, bytes| ledger.admit(work, bytes)).unwrap();
        assert!(!ledger.refused.get());
        assert!(ledger.work.get() < 10_000 && ledger.bytes.get() < 1_000_000);
    }
    let mut value = ModelValue::Bool(true);
    for _ in 0..257 {
        value = ModelValue::Seq(vec![value]);
    }
    let mut calls = 0;
    let error = crate::admit_model_value_work(&value, &mut |_, _| {
        calls += 1;
        Ok(())
    });
    assert!(matches!(error, Err(ref reason) if reason == "model value copy depth limit exceeded"));
    assert!(calls < 1_000);
    let mut sort = Sort::Bool;
    for _ in 0..257 {
        sort = Sort::seq(sort);
    }
    let mut terms = TermStore::new();
    let deep = terms.mk_var("deep", sort);
    let yes = terms.mk_bool(true);
    let ledger = Ledger::new(100_000, 10_000_000);
    let mut model = Metered::new(Rc::clone(&ledger));
    model.values.insert(deep, value);
    unevaluable(Evaluator::new(&terms, &model).evaluate(deep));
    assert!(
        ledger.refused.get(),
        "producer latches a preflight depth refusal"
    );
    unevaluable(Evaluator::new(&terms, &Forward(&model)).evaluate(yes));
}

#[test]
fn same_evaluator_callback_reentry_declines_before_refcell_lookups() {
    struct Reenter<'a> {
        evaluator: Cell<Option<&'a Evaluator<'a>>>,
        other: TermId,
        refused: Cell<bool>,
        trigger_copy: Cell<usize>,
        notify_reentry: Cell<bool>,
        reentries: Cell<usize>,
        leaves: Cell<usize>,
    }
    impl ModelView for Reenter<'_> {
        fn has_evaluation_admission(&self) -> bool {
            true
        }
        fn refuse_evaluation_work(&self, _: &str) {
            self.refused.set(true);
            if self.notify_reentry.replace(false) {
                self.reentries.set(self.reentries.get() + 1);
                unevaluable(self.evaluator.get().unwrap().evaluate(self.other));
            }
        }
        fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
            if self.refused.get() {
                return Err("owner refused".into());
            }
            if work == 1 && bytes == size_of::<(&ModelValue, usize)>() {
                let remaining = self.trigger_copy.get();
                if remaining != 0 {
                    self.trigger_copy.set(remaining - 1);
                    if remaining == 1 {
                        self.reentries.set(self.reentries.get() + 1);
                        unevaluable(self.evaluator.get().unwrap().evaluate(self.other));
                    }
                }
            }
            Ok(())
        }
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            self.leaves.set(self.leaves.get() + 1);
            Some(ModelValue::Bool(true))
        }
    }
    // Exercise the callback from both a held immutable memo hit and the
    // actual new-entry copy. No unsafe backreference or panic suppression.
    for warm_memo in [true, false] {
        let mut terms = TermStore::new();
        let root = terms.mk_var("root", Sort::Bool);
        let other = terms.mk_var("other", Sort::Bool);
        let model = Reenter {
            evaluator: Cell::new(None),
            other,
            refused: Cell::new(false),
            trigger_copy: Cell::new(0),
            notify_reentry: Cell::new(false),
            reentries: Cell::new(0),
            leaves: Cell::new(0),
        };
        let evaluator = Evaluator::new(&terms, &model);
        model.evaluator.set(Some(&evaluator));
        if warm_memo {
            assert!(matches!(
                evaluator.evaluate(root),
                EvalOutcome::Value(ModelValue::Bool(true))
            ));
            assert!(evaluator.memo.borrow().contains_key(&root));
        }
        let before_leaves = model.leaves.get();
        model.trigger_copy.set(if warm_memo { 1 } else { 2 });
        model.notify_reentry.set(true);
        unevaluable(evaluator.evaluate(root));
        assert_eq!(
            model.reentries.get(),
            2,
            "work and refusal notification both tried real reentry"
        );
        assert!(model.refused.get());
        assert_eq!(model.leaves.get(), before_leaves + usize::from(!warm_memo));
        assert!(!evaluator.memo.borrow().contains_key(&other));
        assert_eq!(evaluator.memo.borrow().contains_key(&root), warm_memo);
        assert!(
            !evaluator.admission_callback_active.get(),
            "callback guard must be restored"
        );
        model.evaluator.set(None);
    }
    struct FreshCallback<'a> {
        terms: &'a TermStore,
        child: TermId,
        ledger: Rc<Ledger>,
        armed: Cell<bool>,
        nested: Cell<usize>,
        leaves: Cell<usize>,
    }
    impl ModelView for FreshCallback<'_> {
        fn has_evaluation_admission(&self) -> bool {
            true
        }
        fn refuse_evaluation_work(&self, _: &str) {
            self.ledger.refused.set(true);
        }
        fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
            if self.armed.replace(false) {
                self.nested.set(self.nested.get() + 1);
                let view = Forward(self);
                assert!(matches!(
                    Evaluator::new(self.terms, &view).evaluate(self.child),
                    EvalOutcome::Value(ModelValue::Bool(true))
                ));
            }
            self.ledger.admit(work, bytes)
        }
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            self.leaves.set(self.leaves.get() + 1);
            Some(ModelValue::Bool(true))
        }
    }
    let mut terms = TermStore::new();
    let root = terms.mk_var("root", Sort::Bool);
    let child = terms.mk_var("child", Sort::Bool);
    let ledger = Ledger::new(1_000, 1_000_000);
    let model = FreshCallback {
        terms: &terms,
        child,
        ledger: Rc::clone(&ledger),
        armed: Cell::new(true),
        nested: Cell::new(0),
        leaves: Cell::new(0),
    };
    assert!(matches!(
        Evaluator::new(&terms, &model).evaluate(root),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert_eq!(model.nested.get(), 1);
    assert_eq!(model.leaves.get(), 2);
    assert!(!ledger.refused.get());
    assert!(
        ledger.work.get() < 998 && ledger.bytes.get() < 1_000_000,
        "fresh nested evaluation consumed the SAME allowance"
    );
}
