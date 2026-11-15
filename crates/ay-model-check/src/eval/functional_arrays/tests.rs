// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::collections::BTreeMap;

use super::*;
use crate::{confirm_completed_model, ArrayValue, GateVerdict, ModelView};
use ay_core::Symbol;

#[derive(Default)]
struct View {
    arrays: BTreeMap<TermId, Arc<ArraySnapshot>>,
    scalars: BTreeMap<TermId, ModelValue>,
    stopped: Cell<bool>,
    left: Cell<usize>,
}

impl ModelView for View {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.scalars.get(&term).cloned()
    }
    fn array_snapshot(&self, term: TermId) -> Result<Option<Arc<ArraySnapshot>>, String> {
        Ok(self.arrays.get(&term).cloned())
    }
    fn functional_array_interrupted(&self) -> bool {
        self.stopped.get()
    }
    fn has_functional_arrays(&self) -> bool {
        !self.arrays.is_empty()
    }
    fn charge_functional_array_work(&self, amount: usize) -> Result<(), String> {
        self.left.set(
            self.left
                .get()
                .checked_sub(amount)
                .ok_or("original work exhausted")?,
        );
        Ok(())
    }
}

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::bitvec(value.into(), width)
}
fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}
fn base(value: u64) -> Arc<ArraySnapshot> {
    ArraySnapshot::finite(
        ArrayValue {
            default: bv(value, 8),
            store: vec![],
        },
        &Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        &mut 1000,
    )
    .expect("typed base")
}

struct Case {
    terms: TermStore,
    view: View,
    target: TermId,
    lambda: TermId,
    definition: TermId,
    lo: TermId,
    hi: TermId,
}

fn case(symbolic: bool, high: u64) -> Case {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let dst = terms.mk_var("old_dst", sort.clone());
    let src = terms.mk_var("old_src", sort.clone());
    let target = terms.mk_var("written", sort.clone());
    let bound = terms.mk_var("lambda_index", Sort::bitvec(64));
    let lo = if symbolic {
        terms.mk_var("low", Sort::bitvec(64))
    } else {
        terms.mk_bitvec(1.into(), 64)
    };
    let hi = if symbolic {
        terms.mk_var("high", Sort::bitvec(64))
    } else {
        terms.mk_bitvec(high.into(), 64)
    };
    let low = app(&mut terms, "bvule", &[lo, bound], Sort::Bool);
    let high_guard = app(&mut terms, "bvult", &[bound, hi], Sort::Bool);
    let guard = app(&mut terms, "and", &[low, high_guard], Sort::Bool);
    let offset = app(&mut terms, "bvsub", &[bound, lo], Sort::bitvec(64));
    let copied = app(&mut terms, "select", &[src, offset], Sort::bitvec(8));
    let preserved = app(&mut terms, "select", &[dst, bound], Sort::bitvec(8));
    let body = terms.mk_ite_raw(guard, copied, preserved);
    let lambda = app(&mut terms, "lambda-array", &[bound, body], sort);
    let definition = app(&mut terms, "=", &[target, lambda], Sort::Bool);
    let mut view = View {
        left: Cell::new(100_000),
        ..View::default()
    };
    view.arrays.insert(dst, base(7));
    view.arrays.insert(src, base(9));
    if symbolic {
        view.scalars.insert(lo, bv(1, 64));
        view.scalars.insert(hi, bv(high, 64));
    }
    let selected = Evaluator::new(&terms, &view)
        .capture_array_snapshot(lambda)
        .expect("closed syntax captures");
    view.arrays.insert(target, selected);
    Case {
        terms,
        view,
        target,
        lambda,
        definition,
        lo,
        hi,
    }
}

fn assertion(case: &mut Case, index: u64, expected: u64) -> TermId {
    let index = case.terms.mk_bitvec(index.into(), 64);
    let read = app(
        &mut case.terms,
        "select",
        &[case.target, index],
        Sort::bitvec(8),
    );
    let expected = case.terms.mk_bitvec(expected.into(), 8);
    app(&mut case.terms, "=", &[read, expected], Sort::Bool)
}

#[test]
fn symbolic_huge_bounds_validate_whole_definition_and_all_ground_reads() {
    let mut case = case(true, 1 << 60);
    let roots = [
        case.definition,
        assertion(&mut case, 0, 7),
        assertion(&mut case, 1, 9),
        assertion(&mut case, (1 << 60) - 1, 9),
        assertion(&mut case, 1 << 60, 7),
    ];
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &roots),
        GateVerdict::ConfirmedSat
    ));
    assert!(
        case.view.left.get() > 90_000,
        "no work proportional to symbolic interval size"
    );
}

#[test]
fn independent_contradictory_read_refutes_the_same_chosen_snapshot() {
    let mut case = case(false, 3);
    let good = assertion(&mut case, 1, 9);
    let contradiction = assertion(&mut case, 1, 7);
    assert!(matches!(
        confirm_completed_model(
            &case.terms,
            &case.view,
            &[case.definition, good, contradiction]
        ),
        GateVerdict::ModelViolates { .. }
    ));
}

#[test]
fn stale_scalar_capture_cannot_confirm_original_whole_function() {
    let case = case(true, 3);
    case.view.scalars.get(&case.hi).expect("symbolic bound");
    let mut view = case.view;
    view.scalars.insert(case.hi, bv(4, 64));
    assert!(matches!(
        confirm_completed_model(&case.terms, &view, &[case.definition]),
        GateVerdict::CannotConfirm { .. }
    ));
}

#[test]
fn changed_lambda_is_not_a_sat_literal_or_finite_probe_equality() {
    let mut case = case(false, 3);
    let sort = case.terms.sort(case.target).clone();
    let replacement = case.terms.mk_var("unrelated_array", sort);
    case.view.arrays.insert(replacement, base(9));
    let wrong = app(
        &mut case.terms,
        "=",
        &[case.target, replacement],
        Sort::Bool,
    );
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &[wrong]),
        GateVerdict::CannotConfirm { .. }
    ));
}

#[test]
fn binder_capture_is_rejected_and_distinct_outer_scalar_stays_exact() {
    let mut case = case(true, 3);
    // The genuine original syntax binds only lambda_index. Outer low/high
    // scalars remain closed captures, never fresh per-lane assignments.
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(case.lambda)
        .is_ok());
    let recipe = recognize_range_lambda(&case.terms, case.lambda).expect("range recipe");
    let outer = case.terms.mk_var("lambda_index!outer", Sort::bitvec(64));
    case.view.scalars.insert(outer, bv(1, 64));
    let captured_low = app(
        &mut case.terms,
        "bvule",
        &[recipe.bound, recipe.bound],
        Sort::Bool,
    );
    let captured_hi = app(
        &mut case.terms,
        "bvult",
        &[recipe.bound, case.hi],
        Sort::Bool,
    );
    let condition = app(
        &mut case.terms,
        "and",
        &[captured_low, captured_hi],
        Sort::Bool,
    );
    let shift = app(
        &mut case.terms,
        "bvsub",
        &[recipe.bound, recipe.bound],
        Sort::bitvec(64),
    );
    let yes = app(
        &mut case.terms,
        "select",
        &[recipe.source, shift],
        Sort::bitvec(8),
    );
    let no = app(
        &mut case.terms,
        "select",
        &[recipe.destination, recipe.bound],
        Sort::bitvec(8),
    );
    let body = case.terms.mk_ite_raw(condition, yes, no);
    let sort = case.terms.sort(case.target).clone();
    let lambda = app(&mut case.terms, "lambda-array", &[recipe.bound, body], sort);
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(lambda)
        .is_err());
    assert_ne!(outer, recipe.bound);
}

#[test]
fn cancellation_and_cumulative_work_refuse_before_confirmation() {
    let case = case(false, 3);
    case.view.stopped.set(true);
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &[case.definition]),
        GateVerdict::CannotConfirm { .. }
    ));
    case.view.stopped.set(false);
    case.view.left.set(0);
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &[case.definition]),
        GateVerdict::CannotConfirm { .. }
    ));
}

#[test]
fn construction_debits_one_budget_even_after_failure() {
    let case = case(true, 3);
    let mut work = 3;
    let evaluator = Evaluator::new(&case.terms, &case.view);
    assert!(evaluator
        .capture_array_snapshot_with_work(case.lambda, &mut work)
        .is_err());
    assert_eq!(work, 0);
    assert!(evaluator
        .capture_array_snapshot_with_work(case.lambda, &mut work)
        .is_err());
    assert_eq!(work, 0);
}

#[test]
fn old_model_view_default_does_not_grant_dependent_lambda_support() {
    struct OldView;
    impl ModelView for OldView {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
    }
    let case = case(false, 3);
    assert!(matches!(
        confirm_completed_model(&case.terms, &OldView, &[case.definition]),
        GateVerdict::CannotConfirm { .. }
    ));
    assert!(OldView
        .array_snapshot(case.target)
        .expect("default decline")
        .is_none());
    assert_ne!(case.lo, case.hi);
}

#[test]
fn opaque_function_backed_constructor_does_not_gain_range_equality_authority() {
    let mut case = case(false, 3);
    let sort = case.terms.sort(case.target).clone();
    let function = case
        .terms
        .mk_var("opaque_backing_function", Sort::bitvec(8));
    let opaque = app(&mut case.terms, "as-array", &[function], sort);
    let equality = app(&mut case.terms, "=", &[case.target, opaque], Sort::Bool);
    assert!(Evaluator::new(&case.terms, &case.view)
        .capture_array_snapshot(opaque)
        .is_err());
    assert!(!matches!(
        confirm_completed_model(&case.terms, &case.view, &[equality]),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn default_absent_views_keep_ordinary_select_and_equality_budget_unchanged() {
    struct Legacy;
    impl ModelView for Legacy {
        fn leaf_value(&self, _term: TermId) -> Option<ModelValue> {
            Some(ModelValue::Array(Box::new(ArrayValue {
                default: bv(7, 8),
                store: vec![],
            })))
        }
    }
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let left = terms.mk_var("legacy_left", sort.clone());
    let right = terms.mk_var("legacy_right", sort);
    let index = terms.mk_bitvec(42.into(), 64);
    let read = app(&mut terms, "select", &[left, index], Sort::bitvec(8));
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    let evaluator = Evaluator::new(&terms, &Legacy);
    evaluator.functional_work_left.set(0);
    assert!(
        matches!(evaluator.evaluate(read), EvalOutcome::Value(ModelValue::BitVec { value, width: 8 }) if value == BigInt::from(7))
    );
    assert!(matches!(
        evaluator.evaluate(equality),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert_eq!(evaluator.functional_work_left.get(), 0);
}

#[test]
fn snapshot_hook_without_explicit_activation_refuses_instead_of_becoming_legacy_data() {
    struct Inconsistent;
    impl ModelView for Inconsistent {
        fn leaf_value(&self, _term: TermId) -> Option<ModelValue> {
            None
        }
        fn array_snapshot(&self, _term: TermId) -> Result<Option<Arc<ArraySnapshot>>, String> {
            Ok(Some(base(7)))
        }
    }
    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "inconsistent_array",
        Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
    );
    let index = terms.mk_bitvec(0.into(), 64);
    let read = app(&mut terms, "select", &[array, index], Sort::bitvec(8));
    let evaluator = Evaluator::new(&terms, &Inconsistent);
    assert!(!matches!(evaluator.evaluate(read), EvalOutcome::Value(_)));
}

mod projections;

mod metadata;

mod identity;

mod fill;

mod prefix;
