// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::time::{Duration, Instant};

struct Owner {
    end: Instant,
    raw: Cell<bool>,
    callback: Cell<bool>,
    refused: Cell<bool>,
    left: Cell<usize>,
}

impl Owner {
    fn new() -> Self {
        Self {
            end: Instant::now() + Duration::from_secs(20),
            raw: Cell::new(false),
            callback: Cell::new(false),
            refused: Cell::new(false),
            left: Cell::new(1_000_000),
        }
    }
    fn stopped(&self) -> bool {
        if self.raw.get() || self.callback.get() || Instant::now() >= self.end {
            self.refused.set(true);
        }
        self.refused.get()
    }
    fn charge(&self, amount: usize) -> Result<(), String> {
        if self.stopped() {
            return Err("original prefix owner stopped".into());
        }
        let Some(left) = self.left.get().checked_sub(amount) else {
            self.left.set(0);
            self.refused.set(true);
            return Err("original prefix work exhausted".into());
        };
        self.left.set(left);
        Ok(())
    }
}

struct OwnedView<'a> {
    view: View,
    owner: &'a Owner,
}
impl ModelView for OwnedView<'_> {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.view.leaf_value(term)
    }
    fn array_snapshot(&self, term: TermId) -> Result<Option<Arc<ArraySnapshot>>, String> {
        self.view.array_snapshot(term)
    }
    fn functional_array_interrupted(&self) -> bool {
        self.owner.stopped()
    }
    fn has_functional_arrays(&self) -> bool {
        !self.view.arrays.is_empty()
    }
    fn charge_functional_array_work(&self, amount: usize) -> Result<(), String> {
        self.owner.charge(amount)
    }
}

struct Prefix<'a> {
    terms: TermStore,
    model: OwnedView<'a>,
    target: TermId,
    bound: TermId,
    hi: TermId,
    value: TermId,
    frame: TermId,
    lambda: TermId,
    definition: TermId,
}

fn fixture<'a>(
    owner: &'a Owner,
    cell: Sort,
    high: u64,
    comparison: &str,
    destination: bool,
) -> Prefix<'a> {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), cell.clone());
    let target = terms.mk_var("prefix_target", sort.clone());
    let bound = terms.mk_var("prefix_index", Sort::bitvec(64));
    let hi = terms.mk_bitvec(high.into(), 64);
    let value = terms.mk_var("original_prefix_value", cell.clone());
    let frame = terms.mk_var("original_prefix_frame", cell.clone());
    let zero = match &cell {
        Sort::Bool => ModelValue::Bool(false),
        Sort::BitVec(bits) => ModelValue::bitvec(0.into(), bits.width),
        _ => panic!("fixture cell"),
    };
    let selected = match &cell {
        Sort::Bool => ModelValue::Bool(true),
        Sort::BitVec(bits) => ModelValue::bitvec(9.into(), bits.width),
        _ => panic!("fixture cell"),
    };
    let mut view = View::default();
    view.scalars.insert(value, selected);
    view.scalars.insert(frame, zero.clone());
    let negative = if destination {
        let old = terms.mk_var("original_prefix_destination", sort.clone());
        owner.charge(1).unwrap();
        let mut work = owner.left.get();
        let snapshot = ArraySnapshot::finite(
            ArrayValue {
                default: zero,
                store: vec![],
            },
            &sort,
            &mut work,
        )
        .unwrap();
        owner.left.set(work);
        assert!(!owner.stopped());
        view.arrays.insert(old, snapshot);
        app(&mut terms, "select", &[old, bound], cell)
    } else {
        frame
    };
    let operands = if comparison == "bvugt" || comparison == "bvuge" {
        [hi, bound]
    } else {
        [bound, hi]
    };
    let condition = app(&mut terms, comparison, &operands, Sort::Bool);
    let body = terms.mk_ite_raw(condition, value, negative);
    let lambda = app(&mut terms, "lambda-array", &[bound, body], sort);
    let definition = app(&mut terms, "=", &[target, lambda], Sort::Bool);
    Prefix {
        terms,
        model: OwnedView { view, owner },
        target,
        bound,
        hi,
        value,
        frame,
        lambda,
        definition,
    }
}

fn install(case: &mut Prefix<'_>) {
    let snapshot = Evaluator::new(&case.terms, &case.model)
        .capture_array_snapshot(case.lambda)
        .unwrap();
    case.model.view.arrays.insert(case.target, snapshot);
}

fn check_read(case: &Prefix<'_>, key: u64, expected: ModelValue) {
    case.model.owner.charge(0).unwrap();
    let mut work = case.model.owner.left.get();
    let actual = case.model.view.arrays[&case.target]
        .read_with_stop(&bv(key, 64), &mut work, &mut || case.model.owner.stopped())
        .unwrap();
    case.model.owner.left.set(work);
    case.model.owner.charge(0).unwrap();
    assert!(value_eq(&actual, &expected).unwrap());
}

fn confirms(case: &Prefix<'_>) -> bool {
    matches!(
        confirm_completed_model(&case.terms, &case.model, &[case.definition]),
        GateVerdict::ConfirmedSat
    )
}

#[test]
fn implicit_zero_prefix_preserves_whole_bv32_bv64_bv128_functions() {
    let owner = Owner::new();
    for width in [32, 64, 128] {
        let mut case = fixture(&owner, Sort::bitvec(width), 3, "bvult", false);
        install(&mut case);
        for key in [0, 2] {
            check_read(&case, key, ModelValue::bitvec(9.into(), width));
        }
        for key in [3, u64::MAX] {
            check_read(&case, key, ModelValue::bitvec(0.into(), width));
        }
        assert!(confirms(&case));
    }
}

#[test]
fn empty_zero_prefix_still_authenticates_both_original_scalar_captures() {
    let owner = Owner::new();
    let mut case = fixture(&owner, Sort::bitvec(64), 0, "bvult", false);
    install(&mut case);
    check_read(&case, 0, bv(0, 64));
    assert!(confirms(&case));
    case.model.view.scalars.remove(&case.value);
    assert!(Evaluator::new(&case.terms, &case.model)
        .capture_array_snapshot(case.lambda)
        .is_err());
}

#[test]
fn exclusive_max_prefix_does_not_overwrite_the_last_unsigned_index() {
    let owner = Owner::new();
    let mut case = fixture(&owner, Sort::bitvec(128), u64::MAX, "bvult", false);
    install(&mut case);
    check_read(&case, u64::MAX - 1, ModelValue::bitvec(9.into(), 128));
    check_read(&case, u64::MAX, ModelValue::bitvec(0.into(), 128));
    assert!(confirms(&case));
}

#[test]
fn inclusive_max_is_full_domain_without_wrapping_the_upper_endpoint() {
    let owner = Owner::new();
    for cell in [
        Sort::Bool,
        Sort::bitvec(32),
        Sort::bitvec(64),
        Sort::bitvec(128),
    ] {
        let mut case = fixture(&owner, cell.clone(), u64::MAX, "bvule", false);
        install(&mut case);
        let expected = match cell {
            Sort::Bool => ModelValue::Bool(true),
            Sort::BitVec(bits) => ModelValue::bitvec(9.into(), bits.width),
            _ => panic!("fixture cell"),
        };
        check_read(&case, u64::MAX, expected);
        assert!(confirms(&case));
        case.model.view.scalars.remove(&case.frame);
        assert!(Evaluator::new(&case.terms, &case.model)
            .capture_array_snapshot(case.lambda)
            .is_err());
    }
}

#[test]
fn inclusive_zero_and_bounded_successor_are_exact_not_modular_overflow() {
    let owner = Owner::new();
    for high in [0, 3] {
        let mut case = fixture(&owner, Sort::bitvec(32), high, "bvule", false);
        install(&mut case);
        check_read(&case, high, bv(9, 32));
        check_read(&case, high + 1, bv(0, 32));
        assert!(confirms(&case));
    }
}

#[test]
fn reversed_unsigned_comparisons_preserve_the_exact_operand_identity() {
    let owner = Owner::new();
    for comparison in ["bvugt", "bvuge"] {
        let mut case = fixture(&owner, Sort::bitvec(64), 3, comparison, false);
        install(&mut case);
        check_read(&case, 2, bv(9, 64));
        check_read(&case, 3, bv(if comparison == "bvuge" { 9 } else { 0 }, 64));
        assert!(confirms(&case));
    }
}

#[test]
fn original_array_frame_and_contradictory_read_are_independently_checked() {
    let owner = Owner::new();
    let mut case = fixture(&owner, Sort::bitvec(32), 3, "bvult", true);
    install(&mut case);
    assert!(confirms(&case));
    let index = case.terms.mk_bitvec(2.into(), 64);
    let read = app(
        &mut case.terms,
        "select",
        &[case.target, index],
        Sort::bitvec(32),
    );
    let wrong = case.terms.mk_bitvec(0.into(), 32);
    let false_root = app(&mut case.terms, "=", &[read, wrong], Sort::Bool);
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.model, &[case.definition, false_root]),
        GateVerdict::ModelViolates { .. }
    ));
}

#[test]
fn changed_original_scalar_does_not_confirm_a_saved_prefix_snapshot() {
    let owner = Owner::new();
    let mut case = fixture(&owner, Sort::bitvec(64), 3, "bvult", false);
    install(&mut case);
    case.model.view.scalars.insert(case.value, bv(10, 64));
    assert!(!confirms(&case));
}

#[test]
fn unsupported_unchosen_arm_is_not_erased_by_empty_or_full_prefixes() {
    let owner = Owner::new();
    for high in [0, u64::MAX] {
        let comparison = if high == 0 { "bvult" } else { "bvule" };
        let mut case = fixture(&owner, Sort::bitvec(32), high, comparison, false);
        let unsupported = app(
            &mut case.terms,
            "opaque_prefix",
            &[case.frame],
            Sort::bitvec(32),
        );
        let condition = app(
            &mut case.terms,
            comparison,
            &[case.bound, case.hi],
            Sort::Bool,
        );
        let body = case.terms.mk_ite_raw(condition, case.value, unsupported);
        let sort = case.terms.sort(case.lambda).clone();
        let lambda = app(&mut case.terms, "lambda-array", &[case.bound, body], sort);
        assert!(Evaluator::new(&case.terms, &case.model)
            .capture_array_snapshot(lambda)
            .is_err());
    }
}

#[test]
fn wrong_binder_signed_compare_and_wrong_bound_sort_decline() {
    let owner = Owner::new();
    for mode in 0..3 {
        let mut case = fixture(&owner, Sort::bitvec(64), 3, "bvult", false);
        let (first, high, comparison) = match mode {
            0 => (
                case.terms
                    .mk_var("different_prefix_index", Sort::bitvec(64)),
                case.hi,
                "bvult",
            ),
            1 => (case.bound, case.hi, "bvslt"),
            _ => (case.bound, case.terms.mk_bitvec(3.into(), 32), "bvult"),
        };
        let condition = app(&mut case.terms, comparison, &[first, high], Sort::Bool);
        let body = case.terms.mk_ite_raw(condition, case.value, case.frame);
        let sort = case.terms.sort(case.lambda).clone();
        let lambda = app(&mut case.terms, "lambda-array", &[case.bound, body], sort);
        assert!(Evaluator::new(&case.terms, &case.model)
            .capture_array_snapshot(lambda)
            .is_err());
    }
}

#[test]
fn captured_upper_bound_and_selected_value_cannot_use_the_lexical_index() {
    let owner = Owner::new();
    for capture_high in [false, true] {
        let mut case = fixture(&owner, Sort::bitvec(64), 0, "bvult", false);
        let condition = app(
            &mut case.terms,
            "bvult",
            &[case.bound, if capture_high { case.bound } else { case.hi }],
            Sort::Bool,
        );
        let body = case.terms.mk_ite_raw(
            condition,
            if capture_high { case.value } else { case.bound },
            case.frame,
        );
        let sort = case.terms.sort(case.lambda).clone();
        let lambda = app(&mut case.terms, "lambda-array", &[case.bound, body], sort);
        assert!(Evaluator::new(&case.terms, &case.model)
            .capture_array_snapshot(lambda)
            .is_err());
    }
}

#[test]
fn original_raw_callback_and_absolute_end_refusals_survive_reset() {
    let original_start = Instant::now();
    let common_end = original_start + Duration::from_secs(20);
    for cause in 0..3 {
        let mut owner = Owner::new();
        // Independent negative fixture owners share one live absolute end.
        // The deadline-negative fixture is deliberately already expired.
        owner.end = if cause == 2 {
            original_start
                .checked_sub(Duration::from_secs(1))
                .expect("a current instant has an earlier representable second")
        } else {
            common_end
        };
        let case = fixture(&owner, Sort::bitvec(32), 3, "bvult", false);
        if cause == 0 {
            owner.raw.set(true);
        }
        if cause == 1 {
            owner.callback.set(true);
        }
        assert!(Evaluator::new(&case.terms, &case.model)
            .capture_array_snapshot(case.lambda)
            .is_err());
        owner.raw.set(false);
        owner.callback.set(false);
        assert!(Evaluator::new(&case.terms, &case.model)
            .capture_array_snapshot(case.lambda)
            .is_err());
    }
}

#[test]
fn one_remaining_work_ledger_cannot_be_refilled_after_capture_failure() {
    let owner = Owner::new();
    let case = fixture(&owner, Sort::bitvec(32), 3, "bvult", false);
    owner.left.set(1);
    let evaluator = Evaluator::new(&case.terms, &case.model);
    assert!(evaluator.capture_array_snapshot(case.lambda).is_err());
    assert_eq!(owner.left.get(), 0);
    assert!(evaluator.capture_array_snapshot(case.lambda).is_err());
    assert_eq!(owner.left.get(), 0);
}

#[test]
fn a_late_original_owner_stop_vetoes_whole_definition_confirmation() {
    let owner = Owner::new();
    let mut case = fixture(&owner, Sort::bitvec(32), 3, "bvult", false);
    install(&mut case);
    owner.callback.set(true);
    assert!(!confirms(&case));
    owner.callback.set(false);
    assert!(!confirms(&case));
}
