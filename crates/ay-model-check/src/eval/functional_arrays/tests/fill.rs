// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::recognize_fill_lambda;

struct FillCase {
    terms: TermStore,
    view: View,
    target: TermId,
    lambda: TermId,
    definition: TermId,
    byte: TermId,
}

fn filled(lo: u64, hi: u64, scalar_frame: bool) -> FillCase {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let destination = terms.mk_var("old_fill_destination", sort.clone());
    let target = terms.mk_var("filled", sort.clone());
    let bound = terms.mk_var("fill_index", Sort::bitvec(64));
    let byte = terms.mk_var("original_byte", Sort::bitvec(8));
    let low = terms.mk_bitvec(lo.into(), 64);
    let high = terms.mk_bitvec(hi.into(), 64);
    let ge = app(&mut terms, "bvule", &[low, bound], Sort::Bool);
    let lt = app(&mut terms, "bvult", &[bound, high], Sort::Bool);
    let condition = app(&mut terms, "and", &[ge, lt], Sort::Bool);
    let frame = if scalar_frame {
        terms.mk_bitvec(7.into(), 8)
    } else {
        app(&mut terms, "select", &[destination, bound], Sort::bitvec(8))
    };
    let body = terms.mk_ite_raw(condition, byte, frame);
    let lambda = app(&mut terms, "lambda-array", &[bound, body], sort.clone());
    let definition = app(&mut terms, "=", &[target, lambda], Sort::Bool);
    let mut view = View {
        left: Cell::new(500_000),
        ..View::default()
    };
    view.arrays.insert(destination, base(7));
    view.scalars.insert(byte, bv(9, 8));
    let snapshot = Evaluator::new(&terms, &view)
        .capture_array_snapshot(lambda)
        .expect("exact fill capture");
    view.arrays.insert(target, snapshot);
    FillCase {
        terms,
        view,
        target,
        lambda,
        definition,
        byte,
    }
}

fn read(case: &FillCase, key: u64) -> ModelValue {
    case.view.arrays[&case.target]
        .read(&bv(key, 64), &mut 100_000)
        .expect("whole data read")
}

fn assert_fill_value(actual: ModelValue, expected: ModelValue) {
    match (actual, expected) {
        (ModelValue::Bool(actual), ModelValue::Bool(expected)) => assert_eq!(actual, expected),
        (
            ModelValue::BitVec {
                value: actual,
                width: actual_width,
            },
            ModelValue::BitVec {
                value: expected,
                width: expected_width,
            },
        ) => {
            assert_eq!(actual_width, expected_width);
            assert_eq!(actual, expected);
        }
        (actual, expected) => panic!("wrong fill scalar: {actual:?}, expected {expected:?}"),
    }
}

#[test]
fn range_fill_is_constant_size_and_confirms_entire_original_definition() {
    let case = filled(1, u64::MAX, false);
    assert_fill_value(read(&case, 0), bv(7, 8));
    assert_fill_value(read(&case, 1), bv(9, 8));
    assert_fill_value(read(&case, u64::MAX - 1), bv(9, 8));
    assert_fill_value(read(&case, u64::MAX), bv(7, 8));
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &[case.definition]),
        GateVerdict::ConfirmedSat
    ));
    assert!(case.view.left.get() > 450_000);
}

#[test]
fn scalar_frame_from_closed_printed_capture_preserves_exact_function() {
    let case = filled(1, 3, true);
    assert_fill_value(read(&case, 0), bv(7, 8));
    assert_fill_value(read(&case, 1), bv(9, 8));
    assert!(matches!(
        confirm_completed_model(&case.terms, &case.view, &[case.definition]),
        GateVerdict::ConfirmedSat
    ));
    assert!(recognize_fill_lambda(&case.terms, case.lambda)
        .expect("fill")
        .interval
        .expect("range")
        .destination
        .is_none());
}

#[test]
fn changed_original_scalar_cannot_confirm_saved_whole_fill() {
    let mut case = filled(1, 3, false);
    case.view.scalars.insert(case.byte, bv(10, 8));
    assert!(!matches!(
        confirm_completed_model(&case.terms, &case.view, &[case.definition]),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn empty_and_reversed_still_check_raw_scalar_captures() {
    for (lo, hi) in [(0, 0), (9, 3), (u64::MAX, 0)] {
        let mut case = filled(lo, hi, false);
        assert_fill_value(read(&case, 1), bv(7, 8));
        case.view.scalars.remove(&case.byte);
        assert!(Evaluator::new(&case.terms, &case.view)
            .capture_array_snapshot(case.lambda)
            .is_err());
    }
}

#[test]
fn full_bool_and_bv128_domains_include_last_bv64_key() {
    for (cell, value) in [
        (Sort::Bool, ModelValue::Bool(true)),
        (
            Sort::bitvec(128),
            ModelValue::bitvec(BigInt::from(u128::MAX), 128),
        ),
    ] {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(64), cell.clone());
        let bound = terms.mk_var("full_index", Sort::bitvec(64));
        let scalar = terms.mk_var("full_scalar", cell);
        let lambda = app(&mut terms, "lambda-array", &[bound, scalar], sort);
        let mut view = View {
            left: Cell::new(100_000),
            ..View::default()
        };
        view.scalars.insert(scalar, value.clone());
        let snapshot = Evaluator::new(&terms, &view)
            .capture_array_snapshot(lambda)
            .expect("full model scalar");
        assert_fill_value(
            snapshot
                .read(&bv(u64::MAX, 64), &mut 1000)
                .expect("last key"),
            value,
        );
        assert!(snapshot
            .finite_value(&mut 1000)
            .expect("finite full default")
            .is_some());
    }
}

#[test]
fn repeated_symbolic_byte_uses_exact_bounded_concat() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("i", Sort::bitvec(64));
    let byte = terms.mk_var("b", Sort::bitvec(8));
    let mut value = byte;
    let mut width = 8;
    while width < 128 {
        value = app(
            &mut terms,
            "concat",
            &[value, value],
            Sort::bitvec(width * 2),
        );
        width *= 2;
    }
    let lambda = app(
        &mut terms,
        "lambda-array",
        &[bound, value],
        Sort::array(Sort::bitvec(64), Sort::bitvec(128)),
    );
    let mut view = View {
        left: Cell::new(100_000),
        ..View::default()
    };
    view.scalars.insert(byte, bv(0xab, 8));
    let snapshot = Evaluator::new(&terms, &view)
        .capture_array_snapshot(lambda)
        .expect("exact concat capture");
    assert_fill_value(
        snapshot.read(&bv(0, 64), &mut 1000).expect("full fill"),
        ModelValue::bitvec(BigInt::from(0xababababababababababababababababu128), 128),
    );
}

#[test]
fn unsupported_heads_and_unchosen_unpinned_captures_decline() {
    for indexed in [false, true] {
        let mut terms = TermStore::new();
        let bound = terms.mk_var("i", Sort::bitvec(64));
        let missing = terms.mk_var("missing", Sort::bitvec(8));
        let symbol = if indexed {
            Symbol::indexed("bvnot", vec![0])
        } else {
            Symbol::named("opaque_fill")
        };
        let unsupported = terms.mk_app(symbol, &[missing], Sort::bitvec(8));
        let selected = terms.mk_bitvec(9.into(), 8);
        let condition = terms.mk_bool(true);
        let body = terms.mk_ite_raw(condition, selected, unsupported);
        let lambda = app(
            &mut terms,
            "lambda-array",
            &[bound, body],
            Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        );
        let view = View {
            left: Cell::new(100_000),
            ..View::default()
        };
        assert!(Evaluator::new(&terms, &view)
            .capture_array_snapshot(lambda)
            .is_err());
    }
}

#[test]
fn binder_backedge_wrong_literal_and_excessive_depth_never_form_complete_fill() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("i", Sort::bitvec(64));
    let mut values = vec![
        bound,
        terms.mk_app(Symbol::named("bvadd"), &[bound], Sort::bitvec(64)),
    ];
    let mut deep = terms.mk_bitvec(1.into(), 64);
    for _ in 0..65 {
        deep = app(&mut terms, "bvnot", &[deep], Sort::bitvec(64));
    }
    values.push(deep);
    let view = View {
        left: Cell::new(100_000),
        ..View::default()
    };
    for value in values {
        let lambda = app(
            &mut terms,
            "lambda-array",
            &[bound, value],
            Sort::array(Sort::bitvec(64), Sort::bitvec(64)),
        );
        assert!(Evaluator::new(&terms, &view)
            .capture_array_snapshot(lambda)
            .is_err());
    }
}

#[test]
fn cancellation_and_repeated_failed_capture_share_original_work() {
    let case = filled(1, 3, false);
    case.view.stopped.set(true);
    let evaluator = Evaluator::new(&case.terms, &case.view);
    let mut left = 100;
    assert!(evaluator
        .capture_array_snapshot_with_work(case.lambda, &mut left)
        .is_err());
    case.view.stopped.set(false);
    left = 1;
    assert!(evaluator
        .capture_array_snapshot_with_work(case.lambda, &mut left)
        .is_err());
    assert_eq!(left, 0);
    assert!(evaluator
        .capture_array_snapshot_with_work(case.lambda, &mut left)
        .is_err());
    assert_eq!(left, 0);
}

#[test]
fn a_shared_subgraph_cannot_hide_an_overdeep_later_occurrence() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("i", Sort::bitvec(64));
    let mut shared = terms.mk_bitvec(1.into(), 8);
    for _ in 0..30 {
        shared = app(&mut terms, "bvnot", &[shared], Sort::bitvec(8));
    }
    let mut deep = shared;
    for _ in 0..40 {
        deep = app(&mut terms, "bvnot", &[deep], Sort::bitvec(8));
    }
    let body = app(&mut terms, "bvadd", &[shared, deep], Sort::bitvec(8));
    let lambda = app(
        &mut terms,
        "lambda-array",
        &[bound, body],
        Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
    );
    let view = View {
        left: Cell::new(100_000),
        ..View::default()
    };
    assert!(Evaluator::new(&terms, &view)
        .capture_array_snapshot(lambda)
        .is_err());
}
