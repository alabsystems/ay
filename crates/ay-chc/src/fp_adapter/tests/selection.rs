// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact selection DATA; native SAT checks do not grant CHC/proof authority.

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

#[test]
fn bool_both_forms_select_exact_branch_values() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut poll = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut poll);
    for form in [IteForm::Direct, IteForm::Named] {
        for c in [false, true] {
            for (a, b) in [(true, false), (false, true), (true, true)] {
                let mut terms = TermStore::new();
                let condition = terms.mk_bool(c);
                let left = terms.mk_bool(a);
                let right = terms.mk_bool(b);
                let root = selection_choose(&mut terms, form, condition, left, right);
                assert_eq!(
                    selection_native_truth(&terms, root, &mut budget),
                    if c { a } else { b }
                );
            }
        }
    }
}

#[test]
fn binary32_and64_select_manual_words_and_exclude_wrong_words() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut poll = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut poll);
    for (width, sign, one, infinity) in [
        (32, 1u64 << 31, 0x3f800000u64, 0x7f800000u64),
        (64, 1u64 << 63, 0x3ff0000000000000u64, 0x7ff0000000000000u64),
    ] {
        for form in [IteForm::Direct, IteForm::Named] {
            for c in [false, true] {
                for (a, b) in [
                    (one, sign | one),
                    (0, sign),
                    (infinity, sign | infinity),
                    (1, sign | 1),
                ] {
                    let mut terms = TermStore::new();
                    let condition = terms.mk_bool(c);
                    let left = fp_constant(&mut terms, a, width);
                    let right = fp_constant(&mut terms, b, width);
                    let actual = selection_choose(&mut terms, form, condition, left, right);
                    let expected = if c { a } else { b };
                    let correct = fp_constant(&mut terms, expected, width);
                    let wrong = fp_constant(&mut terms, expected ^ 1, width);
                    let yes = predicate(&mut terms, "=", &[actual, correct]);
                    let no = predicate(&mut terms, "=", &[actual, wrong]);
                    assert!(selection_native_truth(&terms, yes, &mut budget));
                    assert!(!selection_native_truth(&terms, no, &mut budget));
                }
            }
        }
    }
}

#[test]
fn selected_nan_is_one_smt_class_not_a_raw_payload_promise() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut poll = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut poll);
    for (width, nan, sign) in [
        (32, 0x7fc00001u64, 1u64 << 31),
        (64, 0x7ff8000000000001u64, 1u64 << 63),
    ] {
        for form in [IteForm::Direct, IteForm::Named] {
            for c in [false, true] {
                let mut terms = TermStore::new();
                let condition = terms.mk_bool(c);
                let n = fp_constant(&mut terms, nan, width);
                let z = fp_constant(&mut terms, 0, width);
                let (a, b) = if c { (n, z) } else { (z, n) };
                let actual = selection_choose(&mut terms, form, condition, a, b);
                let other_nan = fp_constant(&mut terms, sign | (nan ^ 2), width);
                for (name, args, expected) in [
                    ("=", vec![actual, other_nan], true),
                    ("fp.isNaN", vec![actual], true),
                    ("fp.eq", vec![actual, actual], false),
                ] {
                    let root = predicate(&mut terms, name, &args);
                    assert_eq!(selection_native_truth(&terms, root, &mut budget), expected);
                }
            }
        }
    }
}

#[test]
fn whole_selection_keeps_condition_both_words_and_all_original_roots() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("condition", Sort::Bool);
    let a = terms.mk_var("left", Sort::FloatingPoint(11, 53));
    let b = terms.mk_var("right", Sort::FloatingPoint(11, 53));
    let actual = selection_choose(&mut terms, IteForm::Direct, c, a, b);
    let root = predicate(&mut terms, "fp.isNormal", &[actual]);
    let roots = [root, root];
    let targets = [
        ChcVar::new("condition", crate::ChcSort::Bool),
        ChcVar::new("left", crate::ChcSort::BitVec(64)),
        ChcVar::new("right", crate::ChcSort::BitVec(64)),
    ];
    let inputs = [
        FpInputBinding {
            source: c,
            target: &targets[0],
        },
        FpInputBinding {
            source: a,
            target: &targets[1],
        },
        FpInputBinding {
            source: b,
            target: &targets[2],
        },
    ];
    let namespace = ChcProblem::new();
    let mut poll = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut poll);
    let output = lower_fp_clause(&terms, &roots, &inputs, &namespace, &mut budget).unwrap();
    assert_eq!(output.source_roots(), &roots);
    assert!(std::ptr::eq(output.source_terms(), &terms));
    assert!(std::ptr::eq(output.source_namespace(), &namespace));
    assert_eq!(output.input_bindings().len(), 3);
    let ChcExpr::Op(crate::ChcOp::And, entries) = output.constraint() else {
        panic!()
    };
    let start = entries.len() - 129 - roots.len();
    assert_eq!(entries[start], entries[start + 1]);
    let ChcExpr::Op(crate::ChcOp::Eq, condition) = entries[entries.len() - 129].as_ref() else {
        panic!()
    };
    assert_eq!(condition[1].as_ref(), &ChcExpr::Var(targets[0].clone()));
    for (index, entry) in entries.iter().skip(entries.len() - 128).enumerate() {
        let ChcExpr::Op(crate::ChcOp::Eq, link) = entry.as_ref() else {
            panic!()
        };
        let ChcExpr::Op(crate::ChcOp::Eq, value) = link[1].as_ref() else {
            panic!()
        };
        let ChcExpr::Op(crate::ChcOp::BvExtract(hi, lo), word) = value[0].as_ref() else {
            panic!()
        };
        assert_eq!((*hi, *lo), ((index % 64) as u32, (index % 64) as u32));
        assert_eq!(
            word[0].as_ref(),
            &ChcExpr::Var(targets[1 + index / 64].clone())
        );
    }
}

#[test]
fn all_three_descendants_are_prepaid_for_constant_conditions_and_shared_arms() {
    for form in [IteForm::Direct, IteForm::Named] {
        let mut terms = TermStore::new();
        let c = terms.mk_bool(true);
        let a = terms.mk_bool(false);
        let root = selection_choose(&mut terms, form, c, a, a);
        let mut poll = || ControlFlow::Continue(());
        let mut budget = WorkBudget::new(10_000_000_000, &mut poll);
        let plan = source::plan(&terms, &[root], &[], &mut budget).unwrap();
        assert_eq!(plan.occurrences, 4);
        assert_eq!(plan.gates, 64 + 4 * 4096);
        let repeated = source::plan(&terms, &[root, root], &[], &mut budget).unwrap();
        assert_eq!(repeated.occurrences, 8);
        assert_eq!(repeated.gates - 64, 2 * (plan.gates - 64));
        let before = budget.remaining();
        plan.prepay(&mut budget).unwrap();
        assert_eq!(before - budget.remaining(), (plan.gates * 1024) as u64);
    }
}

#[test]
fn unsupported_unchosen_arm_and_nonliteral_mode_refuse() {
    for form in [IteForm::Direct, IteForm::Named] {
        for c in [false, true] {
            for kind in ["user_fp", "fp.min", "nonliteral", "indexed", "unbound"] {
                let mut terms = TermStore::new();
                let condition = terms.mk_bool(c);
                let good = fp_constant(&mut terms, 0, 32);
                let bad = match kind {
                    "nonliteral" => {
                        let rm = terms.mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));
                        terms.mk_app(
                            Symbol::named("fp.add"),
                            [rm, good, good],
                            Sort::FloatingPoint(8, 24),
                        )
                    }
                    "indexed" => terms.mk_app(
                        Symbol::indexed("ite", vec![8, 24]),
                        [condition, good, good],
                        Sort::FloatingPoint(8, 24),
                    ),
                    "unbound" => terms.mk_var("lost_original", Sort::FloatingPoint(8, 24)),
                    name => terms.mk_app(
                        Symbol::named(name),
                        [good, good],
                        Sort::FloatingPoint(8, 24),
                    ),
                };
                let (a, b) = if c { (good, bad) } else { (bad, good) };
                let selection = selection_choose(&mut terms, form, condition, a, b);
                let root = predicate(&mut terms, "fp.isZero", &[selection]);
                let error = selection_error(&terms, root);
                if kind == "unbound" {
                    assert!(matches!(
                        error,
                        FpAdapterError::Invalid("unbound free input")
                    ));
                } else {
                    assert!(matches!(error, FpAdapterError::Unsupported(_)));
                }
            }
        }
    }
    let terms = TermStore::from_entries(
        vec![
            (
                TermData::Const(ay_core::term::Constant::Bool(true)),
                Sort::Bool,
            ),
            (
                TermData::Forall(Vec::new(), TermId(0), Vec::new()),
                Sort::Bool,
            ),
            (TermData::Ite(TermId(0), TermId(0), TermId(1)), Sort::Bool),
        ],
        None,
        None,
        0,
    );
    assert!(matches!(
        selection_error(&terms, TermId(2)),
        FpAdapterError::Unsupported(_)
    ));
}

#[test]
fn malformed_selection_sort_arity_missing_children_and_cycles_refuse() {
    let t = TermData::Const(ay_core::term::Constant::Bool(true));
    for bad in [TermId(999), TermId(2)] {
        let terms = TermStore::from_entries(
            vec![
                (t.clone(), Sort::Bool),
                (t.clone(), Sort::Bool),
                (TermData::Ite(TermId(0), TermId(1), bad), Sort::Bool),
            ],
            None,
            None,
            0,
        );
        assert!(matches!(
            selection_error(&terms, TermId(2)),
            FpAdapterError::Invalid(_)
        ));
    }
    for bad in [
        TermData::Ite(TermId(1), TermId(0), TermId(0)),
        TermData::Ite(TermId(0), TermId(0), TermId(1)),
    ] {
        let terms = TermStore::from_entries(
            vec![
                (t.clone(), Sort::Bool),
                (
                    TermData::Const(ay_core::term::Constant::BitVec {
                        value: 0u8.into(),
                        width: 1,
                    }),
                    Sort::bitvec(1),
                ),
                (bad, Sort::Bool),
            ],
            None,
            None,
            0,
        );
        assert!(matches!(
            selection_error(&terms, TermId(2)),
            FpAdapterError::Invalid(_)
        ));
    }
    for args in [
        vec![],
        vec![TermId(0), TermId(0)],
        vec![TermId(1), TermId(0), TermId(0)],
        vec![TermId(0), TermId(0), TermId(1)],
    ] {
        let terms = TermStore::from_entries(
            vec![
                (t.clone(), Sort::Bool),
                (
                    TermData::Const(ay_core::term::Constant::BitVec {
                        value: 0u8.into(),
                        width: 1,
                    }),
                    Sort::bitvec(1),
                ),
                (TermData::App(Symbol::named("ite"), args), Sort::Bool),
            ],
            None,
            None,
            0,
        );
        assert!(matches!(
            selection_error(&terms, TermId(2)),
            FpAdapterError::Invalid(_)
        ));
    }
    let mut terms = TermStore::new();
    let c = terms.mk_bool(true);
    let a = fp_constant(&mut terms, 0, 32);
    let b = fp_constant(&mut terms, 0, 64);
    let actual = terms.mk_app(Symbol::named("ite"), [c, a, b], Sort::FloatingPoint(8, 24));
    let root = predicate(&mut terms, "fp.isZero", &[actual]);
    assert!(matches!(
        selection_error(&terms, root),
        FpAdapterError::Invalid(_)
    ));
}

#[test]
fn selection_depth_and_unrolled_occurrence_limits_remain_exact() {
    for form in [IteForm::Direct, IteForm::Named] {
        let mut terms = TermStore::new();
        let c = terms.mk_bool(true);
        let a = terms.mk_bool(false);
        let mut root = a;
        for _ in 0..64 {
            root = selection_choose(&mut terms, form, c, root, a);
        }
        assert!(matches!(
            selection_error(&terms, root),
            FpAdapterError::Invalid(_)
        ));
        let mut root = a;
        for _ in 0..13 {
            root = selection_choose(&mut terms, form, c, root, root);
        }
        assert!(matches!(
            selection_error(&terms, root),
            FpAdapterError::Unsupported(_)
        ));
    }
}

#[test]
fn original_work_and_storage_one_short_poison_without_new_allowance() {
    let mut terms = TermStore::new();
    let root = selection_constant(&mut terms);
    let namespace = ChcProblem::new();
    let (work, storage) = (Cell::new(0usize), Cell::new(0usize));
    let mut count = |units, bytes| {
        work.set(work.get() + units);
        storage.set(storage.get() + bytes);
        Ok(())
    };
    let mut funded = WorkBudget::with_admission(10_000_000_000, &mut count);
    assert!(lower_fp_clause(&terms, &[root], &[], &namespace, &mut funded).is_ok());
    drop(funded);
    let mut poll = || ControlFlow::Continue(());
    let mut short = WorkBudget::new((work.get() - 1) as u64, &mut poll);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &[], &namespace, &mut short),
        Err(FpAdapterError::Owner(QueryError::Exhausted))
    ));
    assert_eq!(short.charge(0), Err(QueryError::Exhausted));
    drop(short);
    let mut zero = WorkBudget::new(0, &mut poll);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &[], &namespace, &mut zero),
        Err(FpAdapterError::Owner(QueryError::Exhausted))
    ));
    let remaining = Cell::new(storage.get() - 1);
    let permit = Cell::new(false);
    let mut admission = |_, bytes| {
        if permit.get() {
            return Ok(());
        }
        let Some(next) = remaining.get().checked_sub(bytes) else {
            return Err(QueryError::Exhausted);
        };
        remaining.set(next);
        Ok(())
    };
    let mut short = WorkBudget::with_admission(work.get() as u64, &mut admission);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &[], &namespace, &mut short),
        Err(FpAdapterError::Owner(QueryError::Exhausted))
    ));
    permit.set(true);
    assert_eq!(short.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn original_raw_callback_and_expired_end_refusals_remain_sticky() {
    owner::original_raw_callback_and_expired_end_refusals_remain_sticky();
}

#[test]
fn native_branch_progress_and_final_admission_refuse_on_same_owner() {
    owner::native_branch_progress_and_final_admission_refuse_on_same_owner();
}

mod owner;
mod symbolic;
