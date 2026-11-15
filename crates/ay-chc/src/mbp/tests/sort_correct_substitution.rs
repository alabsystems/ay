// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An array variable projection substitutes is replaced by a term of its own
//! sort (#mbp-sort-correct-substitution).
//!
//! The model-value fallback answered the `Int` 0 for every sort it did not
//! list, arrays included, so an array variable the projection could not
//! eliminate became `(select 0 k)`. Measured on model-checker-consumer's per-row CHC route
//! (`error_p9` of `safe_static_bytes`): the inliner's back-translation of the
//! BV-native discharge projected the original memory array away that way, the
//! translated proof's clause 2 could only be checked `UNKNOWN`, and the row
//! stayed `unknown`.

use super::*;

fn mem_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)))
}

#[test]
fn an_array_without_a_model_value_defaults_to_a_const_array_of_its_sort() {
    let mem = ChcVar::new("mem", mem_sort());
    let default = Mbp::model_value_expr_or_default(&mem, &FxHashMap::default());
    assert_eq!(
        default,
        ChcExpr::const_array(ChcSort::BitVec(64), ChcExpr::BitVec(0, 8))
    );
    assert_eq!(default.sort(), mem_sort());
}

#[test]
fn an_array_model_value_becomes_a_store_chain_over_its_default() {
    let mem = ChcVar::new("mem", mem_sort());
    let mut model = FxHashMap::default();
    model.insert(
        "mem".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::BitVec(0, 8)),
            entries: vec![(SmtValue::BitVec(0x4_0000_0000, 64), SmtValue::BitVec(4, 8))],
        },
    );
    let value = Mbp::model_value_expr_or_default(&mem, &model);
    assert_eq!(
        value,
        ChcExpr::store(
            ChcExpr::const_array(ChcSort::BitVec(64), ChcExpr::BitVec(0, 8)),
            ChcExpr::BitVec(0x4_0000_0000, 64),
            ChcExpr::BitVec(4, 8),
        )
    );
    assert_eq!(value.sort(), mem_sort());
}

/// Nested arrays default element-wise.
#[test]
fn a_nested_array_defaults_to_nested_const_arrays() {
    let inner = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool));
    let outer = ChcSort::Array(Box::new(ChcSort::Int), Box::new(inner));
    let var = ChcVar::new("grid", outer.clone());
    let default = Mbp::model_value_expr_or_default(&var, &FxHashMap::default());
    assert_eq!(default.sort(), outer);
}

/// A value whose kind does not match the sort has no literal: the default
/// takes over, still of the variable's own sort.
#[test]
fn a_mismatched_model_value_falls_back_to_the_sort_default() {
    let mem = ChcVar::new("mem", mem_sort());
    let mut model = FxHashMap::default();
    model.insert("mem".to_string(), SmtValue::Int(0));
    assert_eq!(Mbp::model_value_expr(&mem, &model), None);
    assert_eq!(
        Mbp::model_value_expr_or_default(&mem, &model).sort(),
        mem_sort()
    );
}

#[test]
fn unsupported_array_element_never_becomes_an_integer_default() {
    let sort = ChcSort::Array(
        Box::new(ChcSort::BitVec(64)),
        Box::new(ChcSort::Uninterpreted("opaque".to_string())),
    );
    let var = ChcVar::new("opaque_memory", sort);
    let result = Mbp::model_value_expr_or_default(&var, &FxHashMap::default());
    assert_eq!(result, ChcExpr::Var(var));
}

#[test]
fn wrong_array_index_or_element_width_is_not_an_array_model_literal() {
    let mem = ChcVar::new("mem", mem_sort());
    for (index, element) in [
        (SmtValue::BitVec(0, 32), SmtValue::BitVec(1, 8)),
        (SmtValue::BitVec(0, 64), SmtValue::BitVec(1, 16)),
    ] {
        let mut model = FxHashMap::default();
        model.insert(
            mem.name.clone(),
            SmtValue::ArrayMap {
                default: Box::new(SmtValue::BitVec(0, 8)),
                entries: vec![(index, element)],
            },
        );
        assert!(Mbp::model_value_expr(&mem, &model).is_none());
        assert_eq!(
            Mbp::model_value_expr_or_default(&mem, &model).sort(),
            mem_sort()
        );
    }
}

#[test]
fn a_one_shot_original_stop_cannot_revive_through_default_fallback() {
    use ay_core::resource::enter_check_stop;
    use std::sync::atomic::{AtomicUsize, Ordering};
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let _scope = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst) == 0
    }));
    let mem = ChcVar::new("mem", mem_sort());
    let mut model = FxHashMap::default();
    model.insert(
        mem.name.clone(),
        SmtValue::ConstArray(Box::new(SmtValue::BitVec(0, 8))),
    );
    assert_eq!(
        Mbp::model_value_expr_or_default(&mem, &model),
        ChcExpr::Var(mem)
    );
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn mid_conversion_and_terminal_stops_never_return_a_default_candidate() {
    use ay_core::resource::enter_check_stop;
    use std::sync::atomic::{AtomicUsize, Ordering};
    let mem = ChcVar::new("mem", mem_sort());
    let mut model = FxHashMap::default();
    model.insert(
        mem.name.clone(),
        SmtValue::ConstArray(Box::new(SmtValue::BitVec(7, 8))),
    );
    // A const-array conversion offers root, key, element, then terminal poll.
    for refuse_at in 1..4 {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = calls.clone();
        let _scope = enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst) == refuse_at
        }));
        assert_eq!(
            Mbp::model_value_expr_or_default(&mem, &model),
            ChcExpr::Var(mem.clone())
        );
        assert_eq!(calls.load(Ordering::SeqCst), refuse_at + 1);
    }
}

#[test]
fn original_guard_budget_is_consumed_without_a_fresh_fallback_allowance() {
    use ay_core::resource::{ChildSpec, Guard, NodeLabel};
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(2)));
    let _scope = guard.enter();
    let mem = ChcVar::new("mem", mem_sort());
    assert_eq!(
        Mbp::model_value_expr_or_default(&mem, &FxHashMap::default()),
        ChcExpr::Var(mem)
    );
    assert!(guard.exhausted().is_some());
}
