// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcOp, ChcSort, ChcVar};
use ay_core::original_query::FiniteAdmissionGrant;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

fn owner(work: u64, storage: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, storage),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn ample() -> CountedAdmission {
    owner(100_000_000, 512 * 1024 * 1024)
}

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn relation() -> ChcExpr {
    op(
        ChcOp::Eq,
        vec![
            op(
                ChcOp::BvAdd,
                vec![var("x", ChcSort::BitVec(8)), ChcExpr::BitVec(1, 8)],
            ),
            ChcExpr::BitVec(2, 8),
        ],
    )
}

#[test]
fn original_shared_dag_is_counted_without_tree_unfolding() {
    let mut child = Arc::new(ChcExpr::Bool(true));
    for _ in 0..80 {
        child = Arc::new(ChcExpr::Op(ChcOp::And, vec![child.clone(), child]));
    }
    let admission = ample();
    let query = read(child.as_ref(), &admission).unwrap();
    assert_eq!(query.census.nodes, 81);
    assert_eq!(query.census.edges, 160);
    assert_eq!(query.nodes.len(), 81);
    assert_eq!(query.node_index(child.as_ref()).unwrap(), 80);
    assert_eq!(query.types.get(0).unwrap(), types::Type::Bool);
    assert!(std::ptr::eq(query.original, child.as_ref()));
    assert_eq!(admission.deadline(), None);
}

#[test]
fn retained_node_lookup_cannot_replace_an_exhausted_original_owner() {
    let expr = relation();
    let admission = ample();
    let query = read(&expr, &admission).unwrap();
    let before = admission.usage().unwrap().work_admitted;
    assert_eq!(query.node_index(&expr).unwrap(), query.nodes.len() - 1);
    assert_eq!(admission.usage().unwrap().work_admitted, before + 1);
    admission.refuse(CountedAdmissionError::WorkExhausted);
    drop(admission);
    let unrelated = ample();
    assert_eq!(
        query.node_index(&expr),
        Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
    );
    assert_eq!(unrelated.usage().unwrap().work_admitted, 0);
}

#[test]
fn scan_above_the_old_routing_cap_remains_bool_without_a_datatype_slice() {
    let count = 131_073;
    let expr = ChcExpr::Op(
        ChcOp::And,
        (0..count).map(|_| Arc::new(ChcExpr::Bool(true))).collect(),
    );
    let admission = ample();
    let query = read(&expr, &admission).unwrap();
    assert_eq!(query.census.nodes, count + 1);
    assert_eq!(query.census.edges, count);
    assert!(!query.census.has_arrays);
    assert_eq!(admission.deadline(), None);
    assert!(admission.usage().unwrap().work_admitted > count as u64);
}

#[test]
fn exact_and_one_short_original_work_and_storage_are_terminal() {
    let expr = relation();
    let baseline = ample();
    drop(read(&expr, &baseline).unwrap());
    let used = baseline.usage().unwrap();
    for (work, bytes, expected) in [
        (used.work_admitted, used.storage_admitted, None),
        (
            used.work_admitted - 1,
            used.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            used.work_admitted,
            used.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let admission = owner(work, bytes);
        let result = read(&expr, &admission);
        if let Some(expected) = expected {
            assert!(matches!(result, Err(Error::Stopped(error)) if error == expected));
            assert_eq!(admission.clone().check(), Err(expected));
            assert!(matches!(
                read(&ChcExpr::Bool(true), &admission),
                Err(Error::Stopped(_))
            ));
        } else {
            drop(result.unwrap());
            assert_eq!(admission.usage().unwrap().work_remaining, 0);
            assert_eq!(admission.usage().unwrap().storage_remaining, 0);
        }
    }
}

#[test]
fn zero_effort_refuses_both_boolean_literals_before_any_admission() {
    for value in [false, true] {
        let admission = owner(0, 1000);
        assert!(matches!(
            read(&ChcExpr::Bool(value), &admission),
            Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
        ));
        assert_eq!(admission.usage().unwrap().work_admitted, 0);
    }
}

#[test]
fn original_cancellation_survives_scope_replacement_and_flag_reset() {
    use ay_core::resource::enter_check_stop;
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = stopped.clone();
    let original = enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let admission = ample();
    drop(original);
    let _replacement = enter_check_stop(Arc::new(|| false));
    stopped.store(true, Ordering::SeqCst);
    assert!(matches!(
        read(&relation(), &admission),
        Err(Error::Stopped(_))
    ));
    stopped.store(false, Ordering::SeqCst);
    assert!(admission.check().is_err());
    assert!(matches!(
        read(&ChcExpr::Bool(true), &admission),
        Err(Error::Stopped(_))
    ));
}

#[test]
fn arrays_are_fully_typed_including_stores_selects_and_dead_branches() {
    let array = ChcExpr::ConstArray(ChcSort::BitVec(8), Arc::new(ChcExpr::BitVec(0, 16)));
    let store = op(
        ChcOp::Store,
        vec![array.clone(), ChcExpr::BitVec(3, 8), ChcExpr::BitVec(7, 16)],
    );
    let select = op(ChcOp::Select, vec![store, ChcExpr::BitVec(3, 8)]);
    let query = op(ChcOp::Eq, vec![select, ChcExpr::BitVec(7, 16)]);
    let admitted = read(&query, &ample()).unwrap();
    assert!(admitted.census.has_arrays);
    assert_eq!(admitted.census.max_bitvector_width, 16);
    let bad_select = op(ChcOp::Select, vec![array.clone(), ChcExpr::BitVec(3, 16)]);
    let dead = op(
        ChcOp::And,
        vec![
            ChcExpr::Bool(false),
            op(ChcOp::Eq, vec![bad_select, ChcExpr::BitVec(0, 16)]),
        ],
    );
    assert!(matches!(read(&dead, &ample()), Err(Error::IllTyped)));
    let bad_store = op(
        ChcOp::Store,
        vec![array.clone(), ChcExpr::BitVec(3, 8), ChcExpr::Bool(true)],
    );
    assert!(matches!(
        read(&op(ChcOp::Eq, vec![bad_store, array]), &ample()),
        Err(Error::IllTyped)
    ));
}

#[test]
fn widths_arity_and_root_sort_never_become_boolean_shortcuts() {
    for bad in [
        ChcExpr::BitVec(0, 0),
        ChcExpr::BitVec(4, 2),
        ChcExpr::BitVec(0, crate::MAX_BITVECTOR_WIDTH + 1),
        op(
            ChcOp::BvAdd,
            vec![ChcExpr::BitVec(1, 8), ChcExpr::BitVec(1, 16)],
        ),
        op(ChcOp::BvExtract(8, 0), vec![ChcExpr::BitVec(0, 8)]),
        op(ChcOp::Not, vec![ChcExpr::Bool(true), ChcExpr::Bool(false)]),
    ] {
        let expr = op(
            ChcOp::Ite,
            vec![ChcExpr::Bool(true), ChcExpr::Bool(true), bad],
        );
        assert!(matches!(read(&expr, &ample()), Err(Error::IllTyped)));
    }
    assert!(matches!(
        read(&ChcExpr::BitVec(0, 8), &ample()),
        Err(Error::IllTyped)
    ));
}

#[test]
fn unsupported_fragments_are_not_counted_solver_or_typing_success() {
    for child in [
        ChcExpr::Int(0),
        ChcExpr::Real(0, 1),
        ChcExpr::FuncApp("f".into(), ChcSort::Bool, Vec::new()),
        ChcExpr::ConstArrayMarker(ChcSort::BitVec(8)),
        var("u", ChcSort::Uninterpreted("U".into())),
    ] {
        let expr = op(ChcOp::And, vec![ChcExpr::Bool(false), child]);
        assert!(matches!(read(&expr, &ample()), Err(Error::Unsupported)));
    }
    let converted = op(ChcOp::Bv2Nat, vec![ChcExpr::BitVec(1, 8)]);
    assert!(matches!(
        read(&converted, &ample()),
        Err(Error::Unsupported)
    ));
}

#[test]
fn same_spelling_with_distinct_declared_sorts_is_not_an_alias() {
    let expr = op(
        ChcOp::And,
        vec![
            var("same", ChcSort::Bool),
            op(
                ChcOp::Eq,
                vec![var("same", ChcSort::BitVec(8)), ChcExpr::BitVec(7, 8)],
            ),
        ],
    );
    let query = read(&expr, &ample()).unwrap();
    assert_eq!(query.census.variable_occurrences, 2);
    assert_eq!(query.census.name_bytes, 8);
    assert_eq!(query.census.bitvector_nodes, 2);
    assert_eq!(query.census.bitvector_width_sum, 16);
}

#[test]
fn deeply_nested_array_sorts_are_iterative_and_include_unobserved_widths() {
    fn nested() -> ChcSort {
        let mut sort = ChcSort::BitVec(257);
        for _ in 0..512 {
            sort = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(sort));
        }
        sort
    }
    let expr = op(
        ChcOp::Eq,
        vec![var("left", nested()), var("right", nested())],
    );
    let query = read(&expr, &ample()).unwrap();
    assert_eq!(query.census.nodes, 3);
    assert_eq!(query.census.bitvector_nodes, 0);
    assert_eq!(query.census.max_bitvector_width, 257);
    assert!(query.census.has_arrays);
    assert_eq!(query.nodes[0].1, query.nodes[1].1);
}

#[test]
fn cancellation_during_a_shared_walk_stays_terminal_after_observer_reset() {
    let calls = Arc::new(AtomicUsize::new(0));
    let enabled = Arc::new(AtomicBool::new(true));
    let observed_calls = calls.clone();
    let observed_enabled = enabled.clone();
    let admission = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000, 1024 * 1024),
        None,
        Arc::new(move || {
            observed_calls.fetch_add(1, Ordering::SeqCst) > 80
                && observed_enabled.load(Ordering::SeqCst)
        }),
    )
    .unwrap();
    let mut child = Arc::new(ChcExpr::Bool(true));
    for _ in 0..80 {
        child = Arc::new(ChcExpr::Op(ChcOp::And, vec![child.clone(), child]));
    }
    assert!(matches!(read(&child, &admission), Err(Error::Stopped(_))));
    assert!(admission.usage().unwrap().work_admitted > 1);
    enabled.store(false, Ordering::SeqCst);
    assert!(admission.clone().check().is_err());
    assert!(matches!(
        read(&ChcExpr::Bool(true), &admission),
        Err(Error::Stopped(_))
    ));
}
