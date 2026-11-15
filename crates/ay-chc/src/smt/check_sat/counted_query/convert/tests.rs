// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::super::read;
use super::*;
use crate::{ChcOp, ChcSort, ChcVar};
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant};
use ay_core::{Constant, Sort, Symbol, TermData};
use std::sync::Arc;

mod cnf;
mod resources;
mod signatures;

fn owner(work: u64, bytes: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn ample() -> CountedAdmission {
    owner(100_000_000, 512 * 1024 * 1024)
}

fn op(op: ChcOp, children: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, children.into_iter().map(Arc::new).collect())
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn convert<'a>(original: &'a ChcExpr, owner: &CountedAdmission) -> Result<Converted<'a>> {
    read(original, owner)?.into_terms()
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
fn shared_dag_postorder_is_preserved_without_unfolding_or_folding() {
    let mut node = Arc::new(ChcExpr::Bool(true));
    for _ in 0..80 {
        node = Arc::new(ChcExpr::Op(ChcOp::And, vec![node.clone(), node]));
    }
    let original = ample();
    let built = convert(&node, &original).unwrap();
    assert_eq!(built.census().nodes, 81);
    assert_eq!(built.node_terms.len(), 81);
    assert_eq!(built.terms().len(), 82); // includes the native false literal
    assert!(std::ptr::eq(built.original(), node.as_ref()));
    for &(source, _) in &built.query.nodes {
        if let ChcExpr::Op(_, args) = source {
            let id = built.term_for(source).unwrap();
            let child = built.term_for(&args[0]).unwrap();
            assert!(
                matches!(built.terms().get(id), TermData::App(name, children)
                if name.name() == "and" && children == &[child, child])
            );
        }
    }
    assert_eq!(original.deadline(), None);
    built.finish().unwrap();
}

#[test]
fn source_pointer_mapping_is_not_replaced_by_structural_interning() {
    let left = Arc::new(ChcExpr::Bool(true));
    let right = Arc::new(ChcExpr::Bool(true));
    let source = ChcExpr::Op(ChcOp::And, vec![left.clone(), right.clone()]);
    let built = convert(&source, &ample()).unwrap();
    assert_ne!(
        built.query.node_index(&left),
        built.query.node_index(&right)
    );
    assert_eq!(built.term_for(&left), built.term_for(&right));
    assert_eq!(built.node_terms.len(), 3);
    let foreign = ChcExpr::Bool(true);
    assert_eq!(built.term_for(&foreign), Err(Error::IllTyped));
}

#[test]
fn original_wide_root_above_the_old_131072_scan_cap_keeps_every_edge() {
    let count = 131_073;
    let source = ChcExpr::Op(
        ChcOp::And,
        (0..count).map(|_| Arc::new(ChcExpr::Bool(true))).collect(),
    );
    let built = convert(&source, &ample()).unwrap();
    assert_eq!(built.census().nodes, count + 1);
    assert_eq!(built.node_terms.len(), count + 1);
    assert_eq!(built.terms().len(), 3);
    assert!(
        matches!(built.terms().get(built.root()), TermData::App(name, children)
        if name.name() == "and" && children.len() == count)
    );
}

#[test]
fn same_spelling_distinct_sorts_and_repeated_typed_bindings_remain_exact() {
    let a = Arc::new(var("same", ChcSort::Bool));
    let repeat = Arc::new(var("same", ChcSort::Bool));
    let b = Arc::new(var("same", ChcSort::BitVec(8)));
    let array_sort = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::Bool));
    let array = Arc::new(var("same", array_sort));
    let source = ChcExpr::Op(
        ChcOp::And,
        vec![
            a.clone(),
            repeat.clone(),
            Arc::new(ChcExpr::Op(ChcOp::Eq, vec![b.clone(), b.clone()])),
            Arc::new(ChcExpr::Op(ChcOp::Select, vec![array.clone(), b.clone()])),
        ],
    );
    let built = convert(&source, &ample()).unwrap();
    let a_id = built.term_for(&a).unwrap();
    let b_id = built.term_for(&b).unwrap();
    let array_id = built.term_for(&array).unwrap();
    assert_eq!(built.term_for(&repeat).unwrap(), a_id);
    assert_ne!(a_id, b_id);
    assert_ne!(a_id, array_id);
    assert_ne!(b_id, array_id);
    assert_eq!(built.bindings().len(), 3);
    for binding in built.bindings() {
        assert_eq!(binding.original.name, "same");
        assert!(
            matches!(built.terms().get(binding.term), TermData::Var(name, _) if name == "same")
        );
        assert!(matches!(
            &binding.original.sort,
            ChcSort::Bool | ChcSort::BitVec(8) | ChcSort::Array(..)
        ));
    }
    assert_eq!(built.terms().sort(a_id), &Sort::Bool);
    assert_eq!(built.terms().sort(b_id), &Sort::bitvec(8));
    assert_eq!(
        built.terms().sort(array_id),
        &Sort::array(Sort::bitvec(8), Sort::Bool)
    );
}

#[test]
fn arrays_const_store_select_and_ite_keep_original_raw_structure() {
    let zero = Arc::new(ChcExpr::BitVec(0, 257));
    let array = Arc::new(ChcExpr::ConstArray(ChcSort::BitVec(13), zero));
    let key = Arc::new(ChcExpr::BitVec(3, 13));
    let value = Arc::new(ChcExpr::BitVec(u128::MAX, 257));
    let stored = Arc::new(ChcExpr::Op(
        ChcOp::Store,
        vec![array.clone(), key.clone(), value.clone()],
    ));
    let choice = Arc::new(ChcExpr::Op(
        ChcOp::Ite,
        vec![Arc::new(ChcExpr::Bool(true)), stored.clone(), array.clone()],
    ));
    let selected = Arc::new(ChcExpr::Op(ChcOp::Select, vec![choice.clone(), key]));
    let source = ChcExpr::Op(ChcOp::Eq, vec![selected.clone(), value]);
    let built = convert(&source, &ample()).unwrap();
    assert!(built.census().has_arrays);
    assert!(
        matches!(built.terms().get(built.term_for(&array).unwrap()), TermData::App(name, _) if name.name() == "const-array")
    );
    assert!(
        matches!(built.terms().get(built.term_for(&stored).unwrap()), TermData::App(name, _) if name.name() == "store")
    );
    assert!(matches!(
        built.terms().get(built.term_for(&choice).unwrap()),
        TermData::Ite(..)
    ));
    assert!(
        matches!(built.terms().get(built.term_for(&selected).unwrap()), TermData::App(name, _) if name.name() == "select")
    );
    assert_eq!(
        built.terms().sort(built.term_for(&selected).unwrap()),
        &Sort::bitvec(257)
    );
}

#[test]
fn native_sort_depth_limit_is_an_explicit_decline_not_a_query_success() {
    let mut sort = ChcSort::Bool;
    for _ in 0..257 {
        sort = ChcSort::Array(Box::new(ChcSort::Bool), Box::new(sort));
    }
    let value = Arc::new(var("deep", sort));
    let source = ChcExpr::Op(ChcOp::Eq, vec![value.clone(), value]);
    let original = ample();
    let query = read(&source, &original).unwrap();
    assert!(query.census.has_arrays); // the source census itself has no depth cap
    assert!(matches!(query.into_terms(), Err(Error::Unsupported)));
    assert!(original.check().is_ok());
}
