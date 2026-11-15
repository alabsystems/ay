// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::TermStore;

#[test]
fn capsule_records_wide_store_read_exact_ids_values_and_edges() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let array = terms.mk_var("a", sort.clone());
    let key = terms.mk_bitvec(1.into(), 64);
    let value = terms.mk_bitvec(9.into(), 32);
    let stored = terms.mk_app(Symbol::named("store"), [array, key, value], sort);
    let selected = terms.mk_app(Symbol::named("select"), [stored, key], Sort::bitvec(32));
    let equality = terms.mk_eq(selected, value);
    let root = terms.mk_not_raw(equality);
    let entries = terms.entries_snapshot();
    let capsule = read(&entries, &[root]);
    assert!(capsule.complete);
    assert_eq!(capsule.roots[0], root);
    assert_eq!(capsule.node_count, 7);
    assert_eq!(capsule.edge_count, 8);
    let store = capsule.nodes[..capsule.node_count]
        .iter()
        .find(|n| n.id == stored)
        .unwrap();
    assert_eq!(
        &capsule.edges[store.first..store.first + store.count],
        &[array, key, value]
    );
    let key_node = capsule.nodes[..capsule.node_count]
        .iter()
        .find(|n| n.id == key)
        .unwrap();
    assert_eq!(key_node.kind, Kind::Bv(1, 64));
    let array_node = capsule.nodes[..capsule.node_count]
        .iter()
        .find(|n| n.id == array)
        .unwrap();
    assert!(array_node.shape.array);
    assert_eq!(
        (array_node.shape.index_width, array_node.shape.width),
        (64, 32)
    );
}

#[test]
fn capsule_preserves_repeated_root_and_operand_occurrences() {
    let entries = vec![
        (TermData::Const(Constant::Bool(true)), Sort::Bool),
        (
            TermData::App(Symbol::named("and"), vec![TermId(0), TermId(0)]),
            Sort::Bool,
        ),
    ];
    let capsule = read(&entries, &[TermId(1), TermId(1)]);
    assert!(capsule.complete);
    assert_eq!(
        (capsule.root_count, capsule.node_count, capsule.edge_count),
        (2, 2, 2)
    );
    assert_eq!(&capsule.roots[..2], &[TermId(1), TermId(1)]);
    assert_eq!(&capsule.edges[..2], &[TermId(0), TermId(0)]);
}

#[test]
fn capsule_bounds_nodes_edges_and_operator_bytes_without_rendering_payloads() {
    let mut entries = vec![(TermData::Const(Constant::Bool(true)), Sort::Bool)];
    for i in 0..32 {
        entries.push((TermData::Not(TermId(i)), Sort::Bool));
    }
    assert!(!read(&entries, &[TermId(32)]).complete);
    assert!(read(&entries, &[TermId(31)]).complete);
    let args = vec![TermId(0); 129];
    entries.push((TermData::App(Symbol::named("and"), args), Sort::Bool));
    assert!(!read(&entries, &[TermId(33)]).complete);
    entries.push((
        TermData::App(Symbol::named("x".repeat(33)), vec![]),
        Sort::Bool,
    ));
    assert!(!read(&entries, &[TermId(34)]).complete);
}

#[test]
fn capsule_missing_cycles_indexed_nested_sorts_and_invalid_constants_are_incomplete() {
    let mut entries = vec![(TermData::Not(TermId(0)), Sort::Bool)];
    assert!(!read(&entries, &[TermId(0)]).complete);
    assert!(!read(&entries, &[TermId(1)]).complete);
    entries.push((
        TermData::App(Symbol::indexed("extract", vec![1, 0]), vec![]),
        Sort::bitvec(2),
    ));
    assert!(!read(&entries, &[TermId(1)]).complete);
    let nested = Sort::array(Sort::bitvec(64), Sort::array(Sort::Bool, Sort::Bool));
    entries.push((TermData::Var("nested".to_owned(), 0), nested));
    assert!(!read(&entries, &[TermId(2)]).complete);
    entries.push((
        TermData::Const(Constant::BitVec {
            value: 256u32.into(),
            width: 8,
        }),
        Sort::bitvec(8),
    ));
    assert!(!read(&entries, &[TermId(3)]).complete);
}
