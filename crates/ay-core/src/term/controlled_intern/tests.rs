// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::sort::ArraySort;
use crate::term::Symbol;
use num_bigint::BigInt;

mod integer;
mod resources;
mod sequence;

fn app(store: &TermStore) -> TermData {
    TermData::App(Symbol::named("controlled_probe"), vec![store.true_term()])
}

fn intern(store: &mut TermStore, term: &TermData, sort: &Sort) -> Result<TermId> {
    store.try_intern_with_progress(term, sort, &mut |_, _| true)
}

#[test]
fn existing_constant_reuses_exact_id_and_birth_without_new_storage() {
    let mut store = TermStore::new();
    let id = store.true_term();
    let stamp = store.entry_stamp(id);
    let bytes = store.instance_term_bytes;
    let result = intern(
        &mut store,
        &TermData::Const(Constant::Bool(true)),
        &Sort::Bool,
    );
    assert_eq!(result, Ok(id));
    assert_eq!(store.entry_stamp(id), stamp);
    assert_eq!(store.instance_term_bytes, bytes);
}

#[test]
fn same_application_at_different_sorts_never_hash_aliases() {
    let mut store = TermStore::new();
    let term = TermData::App(Symbol::named("polymorphic_leaf"), Vec::new());
    let a = intern(&mut store, &term, &Sort::bitvec(8)).expect("bounded source");
    let b = intern(&mut store, &term, &Sort::bitvec(16)).expect("bounded source");
    assert_ne!(a, b);
    assert_eq!(intern(&mut store, &term, &Sort::bitvec(8)), Ok(a));
    assert_eq!(
        store.mk_app(Symbol::named("polymorphic_leaf"), [], Sort::bitvec(16)),
        b
    );
    assert_ne!(store.entry_stamp(a), store.entry_stamp(b));
}

#[test]
fn live_children_and_raw_store_order_are_preserved_without_simplification() {
    let mut store = TermStore::new();
    let index = store.mk_bitvec(BigInt::from(3u8), 64);
    let value = store.mk_bitvec(BigInt::from(9u8), 8);
    let sort = Sort::Array(Box::new(ArraySort::new(Sort::bitvec(64), Sort::bitvec(8))));
    let base = store.mk_var("original_array", sort.clone());
    let term = TermData::App(Symbol::named("store"), vec![base, index, value]);
    let id = intern(&mut store, &term, &sort).expect("whole typed row");
    assert_eq!(store.get(id), &term);
    assert_eq!(store.sort(id), &sort);
    assert_eq!(
        store.mk_app(Symbol::named("store"), [base, index, value], sort),
        id
    );
}

#[test]
fn bounded_boolean_nodes_retain_original_children() {
    let mut store = TermStore::new();
    let term = TermData::Ite(store.true_term(), store.false_term(), store.true_term());
    let id = intern(&mut store, &term, &Sort::Bool).expect("raw Ite");
    assert_eq!(store.get(id), &term);
    let not = TermData::Not(id);
    let negated = intern(&mut store, &not, &Sort::Bool).expect("raw Not");
    assert_eq!(store.get(negated), &not);
}

#[test]
fn controlled_append_preserves_prefix_identity_names_and_metadata() {
    let mut store = TermStore::new();
    let original = store.mk_var("retained_source", Sort::Bool);
    let stamp = store.entry_stamp(original);
    let prefix = store.snapshot_stamp();
    let counter = store.var_counter();
    let metadata = store.checker_visible_metadata_generation();
    let term = app(&store);
    let id = intern(&mut store, &term, &Sort::Bool).expect("append");
    assert!(prefix.is_append_only_prefix_of(&store));
    assert_ne!(prefix, store.snapshot_stamp());
    assert_eq!(store.find_var("retained_source"), Some(original));
    assert_eq!(store.entry_stamp(original), stamp);
    assert_eq!(store.var_counter(), counter);
    assert_eq!(store.checker_visible_metadata_generation(), metadata);
    assert_eq!(store.find_interned(&term), Some(id));
}

#[test]
fn producer_clone_keeps_role_but_owns_a_distinct_arena() {
    let store = TermStore::new();
    let before = store.snapshot_stamp();
    let mut cloned = store.clone();
    let term = app(&cloned);
    let id = intern(&mut cloned, &term, &Sort::Bool).expect("producer clone");
    assert!(!before.is_append_only_prefix_of(&cloned));
    assert_eq!(store.len() + 1, cloned.len());
    assert_eq!(cloned.find_interned(&term), Some(id));
    assert_eq!(
        store.entry_stamp(store.true_term()),
        cloned.entry_stamp(cloned.true_term())
    );
}

#[test]
fn rollback_reused_slot_receives_a_new_birth_stamp() {
    let mut store = TermStore::new();
    let checkpoint = store.rollback_checkpoint();
    let term = app(&store);
    let first = intern(&mut store, &term, &Sort::Bool).expect("first append");
    let first_stamp = store.entry_stamp(first);
    store.rollback_to(checkpoint);
    let second = intern(&mut store, &term, &Sort::Bool).expect("after real rollback");
    assert_eq!(first, second);
    assert_ne!(first_stamp, store.entry_stamp(second));
}

#[test]
fn empty_populated_and_cloned_checker_snapshots_cannot_mint() {
    let producer = TermStore::new();
    let mut checker = TermStore::from_entries(
        producer.entries_snapshot(),
        Some(producer.true_term()),
        Some(producer.false_term()),
        0,
    );
    let mut empty = TermStore::from_entries(Vec::new(), None, None, 0);
    let mut cloned = checker.clone();
    for target in [&mut checker, &mut empty, &mut cloned] {
        let len = target.len();
        assert_eq!(
            intern(target, &TermData::Const(Constant::Bool(true)), &Sort::Bool),
            Err(ControlledTermInternError::ReadOnlySnapshot)
        );
        assert_eq!(target.len(), len);
    }
}

#[test]
fn unsupported_owning_payloads_and_binders_refuse_without_minting() {
    let mut store = TermStore::new();
    let t = store.true_term();
    let unsupported = [
        TermData::Var("caller_selected_identity".to_owned(), 7),
        TermData::Const(Constant::String("owned".to_owned())),
        TermData::App(Symbol::indexed("extract", vec![7, 0]), vec![t]),
        TermData::App(Symbol::named("wide"), vec![t; 4]),
        TermData::App(Symbol::named("x".repeat(65)), Vec::new()),
        TermData::Let(Vec::new(), t),
        TermData::Forall(Vec::new(), t, Vec::new()),
        TermData::Exists(Vec::new(), t, Vec::new()),
    ];
    let before = store.len();
    for term in unsupported {
        assert_eq!(
            intern(&mut store, &term, &Sort::Bool),
            Err(ControlledTermInternError::UnsupportedFragment)
        );
        assert_eq!(store.len(), before);
    }
}

#[test]
fn unsupported_array_sorts_refuse_before_recursive_clone() {
    let mut store = TermStore::new();
    let term = TermData::App(Symbol::named("source"), Vec::new());
    let sorts = [
        Sort::bitvec(0),
        Sort::bitvec(129),
        Sort::Array(Box::new(ArraySort::new(Sort::bitvec(32), Sort::Bool))),
        Sort::Array(Box::new(ArraySort::new(
            Sort::bitvec(64),
            Sort::Seq(Box::new(Sort::Bool)),
        ))),
    ];
    let before = store.len();
    for sort in sorts {
        assert_eq!(
            intern(&mut store, &term, &sort),
            Err(ControlledTermInternError::UnsupportedFragment)
        );
        assert_eq!(store.len(), before);
    }
}

#[test]
fn malformed_constants_and_dead_children_refuse_without_indexing() {
    let mut store = TermStore::new();
    let original = store.len();
    for value in [BigInt::from(-1i8), BigInt::from(256u16)] {
        let term = TermData::Const(Constant::BitVec { value, width: 8 });
        assert_eq!(
            intern(&mut store, &term, &Sort::bitvec(8)),
            Err(ControlledTermInternError::InvalidInput)
        );
    }
    let bad = [
        TermData::Not(TermId::SENTINEL),
        TermData::Ite(store.true_term(), store.true_term(), TermId::SENTINEL),
        TermData::App(Symbol::named("select"), vec![TermId::SENTINEL]),
    ];
    for term in bad {
        assert_eq!(
            intern(&mut store, &term, &Sort::Bool),
            Err(ControlledTermInternError::InvalidInput)
        );
    }
    assert_eq!(store.len(), original);
}

#[test]
fn full_unsigned_bv128_constant_is_not_narrowed() {
    let mut store = TermStore::new();
    let value = (BigInt::from(1u8) << 128u32) - BigInt::from(1u8);
    let term = TermData::Const(Constant::BitVec {
        value: value.clone(),
        width: 128,
    });
    let id = intern(&mut store, &term, &Sort::bitvec(128)).expect("full width");
    assert_eq!(store.get(id), &term);
    assert_eq!(store.mk_bitvec(value, 128), id);
}

#[test]
fn successful_memory_counters_match_actual_owned_entry_and_bucket_growth() {
    let mut store = TermStore::new();
    let term = app(&store);
    let hash = TermStore::compute_hash(&term);
    let before_instance = store.instance_term_bytes;
    let before_heap = store.heap_data_bytes;
    let before_buckets = store.bucket_capacity_bytes;
    let old_capacity = store.hash_cons.get(&hash).map_or(0, Vec::capacity);
    let id = intern(&mut store, &term, &Sort::Bool).expect("credited append");
    let heap = TermStore::heap_size(store.get(id));
    let growth = (store
        .hash_cons
        .get(&hash)
        .expect("interned bucket")
        .capacity()
        - old_capacity)
        * size_of::<TermId>();
    assert_eq!(store.heap_data_bytes - before_heap, heap);
    assert_eq!(store.bucket_capacity_bytes - before_buckets, growth);
    assert_eq!(
        store.instance_term_bytes - before_instance,
        size_of::<TermEntry>() + heap + growth
    );
}
