// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::term::{Constant, Symbol};
use num_bigint::BigInt;

mod resources;

fn fresh(store: &mut TermStore) -> Result<TermId> {
    store.try_fresh_bv64_binder_with_progress(&mut |_, _| true)
}

fn spelling(store: &TermStore, id: TermId) -> &str {
    match store.get(id) {
        TermData::Var(name, _) => name,
        _ => panic!("fresh binder is a Var"),
    }
}

#[test]
fn fixed_bv64_factory_registers_a_new_identity_without_touching_original_names() {
    let mut store = TermStore::new();
    let original = store.mk_var("original", Sort::Bool);
    let birth = store.entry_stamp(original);
    let metadata = store.checker_visible_metadata_generation();
    let before = store.snapshot_stamp();
    let binder = fresh(&mut store).expect("fresh bounded DATA");
    assert_eq!(store.sort(binder), &Sort::bitvec(64));
    assert_eq!(spelling(&store, binder), "__ay_range_pin!1");
    assert_eq!(store.find_var(spelling(&store, binder)), Some(binder));
    assert_eq!(store.find_var("original"), Some(original));
    assert_eq!(store.entry_stamp(original), birth);
    assert_eq!(store.var_counter(), 2);
    assert_eq!(store.checker_visible_metadata_generation(), metadata);
    assert!(before.is_append_only_prefix_of(&store));
}

#[test]
fn an_existing_declared_internal_spelling_is_never_reused_at_another_sort() {
    let mut store = TermStore::new();
    let declared = store.mk_var("__ay_range_pin!9", Sort::bitvec(8));
    let binder = fresh(&mut store).expect("distinct fixed-purpose name");
    assert_eq!(spelling(&store, binder), "__ay_range_pin!10");
    assert_ne!(declared, binder);
    assert_eq!(store.find_var("__ay_range_pin!9"), Some(declared));
    assert_eq!(store.sort(declared), &Sort::bitvec(8));
    assert_eq!(store.var_counter(), 11);
}

#[test]
fn unregistered_function_names_and_inactive_nodes_are_in_the_capture_scan() {
    let mut store = TermStore::new();
    let uf = store.mk_app(Symbol::named("__ay_range_pin!41"), [], Sort::Bool);
    assert_eq!(store.find_var("__ay_range_pin!41"), None);
    let binder = fresh(&mut store).expect("whole arena, not just roots");
    assert_eq!(spelling(&store, binder), "__ay_range_pin!42");
    assert!(matches!(store.get(uf), TermData::App(_, _)));
    assert_eq!(store.var_counter(), 43);
}

#[test]
fn older_unregistered_var_identity_is_not_grafted_into_a_new_binder() {
    let mut store = TermStore::new();
    let raw = store.intern(
        TermData::Var("__ay_range_pin!91".to_owned(), 97),
        Sort::Bool,
    );
    assert_eq!(store.find_var("__ay_range_pin!91"), None);
    let binder = fresh(&mut store).expect("preserve old raw source node");
    assert_eq!(spelling(&store, binder), "__ay_range_pin!98");
    assert_ne!(raw, binder);
    assert!(matches!(store.get(binder), TermData::Var(_, 98)));
    assert_eq!(store.var_counter(), 99);
}

#[test]
fn let_and_both_quantifier_binder_lists_remain_in_the_complete_name_scan() {
    let mut store = TermStore::new();
    let t = store.true_term();
    let _ = store.mk_let(vec![("__ay_range_pin!12".to_owned(), t)], t);
    let _ = store.mk_forall(vec![("__ay_range_pin!24".to_owned(), Sort::Bool)], t);
    let _ = store.mk_exists(vec![("__ay_range_pin!35".to_owned(), Sort::Bool)], t);
    let binder = fresh(&mut store).expect("nested lexical names retained");
    assert_eq!(spelling(&store, binder), "__ay_range_pin!36");
    assert_eq!(store.var_counter(), 37);
}

#[test]
fn indexed_function_spelling_is_also_excluded_without_copying_its_payload() {
    let mut store = TermStore::new();
    let _ = store.mk_app(
        Symbol::indexed("__ay_range_pin!71", vec![1, 2]),
        [],
        Sort::Bool,
    );
    let binder = fresh(&mut store).expect("symbol namespace scan");
    assert_eq!(spelling(&store, binder), "__ay_range_pin!72");
}

#[test]
fn real_rollback_prunes_registry_but_never_rewinds_freshness_or_birth() {
    let mut store = TermStore::new();
    let checkpoint = store.rollback_checkpoint();
    let first = fresh(&mut store).expect("first binder");
    let name = spelling(&store, first).to_owned();
    let birth = store.entry_stamp(first);
    store.rollback_to(checkpoint);
    assert_eq!(store.find_var(&name), None);
    assert_eq!(store.var_counter(), 1);
    let second = fresh(&mut store).expect("fresh after real rollback");
    assert_eq!(first, second);
    assert_ne!(spelling(&store, second), name);
    assert_ne!(store.entry_stamp(second), birth);
    assert_eq!(store.var_counter(), 2);
}

#[test]
fn producer_clone_owns_its_registry_and_a_distinct_arena_identity() {
    let mut source = TermStore::new();
    let first = fresh(&mut source).expect("original producer");
    let prefix = source.snapshot_stamp();
    let mut cloned = source.clone();
    let second = fresh(&mut cloned).expect("cloned producer");
    assert_eq!(source.len() + 1, cloned.len());
    assert_ne!(spelling(&cloned, second), spelling(&source, first));
    assert_eq!(source.var_counter(), 1);
    assert_eq!(cloned.var_counter(), 2);
    assert!(!prefix.is_append_only_prefix_of(&cloned));
    assert_eq!(cloned.find_var(spelling(&source, first)), Some(first));
}

#[test]
fn empty_populated_and_cloned_checker_snapshots_cannot_create_registry_authority() {
    let producer = TermStore::new();
    let mut populated = TermStore::from_entries(
        producer.entries_snapshot(),
        Some(producer.true_term()),
        Some(producer.false_term()),
        0,
    );
    let mut empty = TermStore::from_entries(Vec::new(), None, None, 0);
    let mut cloned = populated.clone();
    for store in [&mut populated, &mut empty, &mut cloned] {
        let len = store.len();
        assert_eq!(
            fresh(store),
            Err(ControlledTermInternError::ReadOnlySnapshot)
        );
        assert_eq!(store.len(), len);
        assert!(store.names.is_empty());
    }
}

#[test]
fn checked_counter_exhaustion_never_saturates_reuses_or_wraps() {
    let mut store = TermStore::new();
    store.var_counter = u32::MAX - 1;
    let binder = fresh(&mut store).expect("last admitted counter");
    assert_eq!(spelling(&store, binder), "__ay_range_pin!4294967294");
    assert_eq!(store.var_counter(), u32::MAX);
    let len = store.len();
    assert_eq!(
        fresh(&mut store),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(store.len(), len);
    assert_eq!(store.var_counter(), u32::MAX);
}

#[test]
fn exhausted_reserved_spelling_refuses_before_owning_copies_or_counter_mutation() {
    let mut store = TermStore::new();
    let _ = store.mk_app(Symbol::named("__ay_range_pin!4294967295"), [], Sort::Bool);
    let len = store.len();
    let mut copied_bytes = 0;
    assert_eq!(
        store.try_fresh_bv64_binder_with_progress(&mut |_, bytes| {
            copied_bytes += bytes;
            true
        }),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(copied_bytes, 0);
    assert_eq!(store.var_counter(), 0);
    assert_eq!(store.len(), len);
}

#[test]
fn generic_public_interning_still_refuses_a_caller_chosen_var_identity() {
    let mut store = TermStore::new();
    let term = TermData::Var("__ay_range_pin!0".to_owned(), 0);
    assert_eq!(
        store.try_intern_with_progress(&term, &Sort::bitvec(64), &mut |_, _| true),
        Err(ControlledTermInternError::UnsupportedFragment)
    );
    assert_eq!(store.var_counter(), 0);
    assert!(store.names.is_empty());
    assert_eq!(
        fresh(&mut store).map(|id| spelling(&store, id).to_owned()),
        Ok("__ay_range_pin!0".to_owned())
    );
}

#[test]
fn successful_term_and_registry_heap_counters_match_the_legacy_healthy_policy() {
    let mut store = TermStore::new();
    let instance = store.instance_term_bytes;
    let heap = store.heap_data_bytes;
    let buckets = store.bucket_capacity_bytes;
    let binder = fresh(&mut store).expect("complete registered DATA");
    let name = spelling(&store, binder);
    let key = store
        .names
        .get_key_value(name)
        .expect("registered exact key")
        .0;
    let registry_heap = key.capacity() + size_of::<(TermId, Sort)>();
    let term_heap = TermStore::heap_size(store.get(binder));
    let bucket_growth = store.bucket_capacity_bytes - buckets;
    assert_eq!(store.heap_data_bytes - heap, term_heap + registry_heap);
    assert_eq!(
        store.instance_term_bytes - instance,
        size_of::<crate::term::TermEntry>() + term_heap + registry_heap + bucket_growth
    );
}

#[test]
fn fresh_binder_and_existing_controlled_app_form_the_exact_lambda_representation() {
    let mut store = TermStore::new();
    let mut progress = |_: usize, _: usize| true;
    let binder = store
        .try_fresh_bv64_binder_with_progress(&mut progress)
        .expect("fresh BV64");
    let cell = TermData::Const(Constant::BitVec {
        value: BigInt::from(7u8),
        width: 8,
    });
    let value = store
        .try_intern_with_progress(&cell, &Sort::bitvec(8), &mut progress)
        .expect("closed cell DATA");
    let array_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let constant = TermData::App(Symbol::named("const-array"), vec![value]);
    let array = store
        .try_intern_with_progress(&constant, &array_sort, &mut progress)
        .expect("closed finite DATA");
    let select = TermData::App(Symbol::named("select"), vec![array, binder]);
    let body = store
        .try_intern_with_progress(&select, &Sort::bitvec(8), &mut progress)
        .expect("typed raw body DATA");
    let lambda = TermData::App(Symbol::named("lambda-array"), vec![binder, body]);
    let output = store
        .try_intern_with_progress(&lambda, &array_sort, &mut progress)
        .expect("existing exact raw representation");
    assert_eq!(store.get_lambda_array(output), Some((binder, body)));
    assert_eq!(store.get(output), &lambda);
    assert_eq!(store.sort(output), &array_sort);
}

#[test]
fn integer_factory_preserves_full_freshness_and_original_stop_admission() {
    let mut store = TermStore::new();
    let original = store.mk_var("__ay_range_pin!73", Sort::Bool);
    let born = store.entry_stamp(original);
    let binder = store
        .try_fresh_int_binder_with_progress(&mut |_, _| true)
        .unwrap();
    assert_eq!(store.sort(binder), &Sort::Int);
    assert_ne!(binder, original);
    assert_eq!(spelling(&store, binder), "__ay_range_pin!74");
    assert_eq!(store.entry_stamp(original), born);
    assert_eq!(store.find_var("__ay_range_pin!73"), Some(original));
    let before = store.var_counter();
    assert_eq!(
        store.try_fresh_int_binder_with_progress(&mut |_, _| false),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(store.var_counter(), before);
    let bv = fresh(&mut store).unwrap();
    assert_eq!(store.sort(bv), &Sort::bitvec(64));
    assert_ne!(bv, binder);
}
