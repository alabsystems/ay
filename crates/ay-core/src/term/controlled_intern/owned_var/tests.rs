// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::term::Symbol;

#[test]
fn owned_var_prefix_accounts_raw_names_ids_and_lexical_binders() {
    let mut store = TermStore::new();
    let truth = store.true_term();
    store.mk_app(Symbol::named("owned_41"), [], Sort::Bool);
    store.intern(TermData::Var("other".into(), 55), Sort::Bool);
    store.mk_let(vec![("owned_60".into(), truth)], truth);
    store.mk_forall(vec![("owned_70".into(), Sort::Int)], truth);
    store.mk_exists(vec![("owned_80".into(), Sort::Int)], truth);
    let sort = Sort::array(Sort::Int, Sort::seq(Sort::Real));
    let id = store
        .try_fresh_var_with_progress("owned", &sort, &mut |_, _| true)
        .unwrap();
    assert!(matches!(store.get(id), TermData::Var(name, 81) if name == "owned_81"));
    assert_eq!(store.sort(id), &sort);
    assert_eq!(store.find_var("owned_81"), Some(id));
    assert_eq!(store.var_counter(), 82);
}

#[test]
fn owned_var_exact_factory_refuses_every_retained_name_kind() {
    for kind in 0..6 {
        let mut store = TermStore::new();
        let truth = store.true_term();
        match kind {
            0 => {
                store.mk_var("occupied", Sort::Bool);
            }
            1 => {
                store.mk_app(Symbol::named("occupied"), [], Sort::Bool);
            }
            2 => {
                store.mk_let(vec![("occupied".into(), truth)], truth);
            }
            3 => {
                store.mk_forall(vec![("occupied".into(), Sort::Int)], truth);
            }
            4 => {
                store.mk_exists(vec![("occupied".into(), Sort::Int)], truth);
            }
            _ => store.mark_skolem_symbol("occupied"),
        }
        let old = store.len();
        let serial = store.var_counter();
        assert_eq!(
            store.try_fresh_owned_named_var_with_progress("occupied", &Sort::Int, &mut |_, _| true),
            Err(ControlledTermInternError::InvalidInput),
        );
        assert_eq!(store.len(), old);
        assert_eq!(store.var_counter(), serial);
    }
}

#[test]
fn owned_var_dynamic_name_and_nested_sort_refuse_before_first_copy() {
    let mut store = TermStore::new();
    let name = "physical".repeat(10_000);
    let old = store.len();
    let mut max_work = 0usize;
    assert_eq!(
        store.try_fresh_var_with_progress(&name, &Sort::Int, &mut |work, bytes| {
            max_work = max_work.max(work);
            let _ = bytes;
            work < 1024
        }),
        Err(ControlledTermInternError::ResourceLimit),
    );
    assert_eq!(store.len(), old);
    assert_eq!(store.var_counter(), 0);
    assert!(
        max_work >= 1024,
        "the original work-only refusal still fires"
    );
    let mut storage = 0usize;
    assert_eq!(
        store.try_fresh_var_with_progress(&name, &Sort::Int, &mut |_, bytes| {
            storage = storage.saturating_add(bytes);
            storage < 1024
        }),
        Err(ControlledTermInternError::ResourceLimit),
    );
    assert!(
        storage >= 1024,
        "separate storage-only admission reaches the pre-copy fence"
    );
    assert_eq!(store.len(), old);
    assert_eq!(store.var_counter(), 0);
    let mut deep = Sort::Int;
    for _ in 0..130 {
        deep = Sort::seq(deep);
    }
    assert_eq!(
        store.try_fresh_var_with_progress("deep", &deep, &mut |_, _| true),
        Err(ControlledTermInternError::ResourceLimit),
    );
    assert_eq!(store.len(), old);
}

#[test]
fn owned_var_readonly_nonwrap_terminal_stop_and_public_var_refusal() {
    let mut store = TermStore::new();
    let mut snapshot = TermStore::from_entries(store.entries_snapshot(), None, None, 0);
    assert_eq!(
        snapshot.try_fresh_var_with_progress("snapshot", &Sort::Int, &mut |_, _| true),
        Err(ControlledTermInternError::ReadOnlySnapshot),
    );
    store.var_counter = u32::MAX;
    assert_eq!(
        store.try_fresh_var_with_progress("last", &Sort::Int, &mut |_, _| true),
        Err(ControlledTermInternError::ResourceLimit),
    );
    let mut baseline = TermStore::new();
    let mut calls = 0usize;
    baseline
        .try_fresh_var_with_progress("late", &Sort::Int, &mut |_, _| {
            calls += 1;
            true
        })
        .unwrap();
    let mut fresh = TermStore::new();
    let mut visited = 0;
    assert_eq!(
        fresh.try_fresh_var_with_progress("late", &Sort::Int, &mut |_, _| {
            visited += 1;
            visited < calls
        }),
        Err(ControlledTermInternError::ResourceLimit),
    );
    assert_eq!(visited, calls);
    assert_eq!(
        fresh.var_counter(),
        1,
        "late refusal never rewinds freshness"
    );
    let raw = TermData::Var("public_raw".into(), 999);
    assert_eq!(
        fresh.try_intern_with_progress(&raw, &Sort::Bool, &mut |_, _| true),
        Err(ControlledTermInternError::UnsupportedFragment)
    );
}

#[test]
fn owned_var_retained_wide_names_are_priced_before_new_copies() {
    let mut store = TermStore::new();
    let wide = "retained".repeat(10_000);
    store.mk_app(Symbol::named(wide.clone()), [], Sort::Bool);
    let old = store.len();
    let mut copied = 0usize;
    assert_eq!(
        store.try_fresh_var_with_progress("next", &Sort::Int, &mut |work, bytes| {
            copied += bytes;
            work < wide.len()
        }),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(
        copied, 0,
        "raw name scanning precedes every new owning copy"
    );
    assert_eq!(store.len(), old);
}

#[test]
fn owned_var_names_above_fixed_heap_margin_have_dynamic_credit() {
    let mut store = TermStore::new();
    let prefix = "long_owned".repeat(600);
    assert!(prefix.len() > 4096);
    let first = store
        .try_fresh_var_with_progress(&prefix, &Sort::Int, &mut |_, _| true)
        .unwrap();
    let name = match store.get(first) {
        TermData::Var(name, _) => name,
        _ => panic!("Var"),
    };
    assert!(name.len() > 4096);
    assert_eq!(store.find_var(name), Some(first));
    assert_eq!(store.sort(first), &Sort::Int);
    let exact_name = "exact_owned".repeat(600);
    let exact = store
        .try_fresh_owned_named_var_with_progress(&exact_name, &Sort::Bool, &mut |_, _| true)
        .unwrap();
    assert!(matches!(store.get(exact), TermData::Var(name, _) if name == &exact_name));
    assert_eq!(store.find_var(&exact_name), Some(exact));
}

#[test]
fn owned_var_real_registry_growth_refuses_before_rehash_and_keeps_original_rows() {
    use crate::kani_compat::hash_table_cost as table;
    for storage_only in [false, true] {
        let mut store = TermStore::new();
        for name in ["initial_a", "initial_b", "initial_c"] {
            store.mk_var(name, Sort::Int);
        }
        assert_eq!(store.names.len(), store.names.capacity());
        let allocation = store.names.allocation_size();
        let cost = table::reserve_one::<(String, (TermId, Sort))>(
            allocation,
            store.names.len(),
            store.names.capacity(),
        )
        .unwrap();
        let old_len = store.len();
        let serial = store.var_counter();
        let mut reached = false;
        assert_eq!(
            store.try_fresh_owned_named_var_with_progress(
                "not_published",
                &Sort::Int,
                &mut |work, bytes| {
                    if work == cost.work && bytes == cost.storage_bytes {
                        reached = true;
                        return if storage_only {
                            bytes < cost.storage_bytes
                        } else {
                            work < cost.work
                        };
                    }
                    true
                }
            ),
            Err(ControlledTermInternError::ResourceLimit)
        );
        assert!(reached, "refusal at the actual registry reserve admission");
        assert_eq!(store.names.allocation_size(), allocation);
        assert_eq!(store.names.len(), 3);
        assert_eq!(store.len(), old_len);
        assert_eq!(store.var_counter(), serial);
        assert!(store.find_var("not_published").is_none());
        for name in ["initial_a", "initial_b", "initial_c"] {
            assert!(store.find_var(name).is_some());
        }
    }
}
