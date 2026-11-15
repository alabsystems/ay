// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn store() -> TermStore {
    TermStore::from_entries(
        vec![
            (TermData::Const(Constant::Bool(true)), Sort::Bool),
            (TermData::Const(Constant::Bool(false)), Sort::Bool),
            (TermData::Var("witness".to_string(), 0), Sort::Int),
        ],
        Some(TermId(0)),
        Some(TermId(1)),
        1,
    )
}

fn names() -> Vec<String> {
    vec![
        "witness".to_string(),
        "ghost".to_string(),
        "witness".to_string(),
    ]
}

fn usage() -> (usize, usize, usize) {
    let (mut work, mut bytes, mut polls) = (0usize, 0usize, 0usize);
    store()
        .with_skolem_symbols_with_progress(names(), &mut |w, b| {
            work = work.checked_add(w).expect("small fixture work");
            bytes = bytes.checked_add(b).expect("small fixture bytes");
            polls += 1;
            true
        })
        .expect("restore independently authenticated names");
    (work, bytes, polls)
}

#[test]
fn metered_skolem_restoration_matches_legacy_metadata_and_preserves_snapshot() {
    let mut legacy = store();
    let before_entries = legacy.entries_snapshot();
    for name in names() {
        legacy.mark_skolem_symbol(name);
    }
    let source = store();
    let before_stamp = source.snapshot_stamp();
    let restored = source
        .with_skolem_symbols_with_progress(names(), &mut |_, _| true)
        .expect("restored registry");
    assert_eq!(restored.entries_snapshot(), before_entries);
    assert_eq!(restored.snapshot_stamp(), before_stamp);
    assert_eq!(restored.checker_visible_metadata_generation(), 2);
    assert_eq!(
        restored.checker_visible_metadata_generation(),
        legacy.checker_visible_metadata_generation()
    );
    assert_eq!(
        restored.boolean_constant_ids(),
        legacy.boolean_constant_ids()
    );
    assert_eq!(restored.var_counter(), legacy.var_counter());
    assert_eq!(restored.skolem_symbols, legacy.skolem_symbols);
    assert!(restored.is_skolem_symbol("witness"));
    assert!(restored.is_skolem_symbol("ghost"));
    assert!(!restored.is_skolem_symbol("sk!unregistered"));
    assert!(restored.skolem_choice.is_empty());
    assert!(restored.hash_cons.is_empty());
    assert!(restored.names.is_empty());
    assert_eq!(restored.instance_term_bytes(), 0);
}

#[test]
fn metered_skolem_restoration_preserves_existing_choice_and_shadow_records() {
    let mut source = store();
    source.mark_skolem_symbol("existing".to_string());
    let choice = crate::SkolemChoice {
        binder: "x".to_string(),
        sort: Sort::Int,
        body: TermId(0),
    };
    source.register_skolem_choice(TermId(2), choice.clone());
    source.mark_to_real_shadowed();
    source.mark_is_int_shadowed();
    let generation = source.checker_visible_metadata_generation();
    let restored = source
        .with_skolem_symbols_with_progress(
            vec!["existing".to_string(), "new".to_string()],
            &mut |_, _| true,
        )
        .unwrap();
    assert!(restored.is_skolem_symbol("existing"));
    assert!(restored.is_skolem_symbol("new"));
    assert_eq!(restored.skolem_choice(TermId(2)), Some(&choice));
    assert!(restored.to_real_shadowed);
    assert!(restored.is_int_shadowed);
    assert_eq!(
        restored.checker_visible_metadata_generation(),
        generation + 1
    );
}

#[test]
fn metered_skolem_restoration_refuses_at_every_callback_including_final_return() {
    let (_, _, polls) = usage();
    for stop in 1..=polls {
        let mut calls = 0;
        let result = store().with_skolem_symbols_with_progress(names(), &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert!(matches!(result, Err(TermSnapshotError::ResourceLimit)));
        assert_eq!(calls, stop, "no callback or returned store after refusal");
    }
}

#[test]
fn metered_skolem_restoration_shares_exact_work_and_allocation_envelopes() {
    let (work, bytes, _) = usage();
    for (work_limit, byte_limit, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut used_work, mut used_bytes) = (0usize, 0usize);
        let mut progress = |w, b| {
            used_work = used_work.checked_add(w).unwrap();
            used_bytes = used_bytes.checked_add(b).unwrap();
            used_work <= work_limit && used_bytes <= byte_limit
        };
        let result = store().with_skolem_symbols_with_progress(names(), &mut progress);
        assert_eq!(result.is_ok(), accepted);
        if accepted {
            assert!(matches!(
                store().with_skolem_symbols_with_progress(names(), &mut progress),
                Err(TermSnapshotError::ResourceLimit)
            ));
        }
    }
}

#[test]
fn metered_skolem_restoration_moves_string_allocations_and_empty_input_still_polls() {
    let name = "owned".repeat(4_096);
    let original_ptr = name.as_ptr();
    let original_capacity = name.capacity();
    let restored = store()
        .with_skolem_symbols_with_progress(vec![name], &mut |_, _| true)
        .unwrap();
    let registered = restored.skolem_symbols.iter().next().unwrap();
    assert_eq!(registered.as_ptr(), original_ptr);
    assert_eq!(registered.capacity(), original_capacity);
    let mut calls = 0;
    let result = store().with_skolem_symbols_with_progress(Vec::new(), &mut |_, _| {
        calls += 1;
        calls < 3
    });
    assert!(matches!(result, Err(TermSnapshotError::ResourceLimit)));
    assert_eq!(
        calls, 3,
        "empty restoration retains the final cancellation poll"
    );
}

#[test]
fn metered_skolem_restoration_refuses_generation_overflow_but_not_duplicates() {
    let mut source = store();
    source.mark_skolem_symbol("existing".to_string());
    source.checker_visible_metadata_generation = u64::MAX;
    let source = source
        .with_skolem_symbols_with_progress(vec!["existing".to_string()], &mut |_, bytes| bytes == 0)
        .expect("an unchanged registry needs neither generation nor allocation");
    assert_eq!(source.checker_visible_metadata_generation(), u64::MAX);
    let mut allocation_attempts = 0;
    assert!(matches!(
        source.with_skolem_symbols_with_progress(vec!["new".to_string()], &mut |_, bytes| {
            allocation_attempts += usize::from(bytes != 0);
            true
        }),
        Err(TermSnapshotError::ResourceLimit)
    ));
    assert_eq!(
        allocation_attempts, 0,
        "generation checked before any new allocation"
    );
}

#[test]
fn metered_skolem_restoration_uses_private_capacity_without_charging_nonexistent_growth() {
    let mut source = store();
    source.skolem_symbols.reserve(256);
    let allocation = source.skolem_symbols.allocation_size();
    let capacity = source.skolem_symbols.capacity();
    let restored = source
        .with_skolem_symbols_with_progress(names(), &mut |_, bytes| bytes == 0)
        .expect("the actual private table already has room");
    assert_eq!(restored.skolem_symbols.capacity(), capacity);
    assert_eq!(restored.skolem_symbols.allocation_size(), allocation);
    assert_eq!(restored.len(), 3);
    assert_eq!(restored.skolem_symbols.len(), 2);
}

#[test]
fn metered_skolem_restoration_prices_ghost_registry_rehash_and_old_long_names() {
    let mut source = store();
    source.skolem_symbols.reserve(8);
    source.mark_skolem_symbol("long".repeat(4_096));
    let mut next = 0;
    while source.skolem_symbols.len() < source.skolem_symbols.capacity() {
        source.mark_skolem_symbol(format!("ghost-{next}"));
        next += 1;
    }
    assert!(source.skolem_symbols.len() > source.len());
    let mut saw_old_name = false;
    let result = source.with_skolem_symbols_with_progress(vec!["n".to_string()], &mut |work, _| {
        saw_old_name |= work >= 16_384;
        work < 16_384
    });
    assert!(matches!(result, Err(TermSnapshotError::ResourceLimit)));
    assert!(saw_old_name);
}

#[test]
fn metered_skolem_growth_bound_covers_actual_locked_hashbrown_allocations() {
    let mut source = store();
    for index in 0..1_024 {
        if source.skolem_symbols.len() == source.skolem_symbols.capacity() {
            let old = source.skolem_symbols.allocation_size();
            let (bytes, _) = native_growth_bounds(old).unwrap();
            source.skolem_symbols.try_reserve(1).unwrap();
            assert!(source.skolem_symbols.allocation_size() <= bytes);
        }
        source.mark_skolem_symbol(format!("ghost-{index}"));
    }
    assert!(matches!(
        native_growth_bounds(usize::MAX),
        Err(TermSnapshotError::ResourceLimit)
    ));
}
