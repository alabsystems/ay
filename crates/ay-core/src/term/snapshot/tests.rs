// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{DatatypeSort, RationalWrapper};
use num_bigint::BigInt;
use num_rational::BigRational;

fn base_entries() -> Vec<(TermData, Sort)> {
    vec![
        (TermData::Const(Constant::Bool(true)), Sort::Bool),
        (TermData::Const(Constant::Bool(false)), Sort::Bool),
        (TermData::Var("x".to_string(), 7), Sort::Real),
        (TermData::Not(TermId(0)), Sort::Bool),
    ]
}

fn source_store(entries: Vec<(TermData, Sort)>) -> TermStore {
    TermStore::from_entries(entries, Some(TermId(0)), Some(TermId(1)), 73)
}

fn copy_entries(entries: &[(TermData, Sort)], progress: Progress<'_>) -> SnapshotResult<TermStore> {
    TermStore::from_entries_with_progress(entries, Some(TermId(0)), Some(TermId(1)), 73, progress)
}

fn assert_refused<T>(result: SnapshotResult<T>) {
    assert!(matches!(result, Err(TermSnapshotError::ResourceLimit)));
}

#[test]
fn both_snapshot_directions_refuse_on_the_first_callback() {
    let entries = base_entries();
    let store = source_store(entries.clone());
    let mut calls = 0;
    let mut refuse = |_: usize, _: usize| {
        calls += 1;
        false
    };
    assert_refused(store.entries_snapshot_with_progress(&mut refuse));
    assert_eq!(calls, 1);
    calls = 0;
    assert_refused(copy_entries(&entries, &mut |_, _| {
        calls += 1;
        false
    }));
    assert_eq!(calls, 1);
    assert_eq!(store.entries_snapshot(), entries);
}

#[test]
fn snapshot_roundtrip_preserves_exact_positions_and_checker_only_state() {
    let mut source = TermStore::new();
    let x = source.mk_var("registered_x", Sort::Int);
    source.mark_skolem_symbol("registered_x".to_string());
    let expected = source.entries_snapshot();
    let snapshot = source
        .entries_snapshot_with_progress(&mut |_, _| true)
        .expect("metered snapshot");
    assert_eq!(snapshot, expected);
    let reconstructed = TermStore::from_entries_with_progress(
        &snapshot,
        Some(source.true_term()),
        Some(source.false_term()),
        source.var_counter(),
        &mut |_, _| true,
    )
    .expect("metered reconstruction");
    assert_eq!(reconstructed.entries_snapshot(), expected);
    assert_eq!(reconstructed.get(x), source.get(x));
    assert_eq!(reconstructed.sort(x), source.sort(x));
    assert_eq!(reconstructed.var_counter(), source.var_counter());
    assert_eq!(reconstructed.true_term(), source.true_term());
    assert_eq!(reconstructed.false_term(), source.false_term());
    assert_eq!(reconstructed.instance_term_bytes(), 0);
    assert!(reconstructed.hash_cons.is_empty());
    assert!(reconstructed.names.is_empty());
    assert!(reconstructed.skolem_symbols.is_empty());
    assert_ne!(reconstructed.entry_stamp(x), source.entry_stamp(x));
}

#[test]
fn boolean_metadata_options_are_preserved_without_authentication() {
    let entries = base_entries();
    for (true_id, false_id) in [
        (None, None),
        (Some(TermId(0)), None),
        (None, Some(TermId(1))),
        (Some(TermId(u32::MAX)), Some(TermId(2))),
    ] {
        let source = TermStore::from_entries(entries.clone(), true_id, false_id, 9);
        assert_eq!(source.boolean_constant_ids(), (true_id, false_id));
        let restored =
            TermStore::from_entries_with_progress(&entries, true_id, false_id, 9, &mut |_, _| true)
                .expect("copy preserves even untrusted metadata");
        assert_eq!(
            restored.boolean_constant_ids(),
            source.boolean_constant_ids()
        );
        assert_eq!(restored.var_counter(), 9);
    }
}

#[test]
fn zero_work_or_byte_allowance_refuses_before_copying() {
    let entries = base_entries();
    let store = source_store(entries.clone());
    assert_refused(store.entries_snapshot_with_progress(&mut |work, _| work == 0));
    assert_refused(store.entries_snapshot_with_progress(&mut |_, bytes| bytes == 0));
    assert_refused(copy_entries(&entries, &mut |work, _| work == 0));
    assert_refused(copy_entries(&entries, &mut |_, bytes| bytes == 0));
}

#[test]
fn mid_copy_refusal_is_immediate_and_does_not_mutate_the_source() {
    let entries = base_entries();
    let store = source_store(entries.clone());
    let mut calls = 0;
    assert_refused(store.entries_snapshot_with_progress(&mut |_, _| {
        calls += 1;
        calls < 7
    }));
    assert_eq!(calls, 7);
    calls = 0;
    assert_refused(copy_entries(&entries, &mut |_, _| {
        calls += 1;
        calls < 7
    }));
    assert_eq!(calls, 7);
    assert_eq!(store.entries_snapshot(), entries);
}

#[test]
fn final_poll_can_withdraw_an_otherwise_complete_copy() {
    let entries = base_entries();
    let store = source_store(entries.clone());
    let mut snapshot_trace = Vec::new();
    store
        .entries_snapshot_with_progress(&mut |work, bytes| {
            snapshot_trace.push((work, bytes));
            true
        })
        .expect("snapshot control");
    assert_eq!(snapshot_trace.last(), Some(&(0, 0)));
    let mut calls = 0;
    assert_refused(store.entries_snapshot_with_progress(&mut |_, _| {
        calls += 1;
        calls < snapshot_trace.len()
    }));
    assert_eq!(calls, snapshot_trace.len());

    let mut reconstruction_trace = Vec::new();
    copy_entries(&entries, &mut |work, bytes| {
        reconstruction_trace.push((work, bytes));
        true
    })
    .expect("reconstruction control");
    assert_eq!(reconstruction_trace.last(), Some(&(0, 0)));
    calls = 0;
    assert_refused(copy_entries(&entries, &mut |_, _| {
        calls += 1;
        calls < reconstruction_trace.len()
    }));
    assert_eq!(calls, reconstruction_trace.len());
}

#[test]
fn unused_large_payload_is_charged_even_with_zero_source_ledgers() {
    let mut entries = base_entries();
    entries.push((
        TermData::Const(Constant::String("u".repeat(32_768))),
        Sort::String,
    ));
    let store = source_store(entries);
    assert_eq!(store.instance_term_bytes(), 0);
    assert_eq!(store.heap_data_bytes, 0);
    let mut observed_large_payload = false;
    assert_refused(store.entries_snapshot_with_progress(&mut |_, bytes| {
        observed_large_payload |= bytes >= 32_768;
        bytes < 32_768
    }));
    assert!(observed_large_payload);
    let entries = store.entries_snapshot();
    observed_large_payload = false;
    assert_refused(copy_entries(&entries, &mut |_, bytes| {
        observed_large_payload |= bytes >= 32_768;
        bytes < 32_768
    }));
    assert!(observed_large_payload);
}

fn nested_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "D",
        vec![DatatypeConstructor::new(
            "C",
            vec![DatatypeField::new(
                "field",
                Sort::Array(Box::new(ArraySort::new(
                    Sort::Int,
                    Sort::Seq(Box::new(Sort::Uninterpreted("nested".repeat(2_048)))),
                ))),
            )],
        )],
    ))
}

#[test]
fn nested_binder_sort_payload_is_charged_before_cloning() {
    let mut entries = base_entries();
    entries.push((
        TermData::Forall(
            vec![("bound".to_string(), nested_sort())],
            TermId(0),
            vec![vec![TermId(2); 32], vec![TermId(0)]],
        ),
        Sort::Bool,
    ));
    let store = source_store(entries.clone());
    let mut saw_nested = false;
    assert_refused(store.entries_snapshot_with_progress(&mut |_, bytes| {
        saw_nested |= bytes >= 12_288;
        bytes < 12_288
    }));
    assert!(saw_nested);
    saw_nested = false;
    assert_refused(copy_entries(&entries, &mut |_, bytes| {
        saw_nested |= bytes >= 12_288;
        bytes < 12_288
    }));
    assert!(saw_nested);
    assert_eq!(
        copy_entries(&entries, &mut |_, _| true)
            .expect("nested binder control")
            .entries_snapshot(),
        entries
    );
}

#[test]
fn vector_payloads_and_numeric_limbs_are_all_accounted() {
    let big = BigInt::from(1) << 8_192usize;
    let entries = vec![
        (TermData::Const(Constant::Bool(true)), Sort::Bool),
        (TermData::Const(Constant::Int(big.clone())), Sort::Int),
        (
            TermData::Const(Constant::Rational(RationalWrapper(BigRational::new(
                big.clone(),
                BigInt::from(3),
            )))),
            Sort::Real,
        ),
        (
            TermData::App(
                Symbol::indexed("indexed", vec![0; 256]),
                vec![TermId(0); 512],
            ),
            Sort::Bool,
        ),
        (
            TermData::Let(vec![("let_name".repeat(256), TermId(0))], TermId(0)),
            Sort::Bool,
        ),
        (
            TermData::Exists(
                vec![("e".to_string(), Sort::Int)],
                TermId(0),
                vec![vec![TermId(0); 1024]],
            ),
            Sort::Bool,
        ),
    ];
    let mut work = 0usize;
    let mut bytes = 0usize;
    let copied = copy_entries(&entries, &mut |work_delta, byte_delta| {
        work = work.checked_add(work_delta).expect("small fixture work");
        bytes = bytes.checked_add(byte_delta).expect("small fixture bytes");
        true
    })
    .expect("all payload variants copy without interpretation");
    assert_eq!(copied.entries_snapshot(), entries);
    assert!(work > 2_000);
    assert!(bytes > 10_000);
    let mut charged_bigint = 0;
    meter_bigint(&big, &mut |_, bytes| {
        charged_bigint = bytes;
        true
    })
    .expect("limb accounting");
    assert_eq!(charged_bigint, 129 * size_of::<u64>());
}

#[test]
fn overdeep_sorts_are_rejected_before_clone_in_both_locations() {
    let mut deep = Sort::Bool;
    for _ in 0..=MAX_SNAPSHOT_SORT_DEPTH {
        deep = Sort::Seq(Box::new(deep));
    }
    let entries = vec![(TermData::Var("deep".to_string(), 0), deep)];
    assert_refused(copy_entries(&entries, &mut |_, _| true));
    let store = source_store(entries);
    assert_refused(store.entries_snapshot_with_progress(&mut |_, _| true));

    let mut deep_binder = Sort::Bool;
    for _ in 0..=MAX_SNAPSHOT_SORT_DEPTH {
        deep_binder = Sort::Seq(Box::new(deep_binder));
    }
    let entries = vec![(
        TermData::Forall(vec![("q".to_string(), deep_binder)], TermId(0), vec![]),
        Sort::Bool,
    )];
    assert_refused(copy_entries(&entries, &mut |_, _| true));
}

#[test]
fn maximum_admitted_sort_depth_roundtrips_without_normalizing_payloads() {
    let mut nested = Sort::Bool;
    for _ in 0..MAX_SNAPSHOT_SORT_DEPTH {
        nested = Sort::Seq(Box::new(nested));
    }
    let entries = vec![
        (TermData::Var("at_limit".to_string(), 19), nested),
        (
            TermData::Const(Constant::Rational(RationalWrapper(BigRational::new_raw(
                BigInt::from(6),
                BigInt::from(-8),
            )))),
            Sort::Real,
        ),
        (
            TermData::Const(Constant::BitVec {
                value: BigInt::from(-5),
                width: 0,
            }),
            Sort::BitVec(crate::BitVecSort::new(0)),
        ),
    ];
    let copied = copy_entries(&entries, &mut |_, _| true).expect("resource-safe raw copy");
    let snapshot = copied
        .entries_snapshot_with_progress(&mut |_, _| true)
        .expect("snapshot preserves raw payloads");
    let TermData::Const(Constant::Rational(raw)) = &snapshot[1].0 else {
        panic!("rational kind must be retained");
    };
    assert_eq!(raw.0.numer(), &BigInt::from(6));
    assert_eq!(raw.0.denom(), &BigInt::from(-8));
    let TermData::Const(Constant::BitVec { value, width }) = &snapshot[2].0 else {
        panic!("bit-vector kind must be retained");
    };
    assert_eq!(value, &BigInt::from(-5));
    assert_eq!(*width, 0);
    assert_eq!(snapshot[0], entries[0]);
}

#[test]
fn one_callback_budget_is_shared_across_snapshot_and_reconstruction() {
    let store = source_store(base_entries());
    let mut snapshot_bytes = 0usize;
    store
        .entries_snapshot_with_progress(&mut |_, bytes| {
            snapshot_bytes += bytes;
            true
        })
        .expect("measure small snapshot");
    let mut spent = 0usize;
    let mut progress = |_: usize, bytes: usize| {
        let Some(next) = spent.checked_add(bytes) else {
            return false;
        };
        if next > snapshot_bytes {
            return false;
        }
        spent = next;
        true
    };
    let entries = store
        .entries_snapshot_with_progress(&mut progress)
        .expect("snapshot fits exact allowance");
    assert_refused(copy_entries(&entries, &mut progress));
    assert_eq!(spent, snapshot_bytes);
}

#[test]
fn checked_accounting_and_output_shape_fail_closed() {
    assert_refused(checked_add(usize::MAX, 1));
    assert_refused(checked_mul(usize::MAX, 2));
    assert_refused(reserve_output::<TermEntry>(usize::MAX, &mut |_, _| true));
    assert_refused(meter_sort(&Sort::Bool, usize::MAX, &mut |_, _| true));
}
