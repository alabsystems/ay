// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::mem::size_of_val;

fn entries() -> Vec<(TermData, Sort)> {
    vec![
        (TermData::Const(Constant::Bool(true)), Sort::Bool),
        (TermData::Not(TermId(u32::MAX)), Sort::Bool),
        (
            TermData::Var("unused-owned-name".repeat(64), 7),
            Sort::Seq(Box::new(Sort::Uninterpreted(
                "nested-owned-sort".repeat(64),
            ))),
        ),
    ]
}

#[test]
fn raw_clone_preserves_positions_malformed_ids_and_exact_resource_charges() {
    let source = entries();
    let (mut work, mut bytes, mut polls) = (0, 0, 0);
    let copied = TermStore::copy_snapshot_entries_with_progress(&source, &mut |w, b| {
        work += w;
        bytes += b;
        polls += 1;
        true
    })
    .unwrap();
    assert_eq!(copied, source);
    assert!(work > source.len() && bytes > size_of_val(source.as_slice()));
    let store = TermStore::from_entries(source.clone(), None, None, 9);
    let (mut store_work, mut store_bytes, mut store_polls) = (0, 0, 0);
    assert_eq!(
        store
            .entries_snapshot_with_progress(&mut |w, b| {
                store_work += w;
                store_bytes += b;
                store_polls += 1;
                true
            })
            .unwrap(),
        source
    );
    assert_eq!((work, bytes, polls), (store_work, store_bytes, store_polls));
    for (work_cap, bytes_cap, admitted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let result = TermStore::copy_snapshot_entries_with_progress(&source, &mut |dw, db| {
            w += dw;
            b += db;
            w <= work_cap && b <= bytes_cap
        });
        assert_eq!(result.is_ok(), admitted);
    }
}

#[test]
fn raw_clone_refuses_every_checkpoint_and_does_not_reset_the_caller() {
    let source = entries();
    let (mut polls, mut total_bytes) = (0, 0);
    TermStore::copy_snapshot_entries_with_progress(&source, &mut |_, bytes| {
        polls += 1;
        total_bytes += bytes;
        true
    })
    .unwrap();
    for refused in 1..=polls {
        let mut calls = 0;
        let result = TermStore::copy_snapshot_entries_with_progress(&source, &mut |_, _| {
            calls += 1;
            calls != refused
        });
        assert_eq!(result, Err(TermSnapshotError::ResourceLimit));
        assert_eq!(calls, refused);
    }
    let mut bytes = 0;
    let mut progress = |_: usize, delta: usize| {
        bytes += delta;
        bytes <= total_bytes
    };
    assert!(TermStore::copy_snapshot_entries_with_progress(&source, &mut progress).is_ok());
    assert_eq!(
        TermStore::copy_snapshot_entries_with_progress(&source, &mut progress),
        Err(TermSnapshotError::ResourceLimit)
    );
    assert_eq!(source, entries());
    assert_eq!(
        TermStore::copy_snapshot_entries_with_progress(&source, &mut |_, _| true).unwrap(),
        source
    );
}
