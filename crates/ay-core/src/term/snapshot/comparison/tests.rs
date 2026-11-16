// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::RationalWrapper;
use num_rational::BigRational;

fn fixture() -> (TermStore, Vec<(TermData, Sort)>) {
    let entries = vec![
        (TermData::Not(TermId::SENTINEL), Sort::Bool),
        (
            TermData::Var("unused".repeat(4096), 7),
            Sort::array(
                Sort::Bool,
                Sort::Seq(Box::new(Sort::Uninterpreted("S".repeat(64)))),
            ),
        ),
    ];
    (
        TermStore::from_entries(entries.clone(), None, None, 0),
        entries,
    )
}

fn trace(terms: &TermStore, entries: &[(TermData, Sort)]) -> Vec<(usize, usize)> {
    let mut charges = Vec::new();
    assert!(terms
        .snapshot_entries_match_with_progress(entries, &mut |w, b| {
            charges.push((w, b));
            true
        })
        .unwrap());
    charges
}

#[test]
fn borrowed_comparison_preserves_malformed_unused_and_nested_raw_identity() {
    let (terms, entries) = fixture();
    assert_eq!(terms.entries_snapshot(), entries);
    assert_ne!(trace(&terms, &entries), Vec::new());
    for index in 0..entries.len() {
        for change_sort in [false, true] {
            let mut changed = entries.clone();
            if change_sort {
                changed[index].1 = Sort::Int;
            } else {
                changed[index].0 = TermData::Var("different".into(), 0);
            }
            assert!(!terms
                .snapshot_entries_match_with_progress(&changed, &mut |_, _| true)
                .unwrap());
        }
    }
    assert!(!terms
        .snapshot_entries_match_with_progress(&entries[..1], &mut |_, _| true)
        .unwrap());
    let empty = TermStore::from_entries(vec![], None, None, 0);
    assert!(empty
        .snapshot_entries_match_with_progress(&[], &mut |_, _| true)
        .unwrap());
}

#[test]
fn both_owned_payloads_are_work_priced_and_every_checkpoint_can_refuse() {
    let (terms, entries) = fixture();
    let charges = trace(&terms, &entries);
    assert!(charges.iter().all(|(_, bytes)| *bytes == 0));
    let work: usize = charges.iter().map(|(w, _)| *w).sum();
    assert!(work > 2 * "unused".len() * 4096);
    for cap in [work, work - 1] {
        let mut spent = 0;
        let result = terms.snapshot_entries_match_with_progress(&entries, &mut |w, _| {
            spent += w;
            spent <= cap
        });
        assert_eq!(result.is_ok(), cap == work);
    }
    for stop in 1..=charges.len() {
        let mut calls = 0;
        assert_eq!(
            terms.snapshot_entries_match_with_progress(&entries, &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(TermSnapshotError::ResourceLimit)
        );
        assert_eq!(calls, stop);
    }
}

#[test]
fn overdeep_right_operand_refuses_before_structural_equality() {
    let (terms, mut entries) = fixture();
    let mut deep = Sort::Bool;
    for _ in 0..258 {
        deep = Sort::Seq(Box::new(deep));
    }
    entries[0].1 = deep;
    assert_eq!(
        terms.snapshot_entries_match_with_progress(&entries, &mut |_, _| true),
        Err(TermSnapshotError::ResourceLimit)
    );
    let (fresh, original) = fixture();
    assert_ne!(trace(&fresh, &original), Vec::new());
}

#[test]
fn rational_snapshot_identity_is_raw_even_for_equivalent_or_malformed_encodings() {
    for (left, right, matches) in [
        ((1, 2), (1, 2), true),
        ((1, 2), (2, 4), false),
        ((1, -2), (-1, 2), false),
        ((1, 0), (1, 0), true),
        ((1, 0), (2, 3), false),
        ((2, 3), (1, 0), false),
    ] {
        let entry = |(numerator, denominator): (i64, i64)| {
            (
                TermData::Const(Constant::Rational(RationalWrapper(BigRational::new_raw(
                    numerator.into(),
                    denominator.into(),
                )))),
                Sort::Real,
            )
        };
        let terms = TermStore::from_entries(vec![entry(left)], None, None, 0);
        assert_eq!(
            terms
                .snapshot_entries_match_with_progress(&[entry(right)], &mut |_, b| {
                    assert_eq!(b, 0);
                    true
                })
                .unwrap(),
            matches
        );
    }
}
