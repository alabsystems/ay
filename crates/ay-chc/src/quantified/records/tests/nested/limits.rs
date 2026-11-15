// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;

fn chain(records: usize) -> ChcSort {
    let mut sort = ChcSort::Bool;
    for index in 0..records {
        sort = record(
            &format!("R{index}"),
            &format!("mk{index}"),
            vec![("next", sort)],
        );
    }
    sort
}

#[test]
fn record_depth_and_flattened_occurrences_have_independent_caps() {
    assert!(sort_bytes(&chain(MAX_RECORD_DEPTH)).is_some());
    assert!(sort_bytes(&chain(MAX_RECORD_DEPTH + 1)).is_none());
    let mut tree = record("Leaf", "leaf", vec![("value", ChcSort::Bool)]);
    for depth in 0..8 {
        tree = record(
            &format!("T{depth}"),
            &format!("mk{depth}"),
            vec![("a", tree.clone()), ("b", tree)],
        );
    }
    assert!(sort_bytes(&tree).is_some());
    let above = record("Above", "above", vec![("a", tree.clone()), ("b", tree)]);
    assert!(sort_bytes(&above).is_none());
}

#[test]
fn repeated_arc_occurrences_charge_names_and_copies_not_unique_metadata() {
    let long = record(
        "Payload",
        "mk_payload",
        vec![(&"f".repeat(12_000), ChcSort::Bool)],
    );
    assert!(sort_bytes(&long).is_some());
    let one = record("One", "one", vec![("a", long.clone())]);
    let two = record("Two", "two", vec![("a", long.clone()), ("b", long.clone())]);
    assert!(sort_bytes(&two).unwrap() > 2 * sort_bytes(&long).unwrap());
    assert!(sort_bytes(&two).unwrap() > sort_bytes(&one).unwrap());
    let shared = record(
        "Many",
        "many",
        (0..64).map(|_| ("field", long.clone())).collect(),
    );
    // The sort census does not confer duplicate-field authority, but it must
    // charge all occurrences even though every child shares the same Arc.
    let repeated = record(
        "Twice",
        "twice",
        vec![("left", shared.clone()), ("right", shared)],
    );
    assert!(sort_bytes(&repeated).is_none());
}

#[test]
fn complete_registry_aggregate_work_is_not_reset_for_each_definition() {
    let large = chain(50);
    let mut problem = ChcProblem::new();
    // Each individual record is bounded; the repeated complete declarations
    // exceed the single registry occurrence/copy ledger before any clone.
    for index in 0..MAX_RECORDS {
        let outer = record(
            &format!("Outer{index}"),
            &format!("mk_outer{index}"),
            vec![("a", large.clone()), ("b", large.clone())],
        );
        assert!(sort_bytes(&outer).is_some());
        add(&mut problem, &outer);
    }
    assert!(registry_bytes(&problem).is_none());
}
