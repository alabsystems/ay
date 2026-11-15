// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

#[test]
fn affected_rows_keep_the_current_and_next_sweep_order() {
    let db = vec![vec![(1, true)]; 4];
    let owner = EmissionProgress::default();
    let budget = &mut 100_000;
    let index = Occurrences::new(&db, budget, &owner).unwrap();
    let mut sweep = index.sweep(budget, &owner).unwrap();
    assert_eq!(sweep.next(budget, &owner), Some(Some(0)));
    sweep.assigned(&index, 1, budget, &owner).unwrap();
    assert_eq!(sweep.next(budget, &owner), Some(Some(1)));
    // Duplicate notification coalesces pending rows, not clauses or literals.
    sweep.assigned(&index, 1, budget, &owner).unwrap();
    for expected in [2, 3, 0, 1] {
        assert_eq!(sweep.next(budget, &owner), Some(Some(expected)));
    }
    assert_eq!(sweep.next(budget, &owner), Some(None));
}

#[test]
fn appended_empty_and_duplicate_rows_are_visited_after_restart() {
    let owner = EmissionProgress::default();
    let budget = &mut 100_000;
    let mut index = Occurrences::new(&[vec![(1, true)]], budget, &owner).unwrap();
    index.append(&vec![], budget, &owner).unwrap();
    index
        .append(&vec![(1, false), (1, true), (1, false)], budget, &owner)
        .unwrap();
    for _ in 0..2 {
        let mut sweep = index.sweep(budget, &owner).unwrap();
        for expected in [0, 1, 2] {
            assert_eq!(sweep.next(budget, &owner), Some(Some(expected)));
        }
        sweep.assigned(&index, 1, budget, &owner).unwrap();
        assert_eq!(sweep.next(budget, &owner), Some(Some(0)));
        assert_eq!(sweep.next(budget, &owner), Some(Some(2)));
        assert_eq!(sweep.next(budget, &owner), Some(None));
    }
}

#[test]
fn clause_occurrences_are_not_normalized_or_strengthened() {
    for db in [
        vec![vec![(1, true), (1, true)], vec![(1, false), (2, true)]],
        vec![vec![(1, false), (1, true)], vec![(2, false), (2, true)]],
        vec![vec![], vec![(1, true)]],
        vec![vec![(1, true)], vec![(1, false)], vec![]],
    ] {
        for code in 0..9 {
            compare_localsat(&db, &fixed(code));
        }
        compare_cdcl(&db, &[], &[]);
    }
}

#[test]
fn reverse_chain_conflict_retains_the_same_native_premise_cone() {
    let mut db = reverse_chain(128);
    // A negative endpoint unit would propagate backwards through this
    // reversed clause order in one sweep, giving no quadratic baseline.
    // This binary endpoint waits for the forward chain to reach its end.
    db.insert(0, vec![(128, false), (129, false)]);
    compare_cdcl(&db, &[], &[]);
    let owner = EmissionProgress::default();
    let (old, old_trace) = measured(|| legacy_cdcl::refute(&db, &[], &[], &mut 1_000_000, &owner));
    let (new, new_trace) = measured(|| cdcl::refute(&db, &[], &[], &mut 1_000_000, &owner));
    assert!(old.is_some() && new.is_some());
    assert!(new_trace.visits * 4 < old_trace.visits);
}
