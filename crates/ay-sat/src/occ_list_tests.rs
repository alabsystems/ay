// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::test_util::lit_signed as lit;

#[test]
fn add_and_get() {
    let mut occ = OccList::new(5);
    occ.add_clause(0, &[lit(1), lit(2), lit(3)]);
    occ.add_clause(1, &[lit(1), lit(-2)]);

    assert_eq!(occ.get(lit(1)), &[0, 1]);
    assert_eq!(occ.get(lit(2)), &[0]);
    assert_eq!(occ.get(lit(-2)), &[1]);
    assert_eq!(occ.get(lit(3)), &[0]);
    assert_eq!(occ.count(lit(1)), 2);
}

#[test]
fn remove_clause_removes_from_all_literals() {
    let mut occ = OccList::new(5);
    occ.add_clause(0, &[lit(1), lit(2)]);
    occ.add_clause(1, &[lit(1), lit(3)]);

    occ.remove_clause(0, &[lit(1), lit(2)]);
    assert_eq!(occ.get(lit(1)), &[1]);
    assert!(occ.get(lit(2)).is_empty());
    assert_eq!(occ.get(lit(3)), &[1]);
}

#[test]
fn remove_nonexistent_is_noop() {
    let mut occ = OccList::new(5);
    occ.add_clause(0, &[lit(1), lit(2)]);
    occ.remove_clause(99, &[lit(1), lit(2)]);
    assert_eq!(occ.get(lit(1)), &[0]);
}

#[test]
fn clear_empties_all() {
    let mut occ = OccList::new(5);
    occ.add_clause(0, &[lit(1), lit(2)]);
    occ.clear();
    assert!(occ.get(lit(1)).is_empty());
    assert!(occ.get(lit(2)).is_empty());
}

#[test]
fn ensure_num_vars_extends() {
    let mut occ = OccList::new(2);
    occ.add_clause(0, &[lit(1)]);
    occ.ensure_num_vars(10);
    assert_eq!(occ.get(lit(1)), &[0]);
    occ.add_clause(1, &[lit(8)]);
    assert_eq!(occ.get(lit(8)), &[1]);
}

#[test]
fn swap_to_front_moves_element() {
    let mut occ = OccList::new(5);
    occ.add_clause(10, &[lit(1)]);
    occ.add_clause(20, &[lit(1)]);
    occ.add_clause(30, &[lit(1)]);
    assert_eq!(occ.get(lit(1)), &[10, 20, 30]);

    occ.swap_to_front(lit(1), 2);
    assert_eq!(occ.get(lit(1)), &[30, 20, 10]);
}

#[test]
fn swap_to_front_noop_at_zero() {
    let mut occ = OccList::new(5);
    occ.add_clause(10, &[lit(1)]);
    occ.add_clause(20, &[lit(1)]);
    occ.swap_to_front(lit(1), 0);
    assert_eq!(occ.get(lit(1)), &[10, 20]);
}

#[test]
fn swap_to_front_out_of_bounds_noop() {
    let mut occ = OccList::new(5);
    occ.add_clause(10, &[lit(1)]);
    occ.swap_to_front(lit(1), 5);
    assert_eq!(occ.get(lit(1)), &[10]);
}

/// Verify that repeated add/remove cycles maintain position map consistency.
/// Exercises the swap_remove + position map update path (#3036).
#[test]
fn position_map_consistency_after_interleaved_ops() {
    let mut occ = OccList::new(5);
    // Add clauses 0..5 for literal 1
    for i in 0..5 {
        occ.add_clause(i, &[lit(1)]);
    }
    assert_eq!(occ.count(lit(1)), 5);

    // Remove middle element (clause 2)
    occ.remove_clause(2, &[lit(1)]);
    assert_eq!(occ.count(lit(1)), 4);
    assert!(!occ.get(lit(1)).contains(&2));

    // Remove first element (clause 0)
    occ.remove_clause(0, &[lit(1)]);
    assert_eq!(occ.count(lit(1)), 3);
    assert!(!occ.get(lit(1)).contains(&0));
    assert!(!occ.get(lit(1)).contains(&2));

    // Remaining should be {1, 3, 4} in some order
    let remaining: Vec<usize> = {
        let mut v = occ.get(lit(1)).to_vec();
        v.sort_unstable();
        v
    };
    assert_eq!(remaining, vec![1, 3, 4]);

    // Add a new clause and remove the last remaining ones
    occ.add_clause(10, &[lit(1)]);
    assert_eq!(occ.count(lit(1)), 4);
    occ.remove_clause(1, &[lit(1)]);
    occ.remove_clause(3, &[lit(1)]);
    occ.remove_clause(4, &[lit(1)]);
    assert_eq!(occ.get(lit(1)), &[10]);

    // Remove the only remaining element
    occ.remove_clause(10, &[lit(1)]);
    assert!(occ.get(lit(1)).is_empty());
}

/// Verify clone_from_other produces a correct deep copy with position maps.
#[test]
fn clone_from_other_preserves_remove_capability() {
    let mut src = OccList::new(5);
    src.add_clause(0, &[lit(1), lit(2)]);
    src.add_clause(1, &[lit(1), lit(3)]);
    src.add_clause(2, &[lit(1)]);

    let mut dst = OccList::new(5);
    dst.clone_from_other(&src);

    assert_eq!(dst.count(lit(1)), 3);
    // Remove from the clone should work (position map is rebuilt)
    dst.remove_clause(1, &[lit(1), lit(3)]);
    assert_eq!(dst.count(lit(1)), 2);
    assert!(dst.get(lit(3)).is_empty());
    // Source should be unaffected
    assert_eq!(src.count(lit(1)), 3);
}

/// An occ-only list (no pos_map) must produce byte-identical `get()`/`count()`
/// results to a full `OccList::new` build for the same clauses, and survive a
/// `clear()` + rebuild with the same results. This is the invariant that makes
/// the level-0 GC `gc_occ` reuse behavior-preserving.
#[test]
fn occ_only_matches_full_build() {
    let clauses: [(usize, &[Literal]); 4] = [
        (0, &[lit(1), lit(2), lit(3)]),
        (1, &[lit(1), lit(-2)]),
        (2, &[lit(-1), lit(3)]),
        (3, &[lit(2)]),
    ];

    let mut full = OccList::new(5);
    let mut lean = OccList::new_occ_only(5);
    for &(idx, lits) in &clauses {
        full.add_clause(idx, lits);
        lean.add_clause(idx, lits);
    }

    for v in 1..=3i32 {
        for &s in &[v, -v] {
            assert_eq!(full.get(lit(s)), lean.get(lit(s)), "get mismatch for {s}");
            assert_eq!(full.count(lit(s)), lean.count(lit(s)));
        }
    }

    // clear() retains capacity; a rebuild reproduces identical occ vectors.
    lean.clear();
    lean.ensure_num_vars(5);
    for &(idx, lits) in &clauses {
        lean.add_clause(idx, lits);
    }
    for v in 1..=3i32 {
        for &s in &[v, -v] {
            assert_eq!(
                full.get(lit(s)),
                lean.get(lit(s)),
                "rebuild mismatch for {s}"
            );
        }
    }
}
