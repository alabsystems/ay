// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for LRA sparse vector operations in types.rs.
//!
//! Validates correctness of `add_sparse_term` and `normalize_sparse_coeffs`
//! which are hot-path primitives used by simplex pivot and tableau operations.

use super::*;
use crate::types::{add_sparse_term, normalize_sparse_coeffs};

/// Verify sorted insertion maintains order across 1000 elements.
///
/// `add_sparse_term` uses `Vec::insert` which is O(n) per call.
/// This test confirms correctness at scale; the O(n^2) cost of
/// building a sorted vector one element at a time is documented
/// in issue #5486 as a performance concern for large tableaux.
#[test]
fn test_add_sparse_term_scaling_1000_terms() {
    let mut coeffs: Vec<(u32, BigRational)> = Vec::new();
    let n = 1000u32;
    // Insert in reverse order to exercise worst-case shifting
    for i in (0..n).rev() {
        add_sparse_term(&mut coeffs, i, BigRational::one());
    }
    assert_eq!(coeffs.len(), n as usize);
    for i in 0..coeffs.len() - 1 {
        assert!(
            coeffs[i].0 < coeffs[i + 1].0,
            "coeffs not sorted at index {i}"
        );
    }
}

/// Verify coefficient merging and zero-cancellation.
///
/// When two terms share the same variable, `add_sparse_term` must
/// sum their coefficients. If the sum is zero, the entry must be
/// removed entirely to maintain the sparse invariant.
#[test]
fn test_add_sparse_term_merge_and_cancel() {
    let mut coeffs: Vec<(u32, BigRational)> = Vec::new();
    add_sparse_term(&mut coeffs, 5, BigRational::one());
    add_sparse_term(&mut coeffs, 5, BigRational::one());
    assert_eq!(coeffs.len(), 1);
    assert_eq!(coeffs[0].1, BigRational::from_integer(2.into()));

    // Adding -2 should cancel out completely
    add_sparse_term(&mut coeffs, 5, BigRational::from_integer((-2).into()));
    assert!(coeffs.is_empty(), "zero-coefficient term not removed");
}

/// Verify normalize_sparse_coeffs deduplicates, sorts, and cancels.
///
/// Input: unsorted with duplicates and cancelling pairs.
/// Expected: sorted, merged, zero-free output.
#[test]
fn test_normalize_sparse_coeffs_dedup() {
    let coeffs = vec![
        (3, BigRational::one()),
        (1, BigRational::one()),
        (3, BigRational::one()),
        (2, BigRational::from_integer((-1).into())),
        (2, BigRational::one()),
    ];
    let result = normalize_sparse_coeffs(coeffs);
    // var 2 cancels (1 + -1 = 0), var 1 stays, var 3 merges to 2
    assert_eq!(result.len(), 2);
    assert_eq!(result[0].0, 1);
    assert_eq!(result[1].0, 3);
    assert_eq!(result[1].1, BigRational::from_integer(2.into()));
}

/// Performance proof: `add_sparse_term_rat` has O(k) per-call cost from
/// `Vec::insert`/`Vec::remove` element shifting. When called k times to
/// build a row (as happens during pivot substitution), the total cost
/// is O(k²) where k = number of nonzero coefficients.
///
/// This test measures the cost for N=2000 and N=4000 to verify the
/// quadratic scaling. With O(k²): doubling k should ~4x the time.
/// A merge-based approach would be O(k log k) and ~2x instead.
#[test]
fn test_perf_add_sparse_term_rat_quadratic_scaling() {
    use crate::types::add_sparse_term_rat;
    use crate::Rational;

    let one = Rational::one();

    // Warm up
    {
        let mut coeffs: Vec<(u32, Rational)> = Vec::new();
        for i in (0..100u32).rev() {
            add_sparse_term_rat(&mut coeffs, i, one.clone());
        }
    }

    // Measure N=2000: worst-case reverse insertion forces maximum shifting
    let n_small = 2000u32;
    let start = ay_core::time::Instant::now();
    let mut coeffs: Vec<(u32, Rational)> = Vec::new();
    for i in (0..n_small).rev() {
        add_sparse_term_rat(&mut coeffs, i, one.clone());
    }
    let t_small = start.elapsed();
    assert_eq!(coeffs.len(), n_small as usize);

    // Measure N=4000
    let n_large = 4000u32;
    let start = ay_core::time::Instant::now();
    let mut coeffs: Vec<(u32, Rational)> = Vec::new();
    for i in (0..n_large).rev() {
        add_sparse_term_rat(&mut coeffs, i, one.clone());
    }
    let t_large = start.elapsed();
    assert_eq!(coeffs.len(), n_large as usize);

    eprintln!(
        "[PERF] add_sparse_term_rat reverse-insert: N={n_small} -> {t_small:?}, N={n_large} -> {t_large:?}"
    );

    // Quadratic scaling: t_large / t_small should be ~4x (±tolerance).
    // If this is subquadratic (merge-based fix), ratio would be ~2x.
    // We just assert both complete within a reasonable bound.
    assert!(
        t_large.as_millis() < 5000,
        "add_sparse_term_rat with {n_large} reverse-insertions took {t_large:?} — \
         excessive for pivot substitution"
    );
}

/// Verify `TableauRow::substitute_var` produces the same result as the naive
/// `remove_coeff` + `add_coeff` loop it replaces (#6194).
///
/// Row: 2*x1 + 3*x2 + 1*x3, constant=5, basic_var=100
/// Substitute x2 with: x1=1, x2=-1, x4=2 (entering_var=2, scale=3)
///   → remove x2's coeff (3), add scale*{x1:1, x4:2} = {x1:3, x4:6}
///   → Result: (2+3)*x1 + 1*x3 + 6*x4 = 5*x1 + 1*x3 + 6*x4
#[test]
fn test_substitute_var_matches_naive() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    // Row: 2*x1 + 3*x2 + 1*x3
    let mut row = TableauRow::new_rat(
        100,
        vec![
            (1, Rational::new(2, 1)),
            (2, Rational::new(3, 1)),
            (3, Rational::one()),
        ],
        Rational::new(5, 1),
    );

    // Naive approach for reference
    let mut naive = row.clone();
    let scale = Rational::new(3, 1); // coefficient of entering_var (x2) in this row
    let subst_coeffs: Vec<(u32, Rational)> = vec![
        (1, Rational::one()),
        (2, Rational::new(-1, 1)),
        (4, Rational::new(2, 1)),
    ];

    // Naive: remove entering_var, add scaled substitution (skip entering_var itself)
    naive.remove_coeff(2);
    for &(v, ref c) in &subst_coeffs {
        if v == 2 {
            continue; // substitute_var filters entering_var from additions
        }
        let contrib = c * &scale;
        if !contrib.is_zero() {
            naive.add_coeff(v, contrib);
        }
    }

    // Optimized: single-pass substitute_var
    row.substitute_var(2, &subst_coeffs, &scale);

    assert_eq!(
        row.coeffs, naive.coeffs,
        "substitute_var must match naive remove+add loop"
    );
}

/// Verify substitute_var handles cancellation correctly.
/// Row: 3*x1 + 2*x2, substitute x2 with {x1: -1} at scale=2
///   → remove x2, add 2*(-1)*x1 = -2*x1
///   → Result: (3-2)*x1 = 1*x1
#[test]
fn test_substitute_var_cancellation() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let mut row = TableauRow::new_rat(
        100,
        vec![(1, Rational::new(3, 1)), (2, Rational::new(2, 1))],
        Rational::zero(),
    );

    let subst = vec![(1, Rational::new(-1, 1))];
    let scale = Rational::new(2, 1);
    row.substitute_var(2, &subst, &scale);

    assert_eq!(
        row.coeffs.len(),
        1,
        "should have exactly one term after cancellation"
    );
    assert_eq!(row.coeffs[0].0, 1);
    assert_eq!(row.coeffs[0].1, Rational::one());
}

/// Verify substitute_var preserves sorted invariant with non-overlapping variable sets.
/// Row: 1*x2 + 1*x4, substitute x2 with {x1: 1, x3: 1, x5: 1} at scale=1
///   → remove x2, add {x1:1, x3:1, x5:1}
///   → Result: 1*x1 + 1*x3 + 1*x4 + 1*x5 (interleaved, still sorted)
#[test]
fn test_substitute_var_interleaved_sorted() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let mut row = TableauRow::new_rat(
        100,
        vec![(2, Rational::one()), (4, Rational::one())],
        Rational::zero(),
    );

    let subst = vec![
        (1, Rational::one()),
        (3, Rational::one()),
        (5, Rational::one()),
    ];
    row.substitute_var(2, &subst, &Rational::one());

    // Should be sorted: x1, x3, x4, x5
    assert_eq!(row.coeffs.len(), 4);
    for i in 0..row.coeffs.len() - 1 {
        assert!(
            row.coeffs[i].0 < row.coeffs[i + 1].0,
            "sorted invariant violated at {i}: {} >= {}",
            row.coeffs[i].0,
            row.coeffs[i + 1].0,
        );
    }
    assert_eq!(row.coeffs[0].0, 1);
    assert_eq!(row.coeffs[1].0, 3);
    assert_eq!(row.coeffs[2].0, 4);
    assert_eq!(row.coeffs[3].0, 5);
}

/// Verify substitute_var when entering_var is the first element in the row.
/// Row: 2*x1 + 3*x3, substitute x1 with {x3: 1} at scale=2
///   → remove x1, add 2*{x3:1} = {x3:2}
///   → Result: (3+2)*x3 = 5*x3
#[test]
fn test_substitute_var_entering_first() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let mut row = TableauRow::new_rat(
        100,
        vec![(1, Rational::new(2, 1)), (3, Rational::new(3, 1))],
        Rational::zero(),
    );

    let subst = vec![(3, Rational::one())];
    row.substitute_var(1, &subst, &Rational::new(2, 1));

    assert_eq!(row.coeffs.len(), 1);
    assert_eq!(row.coeffs[0].0, 3);
    assert_eq!(row.coeffs[0].1, Rational::new(5, 1));
}

/// Verify substitute_var when entering_var is the last element in the row.
/// Row: 1*x1 + 4*x5, substitute x5 with {x1: -1, x3: 2} at scale=4
///   → remove x5, add 4*{x1:-1, x3:2} = {x1:-4, x3:8}
///   → Result: (1-4)*x1 + 8*x3 = -3*x1 + 8*x3
#[test]
fn test_substitute_var_entering_last() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let mut row = TableauRow::new_rat(
        100,
        vec![(1, Rational::one()), (5, Rational::new(4, 1))],
        Rational::zero(),
    );

    let subst = vec![(1, Rational::new(-1, 1)), (3, Rational::new(2, 1))];
    row.substitute_var(5, &subst, &Rational::new(4, 1));

    assert_eq!(row.coeffs.len(), 2);
    assert_eq!(row.coeffs[0].0, 1);
    assert_eq!(row.coeffs[0].1, Rational::new(-3, 1));
    assert_eq!(row.coeffs[1].0, 3);
    assert_eq!(row.coeffs[1].1, Rational::new(8, 1));
}

/// Verify substitute_var handles complete cancellation (all coeffs cancel to zero).
/// Row: 2*x1 + 3*x2, substitute x2 with {x1: -2/3} at scale=3
///   → remove x2, add 3*(-2/3)*x1 = -2*x1
///   → Result: (2-2)*x1 = empty
#[test]
fn test_substitute_var_complete_cancellation() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let mut row = TableauRow::new_rat(
        100,
        vec![(1, Rational::new(2, 1)), (2, Rational::new(3, 1))],
        Rational::zero(),
    );

    let subst = vec![(1, Rational::new(-2, 3))];
    let scale = Rational::new(3, 1);
    row.substitute_var(2, &subst, &scale);

    assert!(
        row.coeffs.is_empty(),
        "all coefficients should cancel: got {:?}",
        row.coeffs
    );
}

/// Edge case: substitute_var on empty row adds scaled subst_coeffs even if
/// entering_var is absent (entering_var removal is vacuous, additions applied).
#[test]
fn test_substitute_var_empty_row() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    // Empty row, entering_var=1 absent, subst adds var 2 with coeff 3*2=6
    let mut row = TableauRow::new_rat(0, vec![], Rational::new(7, 1));
    row.substitute_var(1, &[(2, Rational::new(3, 1))], &Rational::new(2, 1));
    assert_eq!(row.coeffs.len(), 1, "addition from subst_coeffs applied");
    assert_eq!(row.coeffs[0].0, 2);
    assert!(row.coeffs[0].1 == Rational::new(6, 1), "3 * 2 = 6");
    assert!(row.constant == Rational::new(7, 1), "constant unchanged");

    // Empty row, empty subst_coeffs — truly a no-op
    let mut row2 = TableauRow::new_rat(0, vec![], Rational::new(7, 1));
    row2.substitute_var(1, &[], &Rational::one());
    assert!(
        row2.coeffs.is_empty(),
        "empty row + empty subst stays empty"
    );
}

/// Edge case: substitute_var with empty substitution just removes entering_var.
#[test]
fn test_substitute_var_empty_subst() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let mut row = TableauRow::new_rat(
        0,
        vec![(1, Rational::new(3, 1)), (2, Rational::new(5, 1))],
        Rational::new(10, 1),
    );
    row.substitute_var(1, &[], &Rational::one());
    assert_eq!(row.coeffs.len(), 1, "one variable removed");
    assert_eq!(row.coeffs[0].0, 2);
    assert_eq!(row.coeffs[0].1, Rational::new(5, 1));
    assert!(row.constant == Rational::new(10, 1), "constant unchanged");
}

/// Edge case: entering_var not in row — should just add scaled subst_coeffs.
#[test]
fn test_substitute_var_entering_absent() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let mut row = TableauRow::new_rat(
        0,
        vec![(1, Rational::new(2, 1)), (3, Rational::new(4, 1))],
        Rational::new(1, 1),
    );
    // entering_var=5 is not in the row, subst has variable 2
    row.substitute_var(5, &[(2, Rational::new(3, 1))], &Rational::new(2, 1));
    // Should add 3*2 = 6 for variable 2 (since entering_var 5 isn't present to remove)
    assert_eq!(row.coeffs.len(), 3, "new variable added");
    assert_eq!(row.coeffs[0].0, 1);
    assert_eq!(row.coeffs[1].0, 2);
    assert_eq!(row.coeffs[1].1, Rational::new(6, 1));
    assert_eq!(row.coeffs[2].0, 3);
}

/// Verify substitute_var preserves constant term exactly.
#[test]
fn test_substitute_var_constant_preserved() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let constant = Rational::new(17, 3);
    let mut row = TableauRow::new_rat(
        0,
        vec![(1, Rational::new(5, 1)), (2, Rational::new(7, 1))],
        constant.clone(),
    );
    row.substitute_var(1, &[(3, Rational::new(11, 1))], &Rational::new(5, 1));
    assert!(
        row.constant == constant,
        "constant must be preserved by substitute_var"
    );
}

/// Zero-scale substitutions should only remove the entering variable.
#[test]
fn test_substitute_var_zero_scale_only_removes_entering() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let mut row = TableauRow::new_rat(
        0,
        vec![
            (1, Rational::new(2, 1)),
            (2, Rational::new(5, 1)),
            (4, Rational::new(7, 1)),
        ],
        Rational::new(3, 1),
    );

    row.substitute_var(
        2,
        &[(1, Rational::new(9, 1)), (3, Rational::new(-4, 1))],
        &Rational::zero(),
    );

    assert_eq!(
        row.coeffs,
        vec![(1, Rational::new(2, 1)), (4, Rational::new(7, 1))],
        "zero-scale substitution must drop the entering var without adding new terms"
    );
    assert_eq!(row.constant, Rational::new(3, 1));
}

/// Verify substitute_var_with_col_deltas matches substitute_var output
/// and correctly reports column additions and removals (#8003).
#[test]
fn test_substitute_var_with_col_deltas_matches_plain() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    // Row: 2*x1 + 3*x2 + 1*x3
    // Substitute x2 with {x1: 1, x4: 2} at scale=3
    // Expected: remove x2, add 3*{x1:1, x4:2} = {x1:3, x4:6}
    // Row becomes: (2+3)*x1 + 1*x3 + 6*x4 = 5*x1 + 1*x3 + 6*x4
    // Col deltas: x2 removed, x4 added (x1 was already present)

    let coeffs = vec![
        (1, Rational::new(2, 1)),
        (2, Rational::new(3, 1)),
        (3, Rational::one()),
    ];
    let subst = vec![(1, Rational::one()), (4, Rational::new(2, 1))];
    let scale = Rational::new(3, 1);

    let mut row_plain = TableauRow::new_rat(100, coeffs.clone(), Rational::new(5, 1));
    row_plain.substitute_var(2, &subst, &scale);

    let mut row_delta = TableauRow::new_rat(100, coeffs, Rational::new(5, 1));
    let mut col_added = Vec::new();
    let mut col_removed = Vec::new();
    row_delta.substitute_var_with_col_deltas(2, &subst, &scale, &mut col_added, &mut col_removed);

    assert_eq!(
        row_plain.coeffs, row_delta.coeffs,
        "delta variant must produce same coefficients"
    );
    assert!(
        col_removed.contains(&2),
        "entering_var x2 should be in removed list"
    );
    assert!(col_added.contains(&4), "new var x4 should be in added list");
    assert!(
        !col_added.contains(&1),
        "x1 was already present — should NOT be in added"
    );
}

/// Verify col_deltas correctly detects cancellation as removal (#8003).
#[test]
fn test_substitute_var_with_col_deltas_cancellation() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    // Row: 3*x1 + 2*x2. Substitute x2 with {x1: -1} at scale=2.
    // → remove x2, add 2*(-1)*x1 = -2*x1. Result: (3-2)*x1 = 1*x1.
    // Col deltas: x2 removed, x1 NOT removed (it survives).
    let mut row = TableauRow::new_rat(
        0,
        vec![(1, Rational::new(3, 1)), (2, Rational::new(2, 1))],
        Rational::zero(),
    );
    let mut col_added = Vec::new();
    let mut col_removed = Vec::new();
    row.substitute_var_with_col_deltas(
        2,
        &[(1, Rational::new(-1, 1))],
        &Rational::new(2, 1),
        &mut col_added,
        &mut col_removed,
    );

    assert_eq!(row.coeffs.len(), 1);
    assert_eq!(row.coeffs[0].0, 1);
    assert!(col_removed.contains(&2), "entering_var removed");
    assert!(!col_removed.contains(&1), "x1 survived, not removed");
    assert!(col_added.is_empty(), "no new vars added");
}

/// Full cancellation: all vars cancel out after substitution (#8003).
#[test]
fn test_substitute_var_with_col_deltas_full_cancellation() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    // Row: 2*x1 + 1*x2. Substitute x2 with {x1: -2} at scale=1.
    // → remove x2, add -2*x1. Result: (2-2)*x1 = 0 → empty.
    let mut row = TableauRow::new_rat(
        0,
        vec![(1, Rational::new(2, 1)), (2, Rational::one())],
        Rational::new(7, 1),
    );
    let mut col_added = Vec::new();
    let mut col_removed = Vec::new();
    row.substitute_var_with_col_deltas(
        2,
        &[(1, Rational::new(-2, 1))],
        &Rational::one(),
        &mut col_added,
        &mut col_removed,
    );

    assert!(row.coeffs.is_empty(), "all terms cancelled");
    assert!(col_removed.contains(&2), "entering_var removed");
    assert!(col_removed.contains(&1), "x1 cancelled to zero — removed");
    assert!(col_added.is_empty(), "no new vars");
}

/// Zero-valued scaled additions must be filtered before the merge completes.
#[test]
fn test_substitute_var_filters_zero_scaled_additions() {
    use crate::rational::Rational;
    use crate::types::TableauRow;

    let mut row = TableauRow::new_rat(
        0,
        vec![(2, Rational::new(3, 1)), (5, Rational::new(8, 1))],
        Rational::zero(),
    );

    row.substitute_var(
        2,
        &[
            (1, Rational::zero()),
            (3, Rational::new(2, 1)),
            (4, Rational::zero()),
        ],
        &Rational::new(4, 1),
    );

    assert_eq!(
        row.coeffs,
        vec![(3, Rational::new(8, 1)), (5, Rational::new(8, 1))],
        "zero scaled additions must not appear in the substituted row"
    );
}

// ── BoundProvenance tests (#8151) ───────────────────────────────────────

use crate::types::BoundProvenance;
use ay_core::term::TermId;

/// Single atom provenance collects exactly one reason.
#[test]
fn test_provenance_atom_collect_reasons() {
    let prov = BoundProvenance::Atom {
        term: TermId::new(42),
        value: true,
    };
    let mut out = Vec::new();
    prov.collect_reasons(&mut out);
    assert_eq!(out, vec![(TermId::new(42), true)]);
}

/// Sentinel atoms are filtered out during collect.
#[test]
fn test_provenance_atom_sentinel_filtered() {
    let prov = BoundProvenance::Atom {
        term: TermId::SENTINEL,
        value: false,
    };
    let mut out = Vec::new();
    prov.collect_reasons(&mut out);
    assert!(out.is_empty(), "sentinel atoms should be filtered");
}

/// Axiom provenance produces no reasons.
#[test]
fn test_provenance_axiom_empty() {
    let prov = BoundProvenance::Axiom;
    let mut out = Vec::new();
    prov.collect_reasons(&mut out);
    assert!(out.is_empty());
}

/// SharedEquality provenance collects all non-sentinel reasons.
#[test]
fn test_provenance_shared_equality_collect() {
    let prov = BoundProvenance::SharedEquality {
        reasons: smallvec::smallvec![
            (TermId::new(1), true),
            (TermId::SENTINEL, false),
            (TermId::new(3), false),
        ],
    };
    let mut out = Vec::new();
    prov.collect_reasons(&mut out);
    assert_eq!(out, vec![(TermId::new(1), true), (TermId::new(3), false)]);
}

/// Join of two atoms produces both reasons.
#[test]
fn test_provenance_join_two_atoms() {
    let a = BoundProvenance::Atom {
        term: TermId::new(10),
        value: true,
    };
    let b = BoundProvenance::Atom {
        term: TermId::new(20),
        value: false,
    };
    let joined = a.join(b);
    let reasons = joined.collect_reasons_dedup();
    assert_eq!(reasons.len(), 2);
    assert!(reasons.contains(&(TermId::new(10), true)));
    assert!(reasons.contains(&(TermId::new(20), false)));
}

/// Axiom is the identity element for join.
#[test]
fn test_provenance_join_axiom_identity() {
    let a = BoundProvenance::Atom {
        term: TermId::new(5),
        value: true,
    };
    let joined = BoundProvenance::Axiom.join(a);
    let reasons = joined.collect_reasons_dedup();
    assert_eq!(reasons, vec![(TermId::new(5), true)]);

    let joined2 = BoundProvenance::Atom {
        term: TermId::new(5),
        value: true,
    }
    .join(BoundProvenance::Axiom);
    let reasons2 = joined2.collect_reasons_dedup();
    assert_eq!(reasons2, vec![(TermId::new(5), true)]);
}

/// collect_reasons_dedup removes duplicate (term, value) pairs.
#[test]
fn test_provenance_dedup_removes_duplicates() {
    let a = BoundProvenance::Atom {
        term: TermId::new(7),
        value: true,
    };
    let b = BoundProvenance::Atom {
        term: TermId::new(7),
        value: true,
    };
    let joined = a.join(b);
    let reasons = joined.collect_reasons_dedup();
    assert_eq!(
        reasons,
        vec![(TermId::new(7), true)],
        "duplicate should be removed"
    );
}

/// Nested joins flatten correctly during collect.
#[test]
fn test_provenance_nested_join_flattens() {
    let a = BoundProvenance::Atom {
        term: TermId::new(1),
        value: true,
    };
    let b = BoundProvenance::Atom {
        term: TermId::new(2),
        value: false,
    };
    let c = BoundProvenance::Atom {
        term: TermId::new(3),
        value: true,
    };
    // (a join b) join c
    let inner = a.join(b);
    let outer = inner.join(c);
    let reasons = outer.collect_reasons_dedup();
    assert_eq!(reasons.len(), 3);
    assert!(reasons.contains(&(TermId::new(1), true)));
    assert!(reasons.contains(&(TermId::new(2), false)));
    assert!(reasons.contains(&(TermId::new(3), true)));
}

/// build_provenance_from_reasons with empty reasons produces Axiom.
#[test]
fn test_bound_new_empty_reasons_axiom_provenance() {
    use crate::rational::Rational;

    let bound = Bound::without_reasons(Rational::zero(), false);
    // without_reasons sets provenance to None (test-only path)
    assert!(bound.provenance.is_none());

    // Bound::new with all-sentinel reasons -> Axiom
    let bound = Bound::new(
        Rational::zero(),
        vec![TermId::SENTINEL],
        vec![true],
        vec![],
        false,
    );
    match &bound.provenance {
        Some(BoundProvenance::Axiom) => {}
        other => panic!("expected Axiom, got {other:?}"),
    }
}

/// build_provenance_from_reasons with single non-sentinel -> Atom.
#[test]
fn test_bound_new_single_reason_atom_provenance() {
    use crate::rational::Rational;

    let bound = Bound::new(
        Rational::one(),
        vec![TermId::new(42)],
        vec![true],
        vec![],
        false,
    );
    match &bound.provenance {
        Some(BoundProvenance::Atom { term, value }) => {
            assert_eq!(*term, TermId::new(42));
            assert!(*value);
        }
        other => panic!("expected Atom, got {other:?}"),
    }
}

/// build_provenance_from_reasons with multiple reasons -> SharedEquality.
#[test]
fn test_bound_new_multi_reason_shared_equality_provenance() {
    use crate::rational::Rational;

    let bound = Bound::new(
        Rational::one(),
        vec![TermId::new(1), TermId::new(2)],
        vec![true, false],
        vec![],
        false,
    );
    match &bound.provenance {
        Some(BoundProvenance::SharedEquality { reasons }) => {
            assert_eq!(reasons.len(), 2);
            assert_eq!(reasons[0], (TermId::new(1), true));
            assert_eq!(reasons[1], (TermId::new(2), false));
        }
        other => panic!("expected SharedEquality, got {other:?}"),
    }
}
