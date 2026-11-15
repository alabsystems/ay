// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the hoisted equation basis of the affine implication
//! accelerator (#affine-rref-hoist, `affine_implication/basis.rs`): the
//! span filter agrees exactly with the trusted rank test, undecided
//! reductions defer to that test, and solver-level conflicts are unchanged.

use super::*;
use num_rational::BigRational;

/// Build a rational row from integer cells (last cell = constant column).
fn row(cells: &[i64]) -> Vec<BigRational> {
    cells
        .iter()
        .map(|&c| BigRational::from(BigInt::from(c)))
        .collect()
}

/// Differential pin: over a deterministic family of small integer matrices
/// (dependent rows, zero rows, inconsistent constants, rational pivots), the
/// span test against the hoisted reduced basis agrees EXACTLY with the
/// trusted `rank(rows) == rank(rows + target)` test it filters for.
#[test]
fn test_affine_basis_span_agrees_with_rank_test() {
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % 7) as i64 - 3
    };
    let mut agreements = 0;
    let mut implied_seen = 0;
    for case in 0..400 {
        let width = 2 + case % 5; // variables + constant column
        let row_count = 1 + case % 4;
        let mut rows: Vec<Vec<BigRational>> = Vec::new();
        for _ in 0..row_count {
            let cells: Vec<i64> = (0..width).map(|_| next()).collect();
            rows.push(row(&cells));
        }
        // Half the targets are built as combinations of the rows, so the
        // implied branch is exercised as well as the excluded one.
        let target = if case % 2 == 0 {
            let mut t = vec![BigRational::zero(); width];
            for r in &rows {
                let k = BigRational::from(BigInt::from(next()));
                for (cell, value) in t.iter_mut().zip(r) {
                    *cell += &k * value;
                }
            }
            t
        } else {
            row(&(0..width).map(|_| next()).collect::<Vec<_>>())
        };

        let mut never = || false;
        let mut fuel = 1_000_000;
        let rank = LiaSolver::rational_rank(rows.clone(), &mut fuel, &mut never).unwrap();
        let mut with_target = rows.clone();
        with_target.push(target.clone());
        let rank_with = LiaSolver::rational_rank(with_target, &mut fuel, &mut never).unwrap();

        let mut fuel = 1_000_000;
        let basis = LiaSolver::rational_rref(rows, &mut fuel, &mut never).unwrap();
        assert_eq!(basis.len(), rank, "case {case}: rref rank");
        let spans = LiaSolver::affine_basis_spans(&basis, &target, &mut fuel, &mut never)
            .expect("small matrices are always decided");
        assert_eq!(spans, rank == rank_with, "case {case}: span vs rank test");
        agreements += 1;
        implied_seen += usize::from(spans);
    }
    assert_eq!(agreements, 400);
    assert!(
        implied_seen > 100,
        "both branches exercised: {implied_seen}"
    );
}

/// An undecided reduction (fuel exhausted) is reported as `None`, never as
/// "not in span" — the filter must then defer to the trusted test.
#[test]
fn test_affine_basis_span_out_of_fuel_is_undecided() {
    let rows = vec![row(&[1, -1, 0, 0]), row(&[0, 1, -1, 0])];
    let target = row(&[1, 0, -1, 0]);
    let mut never = || false;
    let mut fuel = 1_000_000;
    let basis = LiaSolver::rational_rref(rows, &mut fuel, &mut never).unwrap();
    let mut empty = 0;
    assert_eq!(
        LiaSolver::affine_basis_spans(&basis, &target, &mut empty, &mut never),
        None
    );
    let mut abort = || true;
    let mut fuel = 1_000_000;
    assert_eq!(
        LiaSolver::affine_basis_spans(&basis, &target, &mut fuel, &mut abort),
        None
    );
}

/// Several disequalities against one equation set: the hoisted filter skips
/// the unimplied ones (including one over a variable no equation mentions)
/// and the implied one still yields the same narrowed conflict.
#[test]
fn test_affine_hoisted_basis_finds_the_one_implied_disequality() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let one = terms.mk_int(BigInt::one());
    let two = terms.mk_int(BigInt::from(2));
    let b_plus_one = terms.mk_add(vec![b, one]);
    let c_minus_one = terms.mk_sub(vec![c, one]);
    let eq_ab = terms.mk_eq(a, b_plus_one); // a = b + 1
    let eq_bc = terms.mk_eq(b, c_minus_one); // b = c - 1
    let ne_ab = terms.mk_eq(a, b); // a != b     (not implied: a - b = 1)
    let ne_ad = terms.mk_eq(a, d); // a != d     (d unconstrained)
    let ne_c2 = terms.mk_eq(c, two); // c != 2   (not implied)
    let ne_ac = terms.mk_eq(a, c); // a != c     (implied)

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_bc, true);
    solver.assert_literal(ne_ab, false);
    solver.assert_literal(ne_ad, false);
    solver.assert_literal(ne_c2, false);
    solver.assert_literal(ne_ac, false);

    let conflict = solver
        .check_affine_disequality_implication(false)
        .expect("a = b+1, b = c-1 contradicts a != c");
    let mut expected = vec![
        TheoryLit::new(eq_ab, true),
        TheoryLit::new(eq_bc, true),
        TheoryLit::new(ne_ac, false),
    ];
    expected.sort_unstable();
    assert_eq!(conflict.literals, expected);
    // Only the implied disequality reached the trusted test and the core
    // extraction behind it.
    assert_eq!(solver.affine_min_core_attempts, 1);
    assert_conflict_soundness(
        TheoryResult::Unsat(conflict.literals),
        LiaSolver::new(&terms),
    );
}

/// No disequality implied: the filter must return no conflict, and must not
/// have run the core extraction at all.
#[test]
fn test_affine_hoisted_basis_no_implication_no_conflict() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let one = terms.mk_int(BigInt::one());
    let b_plus_one = terms.mk_add(vec![b, one]);
    let eq_ab = terms.mk_eq(a, b_plus_one);
    let ne_ab = terms.mk_eq(a, b);
    let ne_ad = terms.mk_eq(a, d);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(ne_ab, false);
    solver.assert_literal(ne_ad, false);
    assert!(solver.check_affine_disequality_implication(false).is_none());
    assert_eq!(solver.affine_min_core_attempts, 0);
}
