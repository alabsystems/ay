// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Side-split implied-bound generations: a row direction re-analyzes
//! only when a bound side it actually reads has changed. The basic
//! variable is the recorded exception — either of its sides changing
//! re-analyzes both directions, because each direction's derivation
//! block also reads the basic variable's opposite side.

use super::*;
use crate::types::ColEntry;

fn bound(value: i64) -> Bound {
    Bound::new(
        BigRational::from(BigInt::from(value)).into(),
        vec![TermId::new(900)],
        vec![true],
        vec![Rational::one()],
        false,
    )
}

/// Row `y = x` (`y` basic in row 0) with `0 <= y <= 10` asserted
/// directly and `x` initially unbounded. One analysis pass has already
/// derived `0 <= x <= 10`.
fn solver_y_eq_x(terms: &TermStore) -> LraSolver {
    let mut solver = LraSolver::new(terms);
    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(0)),
            upper: Some(bound(10)),
            status: Some(VarStatus::Basic(0)),
        },
    ];
    solver.rows = vec![TableauRow::new(
        1,
        vec![(0, BigRational::from(BigInt::from(1)))],
        BigRational::zero(),
    )];
    solver.col_index = vec![Vec::new(); 2];
    solver.col_index[0].push(ColEntry::new(0, 0));
    solver.basic_var_to_row.insert(1, 0);
    solver.touched_rows.insert(0);
    solver.compute_implied_bounds();
    assert_eq!(
        solver.implied_bounds[0]
            .0
            .clone()
            .expect("x >= 0 derived")
            .value,
        Rational::from(0)
    );
    assert_eq!(
        solver.implied_bounds[0]
            .1
            .clone()
            .expect("x <= 10 derived")
            .value,
        Rational::from(10)
    );
    // One cascade round only, so the counters below measure exactly
    // the re-analysis triggered by the tightened direct bound.
    solver.bcp_implied_single_pass = true;
    solver
}

/// Tightening the nonbasic `x >= 2` feeds only the UB direction of
/// `y - x = 0` (it reads `x`'s lower side and `y`'s upper side); the
/// LB direction reads `x`'s upper side and `y`'s lower side, neither
/// of which moved. The UB direction must still derive `y >= 2`, and
/// the only dropped derivation is its own equal `x <= 10` — the LB
/// direction's equal `y <= 10` must not be recomputed (its weaker
/// `x >= 0` candidate is f64-screened before the exact test either
/// way).
#[test]
fn nonbasic_side_change_reanalyzes_only_the_direction_that_reads_it() {
    let terms = TermStore::new();
    let mut solver = solver_y_eq_x(&terms);
    let skips_before = solver.stats.implied_not_tighter_skips;
    let analyzed_before = solver.stats.implied_rows_analyzed;

    solver.vars[0].lower = Some(bound(2));
    solver.direct_bounds_changed_since_implied = true;
    solver.direct_bounds_changed_vars.push(0);
    solver.touched_rows.insert(0);
    solver.compute_implied_bounds();

    assert_eq!(
        solver.implied_bounds[1]
            .0
            .clone()
            .expect("y >= 2 derived by the fresh direction")
            .value,
        Rational::from(2)
    );
    assert_eq!(
        solver.stats.implied_rows_analyzed,
        analyzed_before + 1,
        "the row is analyzed once"
    );
    assert_eq!(
        solver.stats.implied_not_tighter_skips,
        skips_before + 1,
        "only the fresh direction's equal x <= 10 is re-derived and dropped"
    );
}

/// Tightening the basic variable `y >= 2` must re-analyze BOTH row
/// directions, including the UB direction whose accumulation reads
/// only `y`'s (unchanged) upper side: each direction's derivation
/// block reads the basic variable's opposite side when it derives
/// and admits bounds, so a basic-side change stamps both directions.
/// Observable as both directions' equal re-derivations being
/// recomputed and dropped around the one tighter `x >= 2` (the
/// third, strictly weaker candidate is f64-screened before the
/// exact not-tighter test in either implementation).
#[test]
fn basic_side_change_reanalyzes_both_directions() {
    let terms = TermStore::new();
    let mut solver = solver_y_eq_x(&terms);
    let skips_before = solver.stats.implied_not_tighter_skips;

    solver.vars[1].lower = Some(bound(2));
    solver.direct_bounds_changed_since_implied = true;
    solver.direct_bounds_changed_vars.push(1);
    solver.touched_rows.insert(0);
    solver.compute_implied_bounds();

    assert_eq!(
        solver.implied_bounds[0]
            .0
            .clone()
            .expect("x >= 2 derived")
            .value,
        Rational::from(2)
    );
    assert_eq!(
        solver.stats.implied_not_tighter_skips,
        skips_before + 2,
        "both directions re-derive their equal bounds"
    );
}
