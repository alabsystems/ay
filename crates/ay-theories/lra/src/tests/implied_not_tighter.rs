// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `compute_implied_bounds` drops a derivation that is not tighter than the
//! slot it targets before building its explanation. These tests pin the
//! strict-aware order of that pre-filter (it must keep exactly what the
//! deferred-update apply loop keeps) and that a re-analysed row which only
//! re-derives the bounds it already produced leaves the stored bounds alone.

use super::*;
use crate::types::ColEntry;

fn implied(value: i64, strict: bool) -> ImpliedBound {
    ImpliedBound {
        value: Rational::from(value),
        strict,
        row_idx: 0,
        explanation: None,
    }
}

/// The pre-filter is the exact negation of the apply loop's `tighter` test,
/// strictness included, on both sides.
#[test]
fn not_tighter_matches_the_apply_loop_order_on_both_sides() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    solver.implied_bounds = vec![(Some(implied(0, false)), Some(implied(10, false)))];
    let r = Rational::from;

    // Empty slot: anything is tighter.
    solver.implied_bounds.push((None, None));
    assert!(!solver.derived_bound_not_tighter(1, false, &r(-5), false));
    assert!(!solver.derived_bound_not_tighter(1, true, &r(5), false));

    // Lower side, current `x >= 0`.
    assert!(
        solver.derived_bound_not_tighter(0, false, &r(-1), true),
        "looser lower"
    );
    assert!(
        solver.derived_bound_not_tighter(0, false, &r(0), false),
        "equal, same strictness"
    );
    assert!(
        !solver.derived_bound_not_tighter(0, false, &r(0), true),
        "x > 0 tightens x >= 0"
    );
    assert!(
        !solver.derived_bound_not_tighter(0, false, &r(1), false),
        "higher lower"
    );

    // Upper side, current `x <= 10`.
    assert!(
        solver.derived_bound_not_tighter(0, true, &r(11), true),
        "looser upper"
    );
    assert!(
        solver.derived_bound_not_tighter(0, true, &r(10), false),
        "equal, same strictness"
    );
    assert!(
        !solver.derived_bound_not_tighter(0, true, &r(10), true),
        "x < 10 tightens x <= 10"
    );
    assert!(
        !solver.derived_bound_not_tighter(0, true, &r(9), false),
        "lower upper"
    );

    // A strict slot is not tightened by the same value, strict or not.
    solver.implied_bounds[0] = (Some(implied(0, true)), Some(implied(10, true)));
    assert!(solver.derived_bound_not_tighter(0, false, &r(0), true));
    assert!(solver.derived_bound_not_tighter(0, false, &r(0), false));
    assert!(solver.derived_bound_not_tighter(0, true, &r(10), true));
    assert!(solver.derived_bound_not_tighter(0, true, &r(10), false));
}

/// Row `y = x` with `y >= 0` (reason term 900): one tableau, analysed three
/// times. The first pass derives `x >= 0`. Re-analysing it unchanged
/// re-derives only bounds the slots already hold, so nothing is stored and
/// the pre-filter counts the drops. Strengthening `y` to `y > 0` derives
/// `x > 0` — same value, stricter — which the pre-filter must let through.
#[test]
fn rederived_bounds_are_dropped_and_a_strictness_upgrade_is_kept() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    let bound = |value: i64, strict: bool| {
        Bound::new(
            BigRational::from(BigInt::from(value)).into(),
            vec![TermId::new(900)],
            vec![true],
            vec![Rational::one()],
            strict,
        )
    };
    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(0, false)),
            upper: None,
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

    // Pass 1: x >= 0 from y >= 0.
    solver.compute_implied_bounds();
    let x_lower = solver.implied_bounds[0].0.clone().expect("x >= 0 derived");
    assert_eq!(x_lower.value, Rational::from(0));
    assert!(!x_lower.strict);
    let trail_after_first = solver.implied_trail.len();

    // Pass 2: nothing changed but the row is re-analysed. Every derivation
    // equals a stored bound: dropped before an explanation is built, and no
    // slot is replaced (the implied trail does not grow).
    let skips_before = solver.stats.implied_not_tighter_skips;
    solver.stamp_var_for_rederivation(1);
    solver.compute_implied_bounds();
    assert!(
        solver.stats.implied_not_tighter_skips > skips_before,
        "re-derived equal bounds must be dropped by the pre-filter"
    );
    assert_eq!(
        solver.implied_trail.len(),
        trail_after_first,
        "no slot replaced"
    );
    let x_lower_again = solver.implied_bounds[0].0.clone().expect("x >= 0 kept");
    assert_eq!(x_lower_again.value, Rational::from(0));
    assert!(!x_lower_again.strict);

    // Pass 3: y > 0. The derived x > 0 has the same value as the stored
    // x >= 0 but is strict, hence tighter, and must replace it.
    solver.vars[1].lower = Some(bound(0, true));
    solver.direct_bounds_changed_since_implied = true;
    solver.direct_bounds_changed_vars.push(1);
    solver.touched_rows.insert(0);
    solver.compute_implied_bounds();
    let x_strict = solver.implied_bounds[0].0.clone().expect("x > 0 derived");
    assert_eq!(x_strict.value, Rational::from(0));
    assert!(
        x_strict.strict,
        "a strictness upgrade is tighter and must be stored"
    );
    let expl = x_strict
        .explanation
        .expect("x is interesting: explanation built");
    assert_eq!(expl.contributing_vars.len(), 1);
    assert_eq!(expl.contributing_vars[0].var, 1);
    assert!(expl.contributing_vars[0].strict);
}

/// A direct bound that loses to the already-stored implied slot changes no
/// row-analysis input, so the incremental overlay must not stamp the
/// variable's bound generation. Stamping it anyway defeats the
/// generation skip and re-analyzes every row containing the variable to
/// re-derive identical bounds — the full-scan overlay already stamps only
/// on change for exactly this reason (measured there on Gcd: 35M rows
/// re-analyzed in 20 s). Row arithmetic reads only slot values and
/// strictness, so an unchanged slot needs no new generation.
#[test]
fn weaker_direct_bound_does_not_stamp_var_for_rederivation() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    let bound = |value: i64, strict: bool| {
        Bound::new(
            BigRational::from(BigInt::from(value)).into(),
            vec![TermId::new(900)],
            vec![true],
            vec![Rational::one()],
            strict,
        )
    };
    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(0, false)),
            upper: None,
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

    // Pass 1 derives x >= 0 into the slot and stamps the row as analysed.
    solver.compute_implied_bounds();
    assert_eq!(
        solver.implied_bounds[0]
            .0
            .clone()
            .expect("x >= 0 derived")
            .value,
        Rational::from(0)
    );
    let gen_before = solver.var_bound_gen.clone();
    let analyzed_before = solver.stats.implied_rows_analyzed;

    // Assert the weaker direct bound x >= -5 through the incremental
    // overlay path. The slot keeps the tighter derived x >= 0, so no row
    // input changed: the generation must not move and the touched row
    // must be generation-skipped rather than re-analysed.
    solver.vars[0].lower = Some(bound(-5, false));
    solver.direct_bounds_changed_since_implied = true;
    solver.direct_bounds_changed_vars.push(0);
    solver.touched_rows.insert(0);
    solver.compute_implied_bounds();

    assert_eq!(
        solver.var_bound_gen, gen_before,
        "an overlay that changed no slot must not stamp the variable"
    );
    assert_eq!(
        solver.stats.implied_rows_analyzed, analyzed_before,
        "the row must be generation-skipped, not re-analysed"
    );
    assert_eq!(
        solver.implied_bounds[0]
            .0
            .clone()
            .expect("x >= 0 kept")
            .value,
        Rational::from(0)
    );
}
