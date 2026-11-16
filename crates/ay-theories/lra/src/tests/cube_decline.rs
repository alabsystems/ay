// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #cube-decline-no-trace: a cube test that declines leaves the assignment
//! exactly where it found it.
//!
//! The tightened bounds live only inside the test's push scope, but the
//! re-solve under them moves the assignment, and `pop` restores bounds, not
//! values. Before this contract a declined test left the LP at the point it
//! had chosen and rejected; the NIA refinement read that point after a
//! rejected tentative patch and walked a branch-and-bound variable one unit
//! per round into the split loop's oscillation guard (`unknown` on a
//! satisfiable `a * b > 2^64 - 1`; see
//! `ay-dpll/tests/group_regression/nia_cube_decline_keeps_point.rs`).
//!
//! The sweep below runs the cube test on small two-row integer LPs and
//! checks the contract on every one: `false` means the assignment is
//! unchanged, `true` means it satisfies every bound. Dropping the restores
//! in `try_cube_test` fails it.

use super::*;

/// One `lo <= a*x + b*y <= hi` row over the Int variables `x`, `y`.
#[derive(Clone, Copy)]
struct Row {
    a: i64,
    b: i64,
    lo: i64,
    hi: i64,
}

fn int(store: &mut TermStore, n: i64) -> TermId {
    store.mk_int(BigInt::from(n))
}

/// Runs the cube test on one LP. `None` when the LP is not feasible (nothing
/// to test); otherwise whether the test succeeded and whether the contract
/// held.
fn run_case(rows: &[Row; 2]) -> Option<(bool, Result<(), String>)> {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let mut atoms = Vec::new();
    for row in rows {
        let a = int(&mut terms, row.a);
        let b = int(&mut terms, row.b);
        let ax = terms.mk_mul(vec![a, x]);
        let by = terms.mk_mul(vec![b, y]);
        let sum = terms.mk_add(vec![ax, by]);
        let lo = int(&mut terms, row.lo);
        let hi = int(&mut terms, row.hi);
        atoms.push(terms.mk_ge(sum, lo));
        atoms.push(terms.mk_le(sum, hi));
    }
    // A box on the originals: their bounds are what rounding and the
    // nonbasic move can break.
    let box_lo = int(&mut terms, -3);
    let box_hi = int(&mut terms, 3);
    for v in [x, y] {
        atoms.push(terms.mk_ge(v, box_lo));
        atoms.push(terms.mk_le(v, box_hi));
    }

    let mut solver = LraSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }
    if !matches!(solver.check(), TheoryResult::Sat) {
        return None;
    }
    let before: Vec<InfRational> = solver.vars.iter().map(|v| v.value.clone()).collect();
    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);

    let found = solver.try_cube_test(&integer_vars);
    let verdict = if found {
        if solver.assignment_satisfies_bounds() {
            Ok(())
        } else {
            Err("a successful cube test left an assignment outside its bounds".to_string())
        }
    } else {
        let after: Vec<InfRational> = solver.vars.iter().map(|v| v.value.clone()).collect();
        if after == before {
            Ok(())
        } else {
            Err(format!(
                "a declined cube test moved the assignment: before {before:?}, after {after:?}"
            ))
        }
    };
    Some((found, verdict))
}

#[test]
fn test_declined_cube_test_leaves_the_assignment_unchanged() {
    // Pairs of these rows meet at fractional vertices (`x + 2y >= 1` and
    // `2x + y >= 1` at `(1/3, 1/3)`), which is where the cube test has
    // something to tighten and round.
    let coeffs = [(1, 2), (2, 1), (1, 1), (3, 2), (2, -3), (1, -1)];
    let lows = [1, 2, 3, -5];
    let widths = [0, 1, 2, 5];
    let mut feasible = 0usize;
    let mut declined = 0usize;
    let mut failures = Vec::new();
    for &(a1, b1) in &coeffs {
        for &(a2, b2) in &coeffs {
            if (a1, b1) == (a2, b2) {
                continue;
            }
            for &lo1 in &lows {
                for &w1 in &widths {
                    for &lo2 in &lows {
                        for &w2 in &widths {
                            let rows = [
                                Row {
                                    a: a1,
                                    b: b1,
                                    lo: lo1,
                                    hi: lo1 + w1,
                                },
                                Row {
                                    a: a2,
                                    b: b2,
                                    lo: lo2,
                                    hi: lo2 + w2,
                                },
                            ];
                            let Some((found, verdict)) = run_case(&rows) else {
                                continue;
                            };
                            feasible += 1;
                            if !found {
                                declined += 1;
                            }
                            if let Err(why) = verdict {
                                failures.push(format!(
                                    "rows ({a1},{b1}) in [{lo1}, {lo1}+{w1}], ({a2},{b2}) in \
                                     [{lo2}, {lo2}+{w2}]: {why}"
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    // Positive controls: the sweep must reach both outcomes, or it checks
    // nothing about the decline paths.
    assert!(feasible > 100, "only {feasible} feasible cases");
    assert!(declined > 0, "no case declined among {feasible}");
    assert!(
        declined < feasible,
        "every one of {feasible} cases declined"
    );
    assert!(
        failures.is_empty(),
        "{} of {feasible} cases broke the cube contract ({declined} declined); first: {}",
        failures.len(),
        failures[0]
    );
}

fn queued_sum(terms: &mut TermStore) -> (TermId, TermId, TermId) {
    let x = terms.mk_var("queued_x", Sort::Int);
    let y = terms.mk_var("queued_y", Sort::Int);
    let two = int(terms, 2);
    let twice_y = terms.mk_mul(vec![two, y]);
    let sum = terms.mk_add(vec![x, twice_y]);
    (x, y, sum)
}

/// Queue a real arithmetic row without registering it through a prior check.
fn queued_row(terms: &mut TermStore, lower: i64, upper: i64) -> (TermId, TermId, [TermId; 2]) {
    let (x, y, sum) = queued_sum(terms);
    let lo = int(terms, lower);
    let hi = int(terms, upper);
    (x, y, [terms.mk_ge(sum, lo), terms.mk_le(sum, hi)])
}

#[test]
fn queued_narrow_row_cube_decline_restores_the_materialized_entry_point() {
    for outer_scope in [false, true] {
        let mut terms = TermStore::new();
        let (x, y, sum) = queued_sum(&mut terms);
        let one = int(&mut terms, 1);
        let atoms = [terms.mk_eq(sum, one)];
        let mut expected = LraSolver::new(&terms);
        let mut solver = LraSolver::new(&terms);
        if outer_scope {
            expected.push();
            solver.push();
        }
        for atom in atoms {
            expected.assert_literal(atom, true);
            solver.assert_literal(atom, true);
        }
        assert!(solver.vars.is_empty() && solver.rows.is_empty());
        let depth = solver.scopes.len();
        let integers = [x, y].into_iter().collect();
        // The independent twin performs only the same public push/flush,
        // never check/simplex, to expose the intended materialized baseline.
        expected.push();
        let entry: Vec<InfRational> = expected.vars.iter().map(|v| v.value.clone()).collect();
        let row_count = expected.rows.len();
        assert!(entry.len() >= 3);
        assert_eq!(row_count, 1);
        // Unlike two comparisons, this equality installs both bounds on
        // ONE slack. A positive delta must therefore reject immediately.
        let row = &expected.rows[0];
        let basic = &expected.vars[row.basic_var as usize];
        let lower = basic.lower.as_ref().expect("queued equality lower bound");
        let upper = basic.upper.as_ref().expect("queued equality upper bound");
        assert_eq!(lower.value, upper.value);
        let delta = LraSolver::cube_delta_for_row(&row.coeffs, row.basic_var, &integers, &expected);
        assert!(delta > Rational::Small(0, 1));
        expected.pop();
        assert_eq!(expected.scopes.len(), depth);

        assert!(!solver.try_cube_test(&integers));
        assert_eq!(solver.scopes.len(), depth);
        assert_eq!(solver.rows.len(), row_count);
        let after: Vec<InfRational> = solver.vars.iter().map(|v| v.value.clone()).collect();
        assert_eq!(after, entry);
        assert!(matches!(solver.check(), TheoryResult::Sat));
        assert!(solver.assignment_satisfies_bounds());
        assert_eq!(solver.scopes.len(), depth);
    }
}

/// The comparison spelling has opposite signed one-sided slacks. The cube
/// fallback may legitimately find an integer witness after tightening fails.
#[test]
fn queued_comparison_row_cube_success_keeps_a_valid_integer_point() {
    for outer_scope in [false, true] {
        let mut terms = TermStore::new();
        let (x, y, atoms) = queued_row(&mut terms, 1, 1);
        let mut solver = LraSolver::new(&terms);
        if outer_scope {
            solver.push();
        }
        for atom in atoms {
            solver.assert_literal(atom, true);
        }
        assert!(solver.vars.is_empty() && solver.rows.is_empty());
        let depth = solver.scopes.len();
        let integers = [x, y].into_iter().collect();
        assert!(solver.try_cube_test(&integers));
        assert!(solver.vars.len() >= 3 && !solver.rows.is_empty());
        assert_eq!(solver.scopes.len(), depth);
        assert!(solver.assignment_satisfies_bounds());
        assert!(solver.all_integer_vars_integral(&integers));
        let x_value = solver.get_value(x).expect("materialized x");
        let y_value = solver.get_value(y).expect("materialized y");
        assert_eq!(
            x_value + y_value * BigRational::from_integer(BigInt::from(2)),
            BigRational::from_integer(BigInt::from(1))
        );
        assert!(matches!(solver.check(), TheoryResult::Sat));
        assert!(solver.assignment_satisfies_bounds());
        assert_eq!(solver.scopes.len(), depth);
    }
}

#[test]
fn queued_wide_row_cube_success_materializes_without_a_prior_check() {
    for outer_scope in [false, true] {
        let mut terms = TermStore::new();
        let (x, y, atoms) = queued_row(&mut terms, -5, 5);
        let mut solver = LraSolver::new(&terms);
        if outer_scope {
            solver.push();
        }
        for atom in atoms {
            solver.assert_literal(atom, true);
        }
        assert!(solver.vars.is_empty() && solver.rows.is_empty());
        let depth = solver.scopes.len();
        let integers = [x, y].into_iter().collect();
        assert!(solver.try_cube_test(&integers));
        assert!(solver.vars.len() >= 3 && !solver.rows.is_empty());
        assert_eq!(solver.scopes.len(), depth);
        assert!(solver.assignment_satisfies_bounds());
        assert!(solver.all_integer_vars_integral(&integers));
        assert!(matches!(solver.check(), TheoryResult::Sat));
        assert!(solver.assignment_satisfies_bounds());
        assert_eq!(solver.scopes.len(), depth);
    }
}
