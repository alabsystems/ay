// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dirty-row post-simplex propagation must be complete.
//!
//! `compute_implied_bounds` analyzes only touched rows (rows containing a
//! variable whose bound changed, plus the cascade), and `pop_inner` seeds
//! exactly the rows of the variables whose direct bounds it restored or
//! whose derived bounds it rewound, instead of forcing a full overlay and a
//! full sweep after every backtrack. Two claims, checked after random
//! sequences of bound assertions, pushes, pops and simplex pivots:
//!
//! 1. No coverage loss: every bound a full re-derivation from scratch finds
//!    on the final tableau is at least matched by the incrementally reached
//!    state. (The incremental state may be strictly tighter: bounds derived
//!    under an intermediate basis are valid consequences that single-row
//!    propagation on the final basis cannot always reproduce.)
//! 2. Soundness: every incrementally stored bound is a consequence of the
//!    current direct bounds, checked by an exact oracle — asserting the
//!    opposite strict bound on the variable makes the tableau infeasible.
//!
//! The random tableaus use unit coefficients and integer bounds so the bound
//! lattice is finite.

use super::*;

/// Deterministic xorshift PRNG (no dev-dependency needed).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

type Slot = (Option<(Rational, bool)>, Option<(Rational, bool)>);

fn snapshot(solver: &LraSolver) -> Vec<Slot> {
    solver
        .implied_bounds
        .iter()
        .map(|(lb, ub)| {
            (
                lb.as_ref().map(|b| (b.value.clone(), b.strict)),
                ub.as_ref().map(|b| (b.value.clone(), b.strict)),
            )
        })
        .collect()
}

/// Wipe every piece of incremental implied-bound state and re-derive from
/// scratch (full overlay, full sweep, iterated to the fixpoint).
fn full_rederive(solver: &mut LraSolver) -> Vec<Slot> {
    solver.implied_bounds.clear();
    solver.implied_trail.clear();
    solver.var_bound_gen.clear();
    solver.row_computed_gen.clear();
    solver.implied_tighten_streak.clear();
    solver.touched_rows.clear();
    solver.direct_bounds_changed_vars.clear();
    solver.direct_bounds_changed_since_implied = true;
    solver.ib_overlay_complete = false;
    for _ in 0..64 {
        let result = solver.compute_implied_bounds();
        if result.newly_bounded.is_empty() && result.converged {
            break;
        }
    }
    snapshot(solver)
}

fn run_trial(seed: u64) {
    let mut rng = Rng(seed | 1);
    let mut terms = TermStore::new();
    let n_vars = 6;
    let vars: Vec<TermId> = (0..n_vars)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Real))
        .collect();
    // Unit-coefficient expressions: singles, pair sums/differences, one triple.
    let mut exprs: Vec<TermId> = vars.clone();
    for _ in 0..7 {
        let a = rng.below(n_vars);
        let mut b = rng.below(n_vars);
        while b == a {
            b = rng.below(n_vars);
        }
        let e = if rng.below(2) == 0 {
            terms.mk_add(vec![vars[a], vars[b]])
        } else {
            terms.mk_sub(vec![vars[a], vars[b]])
        };
        exprs.push(e);
    }
    exprs.push(terms.mk_add(vec![vars[0], vars[1], vars[2]]));
    // Two bound atoms per expression with small integer thresholds.
    let mut atoms: Vec<TermId> = Vec::new();
    for &e in &exprs {
        let c1 = terms.mk_rational(BigRational::from(BigInt::from(rng.below(7) as i64 - 3)));
        let c2 = terms.mk_rational(BigRational::from(BigInt::from(rng.below(7) as i64 - 3)));
        atoms.push(terms.mk_le(e, c1));
        atoms.push(terms.mk_ge(e, c2));
    }

    let mut solver = LraSolver::new(&terms);
    for &atom in &atoms {
        solver.register_atom(atom);
    }
    let mut depth = 0usize;
    let mut asserted: Vec<TermId> = Vec::new();
    let mut checks = 0u32;
    for _step in 0..60 {
        match rng.below(10) {
            0..=3 => {
                let atom = atoms[rng.below(atoms.len())];
                if solver.asserted.contains_key(&atom) {
                    continue;
                }
                let value = rng.below(4) != 0;
                solver.assert_literal(atom, value);
                asserted.push(atom);
            }
            4..=5 => {
                solver.push();
                depth += 1;
            }
            6 if depth > 0 => {
                solver.pop();
                depth -= 1;
            }
            _ => {
                // The per-variable Zeno streak cap (#8857) refuses replacing
                // tightenings beyond a budget that only a direct-bound change
                // of THAT variable resets; a from-scratch re-derivation starts
                // with an empty budget. It is a deliberate, schedule-dependent
                // throttle, not row coverage — equalize it so the comparison
                // measures what this test is about.
                solver.implied_tighten_streak.fill(0);
                let result = solver.check();
                checks += 1;
                let _ = solver.propagate();
                if matches!(
                    result,
                    TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                ) && depth > 0
                {
                    solver.pop();
                    depth -= 1;
                }
            }
        }
    }
    // Converge the incremental state, then compare against a re-derivation
    // from scratch on the very same tableau and direct bounds.
    solver.implied_tighten_streak.fill(0);
    let result = solver.check();
    let _ = solver.propagate();
    if matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ) {
        // Infeasible tableau: bound analysis still ran, but pivots may have
        // been cut short; the comparison is only meaningful on a feasible
        // basis. Widen to the outermost scope and converge again.
        while depth > 0 {
            solver.pop();
            depth -= 1;
        }
        solver.implied_tighten_streak.fill(0);
        let _ = solver.check();
        let _ = solver.propagate();
    }
    // Converge the incremental state over its pending touched rows only
    // (never a full sweep).
    solver.implied_tighten_streak.fill(0);
    for _ in 0..64 {
        if solver.touched_rows.is_empty() {
            break;
        }
        let _ = solver.compute_implied_bounds();
    }
    let full_sweeps = solver.stats.implied_full_sweeps;
    let incremental = snapshot(&solver);
    let rederived = full_rederive(&mut solver);
    assert_eq!(
        incremental.len(),
        rederived.len(),
        "seed {seed}: slot count differs"
    );
    // (1) No coverage loss: incremental at least as tight as from scratch.
    for (vi, (inc, full)) in incremental.iter().zip(rederived.iter()).enumerate() {
        assert!(
            at_least_as_tight(&inc.0, &full.0, false),
            "seed {seed} (checks {checks}): lower bound of var {vi} looser incrementally \
             ({:?}) than re-derived from scratch ({:?})",
            inc.0,
            full.0
        );
        assert!(
            at_least_as_tight(&inc.1, &full.1, true),
            "seed {seed} (checks {checks}): upper bound of var {vi} looser incrementally \
             ({:?}) than re-derived from scratch ({:?})",
            inc.1,
            full.1
        );
    }
    // (2) Soundness: each incremental bound is entailed by the direct bounds.
    for (vi, (lb, ub)) in incremental.iter().enumerate() {
        if let Some((value, strict)) = lb {
            assert_bound_entailed(&mut solver, vi as u32, value, *strict, false, seed);
        }
        if let Some((value, strict)) = ub {
            assert_bound_entailed(&mut solver, vi as u32, value, *strict, true, seed);
        }
    }
    assert!(
        full_sweeps <= 1,
        "seed {seed}: pops must not force full sweeps (saw {full_sweeps})"
    );
}

/// `a` is at least as tight as `b` (a missing `b` is trivially matched).
fn at_least_as_tight(
    a: &Option<(Rational, bool)>,
    b: &Option<(Rational, bool)>,
    is_upper: bool,
) -> bool {
    match (a, b) {
        (_, None) => true,
        (None, Some(_)) => false,
        (Some((av, a_strict)), Some((bv, b_strict))) => {
            LraSolver::bound_at_least_as_tight(av, *a_strict, bv, *b_strict, is_upper)
        }
    }
}

/// Exact oracle: asserting the opposite of the bound must make the current
/// tableau (direct bounds and rows) infeasible.
fn assert_bound_entailed(
    solver: &mut LraSolver,
    var: u32,
    value: &Rational,
    strict: bool,
    is_upper: bool,
    seed: u64,
) {
    solver.push();
    // Opposite of `var <= value` is `var > value` (strict when the bound is
    // not, and vice versa); mirror for lower bounds.
    let (opposite, opposite_strict) = if is_upper {
        (BoundType::Lower, !strict)
    } else {
        (BoundType::Upper, !strict)
    };
    solver.assert_var_bound(
        var,
        value.clone(),
        opposite,
        opposite_strict,
        TermId::SENTINEL,
        true,
        Rational::one(),
    );
    let verdict = solver.check();
    solver.pop();
    assert!(
        matches!(
            verdict,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "seed {seed}: stored {} bound {}{} on var {var} is not entailed by the direct bounds \
         (opposite bound leaves the tableau {verdict:?})",
        if is_upper { "upper" } else { "lower" },
        if strict { "strict " } else { "" },
        value
    );
}

#[test]
fn dirty_row_implied_bounds_cover_full_rederivation_after_random_history() {
    for seed in 1..=40u64 {
        run_trial(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    }
}

/// A pop must keep row-derived bounds that were derived at a scope that is
/// still open (they are trailed and valid), drop only stale direct overlays
/// of the restored variables, and touch only their rows.
#[test]
fn pop_keeps_outer_scope_derived_bounds_and_touches_only_changed_rows() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let sum_xy = terms.mk_add(vec![x, y]);
    let sum_xy_le_10 = terms.mk_le(sum_xy, ten);
    let y_ge_1 = terms.mk_ge(y, one);
    let x_le_2 = terms.mk_le(x, two);
    let z_ge_1 = terms.mk_ge(z, one);
    let z_le_2 = terms.mk_le(z, two);

    let mut solver = LraSolver::new(&terms);
    for atom in [sum_xy_le_10, y_ge_1, x_le_2, z_ge_1, z_le_2] {
        solver.register_atom(atom);
    }
    // Outer scope: x + y <= 10, y >= 1  ==>  derived x <= 9.
    solver.assert_literal(sum_xy_le_10, true);
    solver.assert_literal(y_ge_1, true);
    assert!(is_sat_like(&solver.check()));
    let _ = solver.propagate();
    let xv = *solver.term_to_var.get(&x).expect("x interned") as usize;
    let zv = *solver.term_to_var.get(&z).expect("z interned") as usize;
    let x_ub_outer = solver.implied_bounds[xv]
        .1
        .clone()
        .expect("x <= 9 derived at the outer scope");
    assert_eq!(x_ub_outer.value, Rational::from(9i32));
    assert_ne!(x_ub_outer.row_idx, usize::MAX, "row-derived");

    // Inner scope: a direct bound on an unrelated variable z only.
    solver.push();
    solver.assert_literal(z_ge_1, true);
    assert!(is_sat_like(&solver.check()));
    let _ = solver.propagate();
    assert!(solver.implied_bounds[zv].0.is_some(), "z >= 1 overlaid");
    let rows_before = solver.rows.len();
    solver.pop();

    // The outer-scope derived bound on x survives the pop untouched ...
    let x_ub_after = solver.implied_bounds[xv]
        .1
        .as_ref()
        .expect("outer-scope derived bound must survive the pop");
    assert_eq!(x_ub_after.value, Rational::from(9i32));
    // ... the stale direct overlay of z is gone ...
    assert!(
        solver.implied_bounds[zv].0.is_none(),
        "popped direct bound must not linger in the overlay"
    );
    // ... and the next check neither sweeps every row nor re-analyzes the
    // one row (x + y): none of its variables changed, so it is
    // generation-skipped even though it is still pending from the outer
    // cascade.
    assert_eq!(solver.rows.len(), rows_before);
    let sweeps_before = solver.stats.implied_full_sweeps;
    let analyzed_before = solver.stats.implied_rows_analyzed;
    assert!(is_sat_like(&solver.check()));
    let _ = solver.propagate();
    assert_eq!(
        solver.stats.implied_full_sweeps, sweeps_before,
        "a pop must not force a full sweep"
    );
    assert_eq!(
        solver.stats.implied_rows_analyzed, analyzed_before,
        "a row none of whose variables changed must not be re-analyzed after a pop"
    );
    assert_eq!(
        solver.implied_bounds[xv]
            .1
            .as_ref()
            .map(|b| b.value.clone()),
        Some(Rational::from(9i32))
    );
}
