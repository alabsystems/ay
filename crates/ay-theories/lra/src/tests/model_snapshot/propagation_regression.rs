// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::ColEntry;

/// Regression test for the `last_simplex_feasible` simplex-skip guard (#6256).
///
/// When the simplex returns Unsat and no new bounds are asserted, the
/// simplex-skip optimization must NOT return Sat. The `last_simplex_feasible`
/// flag prevents this: when false, the skip path returns Unknown instead.
///
/// Without this guard, the simplex-skip would see `need_simplex == false`
/// (no bounds tightened, no new rows) and return Sat — a false positive.
#[test]
fn test_simplex_skip_after_unsat_does_not_return_sat_6256() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // Contradictory: x >= 10 and x <= 5
    let ge_ten = terms.mk_ge(x, ten);
    let le_five = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_ten, true); // x >= 10
    solver.assert_literal(le_five, true); // x <= 5

    // First check: simplex detects infeasibility.
    let result1 = solver.check();
    assert!(
        matches!(
            result1,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "First check() should detect UNSAT for (x>=10, x<=5), got {result1:?}"
    );

    // Second check without any new assertions.
    // The simplex-skip sees need_simplex=false (no bounds tightened, no new rows).
    // Without last_simplex_feasible guard, this would return Sat (false positive).
    let result2 = solver.check();
    assert!(
        !matches!(result2, TheoryResult::Sat),
        "Second check() after UNSAT must NOT return Sat when no new bounds asserted. \
         Got {result2:?}. Bug: last_simplex_feasible guard not preventing false-SAT \
         on simplex-skip path (#6256)."
    );
}

/// Regression test: after check() returns Unsat, a subsequent check() without
/// new assertions must NOT return Sat — even through the simplex-skip path.
/// This tests the same invariant as test_simplex_skip_after_unsat_does_not_return_sat_6256
/// but uses a problem requiring the simplex (not just bound precheck) to detect
/// the infeasibility.
///
/// Pattern A from P2:142 strategic audit: the dirty flag and
/// last_simplex_feasible guard must work together to prevent false-SAT on
/// repeated check() calls without assert_literal().
#[test]
fn test_simplex_skip_after_infeasible_requires_pivots_6259() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x + y <= 5, x >= 10, y >= 0 — infeasible (x+y >= 10, but x+y <= 5)
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_5 = terms.mk_le(sum, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_5);
    solver.register_atom(x_ge_10);
    solver.register_atom(y_ge_0);
    solver.assert_literal(sum_le_5, true);
    solver.assert_literal(x_ge_10, true);
    solver.assert_literal(y_ge_0, true);

    // First check: should detect infeasibility.
    let result1 = solver.check();
    assert!(
        !matches!(result1, TheoryResult::Sat),
        "First check() should detect infeasibility (x+y<=5, x>=10, y>=0), got {result1:?}"
    );

    // Second check without any new assertions.
    // Tests that the last_simplex_feasible guard and dirty flag prevent false-SAT.
    let result2 = solver.check();
    assert!(
        !matches!(result2, TheoryResult::Sat),
        "Second check() after infeasible state must NOT return Sat. \
         Got {result2:?}. Bug: dirty flag cleared after non-Sat result, !dirty \
         early return produces false-SAT without assert_literal()."
    );

    // Third check — same pattern, verifying stability.
    let result3 = solver.check();
    assert!(
        !matches!(result3, TheoryResult::Sat),
        "Third check() after infeasible state must NOT return Sat. Got {result3:?}."
    );
}

#[test]
fn test_compute_implied_bounds_keeps_fully_assigned_refinement_rows() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(y_ge_0);
    solver.register_atom(y_le_0);
    solver.register_atom(sum_le_3);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(sum_le_3, true);

    assert!(
        solver.unassigned_atom_count.iter().all(|&count| count == 0),
        "all atoms are assigned; this regression specifically targets the fully-assigned row case"
    );

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after fixing y = 0 and asserting x + y <= 3, got {result:?}"
    );

    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    let (lb, ub) = &solver.implied_bounds[x_var as usize];
    assert!(
        lb.is_none(),
        "x + y <= 3 with y = 0 must not derive a lower bound on x, got {lb:?}; row0={:?}; slack_bounds=({:?}, {:?}); x_status={:?}",
        solver.rows.first(),
        solver.vars[solver.rows[0].basic_var as usize]
            .lower
            .as_ref()
            .map(|b| (&b.value, b.strict)),
        solver.vars[solver.rows[0].basic_var as usize]
            .upper
            .as_ref()
            .map(|b| (&b.value, b.strict)),
        solver.vars[x_var as usize].status
    );
    let derived_upper = ub
        .as_ref()
        .is_some_and(|b| !b.strict && b.value.to_big() == BigRational::from(BigInt::from(3)));
    assert!(
        derived_upper,
        "fully-assigned rows must derive the upper bound x <= 3 (via row or eager derivation), got {ub:?}"
    );
}

#[test]
fn test_check_queues_bound_refinement_for_fully_assigned_row_without_x_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(y_ge_0);
    solver.register_atom(y_le_0);
    solver.register_atom(sum_le_3);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(sum_le_3, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after fixing y = 0 and asserting x + y <= 3, got {result:?}"
    );

    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    let (lb_dbg, ub_dbg) = &solver.implied_bounds[x_var as usize];
    assert!(
        lb_dbg.is_none(),
        "x + y <= 3 with y = 0 must not derive a lower bound on x, got {lb_dbg:?}; row0={:?}; slack_bounds=({:?}, {:?}); x_status={:?}",
        solver.rows.first(),
        solver.vars[solver.rows[0].basic_var as usize]
            .lower
            .as_ref()
            .map(|b| (&b.value, b.strict)),
        solver.vars[solver.rows[0].basic_var as usize]
            .upper
            .as_ref()
            .map(|b| (&b.value, b.strict)),
        solver.vars[x_var as usize].status
    );
    // The upper bound on x is derived via compute_implied_bounds (#6617).
    // The old inline eager_row_bound_derivation path was removed; bound
    // writing is now exclusively via the batch path after simplex.
    let has_upper = ub_dbg
        .as_ref()
        .is_some_and(|b| !b.strict && b.value.to_big() == three_value)
        || solver.vars[x_var as usize]
            .upper
            .as_ref()
            .is_some_and(|b| !b.strict && b.value == three_value);
    assert!(
        has_upper,
        "x should have upper bound <= 3 (via implied or eager derivation), got implied_ub={ub_dbg:?}, direct_ub={:?}",
        solver.vars[x_var as usize].upper.as_ref().map(|b| &b.value)
    );
    assert!(
        solver.propagation_dirty_vars.contains(&x_var),
        "derived bound should mark x dirty for propagation/refinement"
    );

    // #9031: Bound refinements are disabled for soundness. The implied upper
    // bound x <= 3 is derived via compute_implied_bounds and stored in
    // self.implied_bounds[x_var]. The has_upper assertion above already
    // validates this. Verify the implied bound is sufficient — no refinement
    // or direct bound is expected.
    //
    // The implied bound enables propagation of x-related atoms when they exist
    // (via compute_bound_propagations_for_vars in the propagation pipeline).
}

#[test]
fn test_lra_registered_x_atom_gets_propagated_from_fully_assigned_row_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let x_le_3 = terms.mk_le(x, three);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(y_ge_0);
    solver.register_atom(y_le_0);
    solver.register_atom(x_le_3);
    solver.register_atom(sum_le_3);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(sum_le_3, true);

    let result = solver.check();
    assert!(
        is_sat_like(&result),
        "expected SAT-like result after fixing y = 0 and asserting x + y <= 3, got {result:?}"
    );
    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let pending_x = solver
        .pending_propagations
        .iter()
        .find(|pending| pending.propagation.literal == TheoryLit::new(x_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "expected pending propagation for x <= 3 after check(), got {:?}",
                solver.pending_propagations
            )
        });
    // With lazy/deferred materialization, the reason may be:
    // (a) eagerly populated (direct bound) — reason non-empty
    // (b) deferred via DeferredReason — reason empty, deferred is Some
    // (c) lazy via reason_data u64 — reason empty, reason_data is Some, deferred is None
    // All three are valid.
    if pending_x.propagation.reason.is_empty() {
        if pending_x.propagation.is_lazy() {
            // #8467: Lazy justification — reason_data encodes the bound info.
            let reason_data = pending_x
                .propagation
                .reason_data
                .expect("lazy propagation must have reason_data");
            // Verify it's a valid encoding (bit 63 set = interval encoding)
            assert!(reason_data != 0, "reason_data must be non-zero");
        } else {
            let deferred = pending_x
                .deferred
                .expect("empty-reason propagation should carry a deferred reason token");
            match deferred {
                DeferredReason::ImpliedRow {
                    var,
                    need_upper,
                    fallback_row_idx,
                } => {
                    assert_eq!(var, x_var, "deferred token must target x's implied bound");
                    assert!(
                        need_upper,
                        "x <= 3 should defer the implied upper-bound explanation"
                    );
                    assert!(
                        fallback_row_idx.is_some(),
                        "deferred implied propagation should preserve a single-row fallback"
                    );
                }
                DeferredReason::DirectBound { var, need_upper } => {
                    assert_eq!(var, x_var, "deferred token must target x's implied bound");
                    assert!(
                        need_upper,
                        "x <= 3 should defer the implied upper-bound explanation"
                    );
                }
                DeferredReason::ImpliedBound { var, need_upper } => {
                    assert_eq!(var, x_var, "deferred token must target x's implied bound");
                    assert!(
                        need_upper,
                        "x <= 3 should defer the implied upper-bound explanation"
                    );
                }
                DeferredReason::Interval { .. } => {
                    panic!("expected ImpliedRow, DirectBound, or ImpliedBound, got Interval");
                }
            }
        }
    }

    let propagations = solver.propagate();
    let propagated_x = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(x_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "expected x <= 3 to be propagated from the row-derived bound, got {propagations:?}"
            )
        });
    // #8467: DirectBound propagations are now lazy. Materialize for validation.
    let reason = if propagated_x.is_lazy() {
        let reason_data = propagated_x
            .reason_data
            .expect("lazy prop must have reason_data");
        solver
            .explain_propagation(propagated_x.literal.term, reason_data)
            .expect("explain_propagation must succeed for valid lazy prop")
    } else {
        propagated_x.reason.clone()
    };
    assert!(
        !reason.is_empty(),
        "row-derived propagation for x <= 3 must carry a non-empty reason"
    );
    assert!(
        reason
            .iter()
            .all(|lit| solver.asserted.get(&lit.term) == Some(&lit.value)),
        "propagation reasons must reference asserted literals, got {reason:?}"
    );
    assert!(
        solver.propagated_atoms.contains(&(x_le_3, true)),
        "successful propagate() should mark the literal as propagated"
    );
    assert!(
        solver.take_bound_refinements().is_empty(),
        "registered x <= 3 atom should be propagated, not queued as a fresh refinement"
    );
}

#[test]
fn test_collect_statistics_tracks_eager_and_deferred_reasons_issue_6617() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let neg_one = terms.mk_rational(BigRational::from(BigInt::from(-1)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let x_le_3 = terms.mk_le(x, three);
    let z_ge_0 = terms.mk_ge(z, zero);
    let z_ge_neg_one = terms.mk_ge(z, neg_one);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    for atom in [y_ge_0, y_le_0, x_le_3, z_ge_0, z_ge_neg_one, sum_le_3] {
        solver.register_atom(atom);
    }

    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(sum_le_3, true);
    solver.assert_literal(z_ge_0, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT before draining propagations, got {result:?}"
    );

    let propagations = solver.propagate();
    assert!(
        propagations
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(x_le_3, true)),
        "expected deferred row-backed propagation for x <= 3, got {propagations:?}"
    );
    assert!(
        propagations
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(z_ge_neg_one, true)),
        "expected eager direct-bound propagation for z >= -1, got {propagations:?}"
    );

    // #8467: DirectBound propagations are now lazy — reason_data is set but
    // reason Vec is empty. Materialize via explain_propagation to verify the
    // full round-trip works.
    let lazy_count = propagations.iter().filter(|p| p.is_lazy()).count();
    for prop in &propagations {
        if prop.is_lazy() {
            let reason_data = prop.reason_data.expect("lazy must have reason_data");
            let reason = solver
                .explain_propagation(prop.literal.term, reason_data)
                .expect("explain_propagation must succeed for valid lazy prop");
            assert!(
                !reason.is_empty(),
                "explain_propagation must return non-empty reason"
            );
        }
    }
    let stats: HashMap<_, _> = TheorySolver::collect_statistics(&solver)
        .into_iter()
        .collect();
    // #8511: With eager materialization in all drain paths, count includes
    // emitted_direct, emitted_implied, deferred, eager, and lazy_count.
    let deferred = stats.get("lra_reasons_deferred").copied().unwrap_or(0);
    let eager = stats.get("lra_reasons_eager").copied().unwrap_or(0);
    let direct = stats
        .get("lra_reasons_deferred_direct")
        .copied()
        .unwrap_or(0);
    let emitted_direct = stats.get("lra_emitted_direct").copied().unwrap_or(0);
    let emitted_implied = stats.get("lra_emitted_implied").copied().unwrap_or(0);
    let total = deferred + eager + direct + emitted_direct + emitted_implied + lazy_count as u64;
    assert!(
        total >= 2,
        "expected at least 2 total reason materializations (deferred={deferred}, eager={eager}, direct={direct}, emitted_direct={emitted_direct}, emitted_implied={emitted_implied}, lazy_explained={lazy_count})"
    );
}

#[test]
fn test_propagate_runs_touched_row_batch_with_single_row_issue_6617() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());

    let x0 = terms.mk_var("x0", Sort::Real);
    let s0 = terms.mk_var("s0", Sort::Real);

    let slack_lb = terms.mk_ge(s0, zero);
    let x0_le_3 = terms.mk_le(x0, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x0_le_3);

    let x_var = solver.ensure_var_registered(x0);
    let slack_var = solver.ensure_var_registered(s0);
    let max_var = x_var.max(slack_var) as usize;
    solver.vars = (0..=max_var).map(|_| VarInfo::default()).collect();
    solver.rows.clear();
    solver.col_index = vec![Vec::new(); max_var + 1];
    solver.basic_var_to_row.clear();
    solver.touched_rows.clear();
    solver.propagation_dirty_vars.clear();
    solver.pending_propagations.clear();

    solver.vars[x_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: None,
        upper: None,
        status: Some(VarStatus::NonBasic),
    };
    solver.vars[slack_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: Some(Bound::new(
            BigRational::zero().into(),
            vec![slack_lb],
            vec![true],
            vec![Rational::one()],
            false,
        )),
        upper: None,
        status: Some(VarStatus::Basic(0)),
    };
    solver.asserted.insert(slack_lb, true);
    solver.rows.push(TableauRow::new(
        slack_var,
        vec![(x_var, BigRational::from(BigInt::from(-1)))],
        three_value,
    ));
    solver.col_index[x_var as usize].push(ColEntry::new(0, 0));
    solver.basic_var_to_row.insert(slack_var, 0);
    solver.touched_rows.insert(0);
    solver.propagate_direct_touched_rows_pending = true;

    solver.last_simplex_feasible = true;

    let propagations = solver.propagate();
    let propagated_x0 = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(x0_le_3, true))
        .unwrap_or_else(|| {
            panic!("expected propagate() to batch touched rows into x0 <= 3, got {propagations:?}")
        });
    // #8467: With lazy justification, propagation may have either eager reasons
    // (reason non-empty) or lazy reason_data (reason empty, reason_data set).
    assert!(
        !propagated_x0.reason.is_empty() || propagated_x0.is_lazy(),
        "propagate-time touched-row derivation must carry a non-empty reason or lazy reason_data"
    );
    let x0_upper = solver.implied_bounds[x_var as usize]
        .1
        .as_ref()
        .expect("propagate() should materialize the row-derived x0 <= 3 bound");
    assert_eq!(x0_upper.value, Rational::from(3i32));
    assert!(
        !solver.propagate_direct_touched_rows_pending,
        "propagate() should consume the fresh direct-touch batch flag"
    );
}

/// #6617 / #8422: propagate() now runs a fixpoint loop over touched rows,
/// processing cascade rows during propagation rather than deferring them
/// to check(). After the first propagate(), touched_rows should be drained
/// (empty or contain only newly-seeded cascade rows from the fixpoint).
/// The second propagate() should produce no new propagations since all
/// cascade rows were already processed.
#[test]
fn test_propagate_processes_cascade_rows_via_fixpoint_issue_6617() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());

    let x0 = terms.mk_var("x0", Sort::Real);
    let s0 = terms.mk_var("s0", Sort::Real);

    let slack_lb = terms.mk_ge(s0, zero);
    let x0_le_3 = terms.mk_le(x0, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x0_le_3);

    let x_var = solver.ensure_var_registered(x0);
    let slack_var = solver.ensure_var_registered(s0);
    let max_var = x_var.max(slack_var) as usize;
    solver.vars = (0..=max_var).map(|_| VarInfo::default()).collect();
    solver.rows.clear();
    solver.col_index = vec![Vec::new(); max_var + 1];
    solver.basic_var_to_row.clear();
    solver.touched_rows.clear();
    solver.propagation_dirty_vars.clear();
    solver.pending_propagations.clear();

    solver.vars[x_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: None,
        upper: None,
        status: Some(VarStatus::NonBasic),
    };
    solver.vars[slack_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: Some(Bound::new(
            BigRational::zero().into(),
            vec![slack_lb],
            vec![true],
            vec![Rational::one()],
            false,
        )),
        upper: None,
        status: Some(VarStatus::Basic(0)),
    };
    solver.asserted.insert(slack_lb, true);
    solver.rows.push(TableauRow::new(
        slack_var,
        vec![(x_var, BigRational::from(BigInt::from(-1)))],
        three_value,
    ));
    solver.col_index[x_var as usize].push(ColEntry::new(0, 0));
    solver.basic_var_to_row.insert(slack_var, 0);
    solver.touched_rows.insert(0);
    solver.propagate_direct_touched_rows_pending = true;
    solver.last_simplex_feasible = true;

    let first = solver.propagate();
    assert!(
        first
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(x0_le_3, true)),
        "first propagate() should materialize x0 <= 3 from the fresh direct-touch row batch"
    );
    // #8422: propagate() now runs a fixpoint loop that processes cascade rows.
    // The direct-touch flag should be consumed.
    assert!(
        !solver.propagate_direct_touched_rows_pending,
        "propagate() should consume the fresh direct-touch batch flag"
    );

    let second = solver.propagate();
    assert!(
        second.is_empty(),
        "second propagate() should not produce new propagations (cascade already processed)"
    );
}

#[test]
fn test_check_during_propagate_interleaves_bound_cascade_issue_7719() {
    let mut terms = TermStore::new();
    let five_value = BigRational::from(BigInt::from(5));
    let five = terms.mk_rational(five_value.clone());

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);

    let x_le_y = terms.mk_le(x, y);
    let y_le_z = terms.mk_le(y, z);
    let x_ge_5 = terms.mk_ge(x, five);
    let five_again = terms.mk_rational(five_value.clone());
    let z_ge_5 = terms.mk_ge(z, five_again);

    let mut solver = LraSolver::new(&terms);
    for atom in [x_le_y, y_le_z, x_ge_5, z_ge_5] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_le_y, true);
    solver.assert_literal(y_le_z, true);
    solver.assert_literal(x_ge_5, true);

    let result = solver.check_during_propagate();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x <= y <= z with x >= 5 should remain SAT during BCP, got {result:?}"
    );

    let z_var = *solver.term_to_var.get(&z).expect("z should be interned");
    let z_lower = solver.implied_bounds[z_var as usize]
        .0
        .as_ref()
        .expect("interleaved atom processing must derive z >= 5 in the same batched BCP check");
    assert_eq!(
        z_lower.value, five_value,
        "x <= y <= z and x >= 5 must imply z >= 5 during the same check"
    );
    assert!(
        solver.propagation_dirty_vars.contains(&z_var),
        "derived z bound should be marked dirty for propagation"
    );

    let propagations = solver.propagate();
    assert!(
        propagations
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(z_ge_5, true)),
        "derived z >= 5 bound should reach propagate(); got {propagations:?}"
    );
}

#[test]
fn test_capped_implied_bound_cascade_stays_pending_issue_8422() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let bound = |value: i64, reason: u32| {
        Bound::new(
            BigRational::from(BigInt::from(value)).into(),
            vec![TermId::new(reason)],
            vec![true],
            vec![Rational::one()],
            false,
        )
    };

    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(0, 1000)),
            upper: None,
            status: Some(VarStatus::Basic(0)),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(5, 1001)),
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(0, 1002)),
            upper: None,
            status: Some(VarStatus::Basic(1)),
        },
    ];

    // Row 0 derives y >= 5 from s0 >= 0 and x >= 5.
    // Row 1 can then derive z >= 5, but the throttled inner cascade plus
    // zero outer rounds force that second hop into the continuation path.
    solver.rows = vec![
        TableauRow::new(
            0,
            vec![
                (1, BigRational::from(BigInt::from(-1))),
                (2, BigRational::from(BigInt::from(1))),
            ],
            BigRational::zero(),
        ),
        TableauRow::new(
            4,
            vec![
                (2, BigRational::from(BigInt::from(-1))),
                (3, BigRational::from(BigInt::from(1))),
            ],
            BigRational::zero(),
        ),
    ];
    solver.col_index = vec![Vec::new(); 5];
    solver.col_index[1].push(ColEntry::new(0, 0));
    solver.col_index[2].extend([ColEntry::new(0, 1), ColEntry::new(1, 0)]);
    solver.col_index[3].push(ColEntry::new(1, 1));
    solver.basic_var_to_row.insert(0, 0);
    solver.basic_var_to_row.insert(4, 1);
    solver.touched_rows.extend([0, 1]);
    solver.propagate_direct_touched_rows_pending = true;
    solver.max_fixpoint_rounds = Some(0);
    solver.bcp_cascade_dry_streak = 3;

    solver.run_post_simplex_propagation(false, false, true);

    assert!(
        solver.implied_bounds[2].0.is_some(),
        "first capped pass should derive y >= 5"
    );
    assert!(
        solver.implied_bounds[3].0.is_none(),
        "z >= 5 should require the queued continuation hop"
    );
    assert!(
        solver.propagate_direct_touched_rows_pending,
        "capped fixpoint must keep the touched-row continuation flag set"
    );
    assert!(
        solver.has_pending_analysis(),
        "extension layer must see capped cascade rows even after direct-bound flags clear"
    );

    solver.max_fixpoint_rounds = Some(4);
    solver.bcp_cascade_dry_streak = 0;
    solver.run_post_simplex_propagation(false, false, true);

    let z_lower = solver.implied_bounds[3]
        .0
        .as_ref()
        .expect("continuation pass should derive z >= 5");
    assert_eq!(z_lower.value, Rational::from(5i32));
    assert!(
        !solver.propagate_direct_touched_rows_pending,
        "converged continuation should clear the touched-row flag"
    );
}

/// Verify that propagate() refreshes simplex feasibility before running
/// touched-row analysis (#6987). When `bounds_tightened_since_simplex` is
/// true, propagate() must call dual_simplex() to update the basis before
/// compute_implied_bounds(). Without this refresh, row analysis runs
/// against a stale basis and may miss pivot-created opportunities.
///
/// Z3 reference: theory_lra.cpp:2254 — make_feasible() inside propagate_core().
#[test]
fn test_propagate_refreshes_simplex_before_touched_row_batch_issue_6987() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());

    let x0 = terms.mk_var("x0", Sort::Real);
    let s0 = terms.mk_var("s0", Sort::Real);

    let slack_lb = terms.mk_ge(s0, zero);
    let x0_le_3 = terms.mk_le(x0, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x0_le_3);

    let x_var = solver.ensure_var_registered(x0);
    let slack_var = solver.ensure_var_registered(s0);
    let max_var = x_var.max(slack_var) as usize;
    solver.vars = (0..=max_var).map(|_| VarInfo::default()).collect();
    solver.rows.clear();
    solver.col_index = vec![Vec::new(); max_var + 1];
    solver.basic_var_to_row.clear();
    solver.touched_rows.clear();
    solver.propagation_dirty_vars.clear();
    solver.pending_propagations.clear();

    solver.vars[x_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: None,
        upper: None,
        status: Some(VarStatus::NonBasic),
    };
    solver.vars[slack_var as usize] = VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: Some(Bound::new(
            BigRational::zero().into(),
            vec![slack_lb],
            vec![true],
            vec![Rational::one()],
            false,
        )),
        upper: None,
        status: Some(VarStatus::Basic(0)),
    };
    solver.asserted.insert(slack_lb, true);
    solver.rows.push(TableauRow::new(
        slack_var,
        vec![(x_var, BigRational::from(BigInt::from(-1)))],
        three_value,
    ));
    solver.col_index[x_var as usize].push(ColEntry::new(0, 0));
    solver.basic_var_to_row.insert(slack_var, 0);
    solver.touched_rows.insert(0);
    solver.propagate_direct_touched_rows_pending = true;

    // Key difference from the #6617 test: set bounds_tightened_since_simplex
    // to true, simulating a BCP bound tightening that happened after the last
    // check(). The old code would skip row analysis because it never called
    // dual_simplex() during propagate(). The new code (#6987) calls
    // refresh_simplex_for_propagate() first.
    solver.bounds_tightened_since_simplex = true;
    solver.last_simplex_feasible = true;

    let propagations = solver.propagate();
    // After the simplex refresh, the touched row should derive x0 <= 3.
    let found_x0_le_3 = propagations
        .iter()
        .any(|prop| prop.literal == TheoryLit::new(x0_le_3, true));
    assert!(
        found_x0_le_3,
        "propagate() should derive x0 <= 3 after simplex refresh (#6987), got {propagations:?}"
    );
    // bounds_tightened_since_simplex should be cleared by the refresh.
    assert!(
        !solver.bounds_tightened_since_simplex,
        "refresh_simplex_for_propagate should clear bounds_tightened_since_simplex"
    );
}

#[test]
fn test_register_atom_tracks_compound_wakeups_separately_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y must be interned");
    let slack = *solver
        .expr_to_slack
        .values()
        .next()
        .map(|(slack, _)| slack)
        .expect("compound atom should create exactly one slack variable");

    assert!(
        solver
            .atom_index
            .get(&x_var)
            .is_none_or(|atoms| atoms.iter().all(|atom| atom.term != sum_le_3)),
        "compound atom must not pollute direct-bound index for x"
    );
    assert!(
        solver
            .atom_index
            .get(&y_var)
            .is_none_or(|atoms| atoms.iter().all(|atom| atom.term != sum_le_3)),
        "compound atom must not pollute direct-bound index for y"
    );
    for wake_key in [x_var, y_var, slack] {
        assert!(
            solver
                .compound_use_index
                .get(&wake_key)
                .is_some_and(|atoms| atoms
                    .iter()
                    .any(|entry| { entry.term == sum_le_3 && entry.slack == slack })),
            "compound atom must be queued under wake key {wake_key}"
        );
    }
}

#[test]
fn test_compound_propagation_uses_compound_use_index_without_var_to_atoms_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let x_le_3 = terms.mk_le(x, three);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(y_ge_0);
    solver.register_atom(y_le_0);
    solver.register_atom(x_le_3);
    solver.register_atom(sum_le_3);
    solver.var_to_atoms.clear();

    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(x_le_3, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after fixing y = 0 and asserting x <= 3, got {result:?}"
    );
    assert!(
        solver
            .pending_propagations
            .iter()
            .any(|pending| pending.propagation.literal == TheoryLit::new(sum_le_3, true)),
        "compound wakeup helper should queue x + y <= 3 even when var_to_atoms is empty"
    );

    let propagations = solver.propagate();
    let propagated_sum = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(sum_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "expected x + y <= 3 to be propagated from compound_use_index, got {propagations:?}"
            )
        });
    // #8467: DirectBound propagations are now lazy (reason_data set, reason empty).
    // Call explain_propagation to materialize the reason for validation.
    let reason = if propagated_sum.is_lazy() {
        let reason_data = propagated_sum
            .reason_data
            .expect("lazy prop must have reason_data");
        solver
            .explain_propagation(propagated_sum.literal.term, reason_data)
            .expect("explain_propagation must succeed for valid lazy prop")
    } else {
        propagated_sum.reason.clone()
    };
    assert!(
        !reason.is_empty(),
        "compound propagation must carry a non-empty reason"
    );
}

#[test]
fn test_compound_same_expression_stronger_atom_propagates_weaker_atom_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_1);
    solver.register_atom(sum_le_3);

    solver.assert_literal(sum_le_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after asserting stronger compound atom, got {result:?}"
    );

    let pending = solver
        .pending_propagations
        .iter()
        .find(|pending| pending.propagation.literal == TheoryLit::new(sum_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "same-expression stronger compound atom should eagerly imply the weaker atom, got {:?}",
                solver.pending_propagations
            )
        });
    // #6617 Phase 3: Compound propagations now use DeferredReason::DirectBound,
    // so the pending reason is empty. The deferred token must be present.
    assert!(
        pending.deferred.is_some() || !pending.propagation.reason.is_empty(),
        "compound propagation must carry either a deferred token or an eager reason"
    );

    let propagations = solver.propagate();
    let propagated_sum = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(sum_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "expected x + y <= 3 to propagate from the stronger same-expression atom, got {propagations:?}"
            )
        });
    // #8467: DirectBound propagations are now lazy (reason_data set, reason empty).
    // Call explain_propagation to materialize the reason for validation.
    let reason = if propagated_sum.is_lazy() {
        let reason_data = propagated_sum
            .reason_data
            .expect("lazy prop must have reason_data");
        solver
            .explain_propagation(propagated_sum.literal.term, reason_data)
            .expect("explain_propagation must succeed for valid lazy prop")
    } else {
        propagated_sum.reason.clone()
    };
    assert!(
        !reason.is_empty(),
        "propagate() must produce a non-empty reason for the compound propagation"
    );
    // The reason should contain the asserted atom (sum_le_1 true) as witness.
    assert!(
        reason.iter().any(|lit| lit.term == sum_le_1 && lit.value),
        "propagate() reason should include the stronger asserted atom as witness, got {reason:?}"
    );
}

#[test]
fn test_compute_expr_interval_preserves_open_zero_lower_endpoint_6582() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());

    let x_gt_0 = terms.mk_gt(x, zero);
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.intern_var(x);
    let y_var = solver.intern_var(y);
    solver.assert_var_bound(
        x_var,
        BigRational::zero().into(),
        BoundType::Lower,
        true,
        x_gt_0,
        true,
        Rational::one(),
    );
    solver.assert_var_bound(
        y_var,
        BigRational::zero().into(),
        BoundType::Lower,
        false,
        y_ge_0,
        true,
        Rational::one(),
    );

    let mut expr = LinearExpr::zero();
    expr.add_term(x_var, BigRational::from(BigInt::from(1)));
    expr.add_term(y_var, BigRational::from(BigInt::from(1)));
    let (lb, ub) = solver.compute_expr_interval(&expr);
    let boundary = lb.expect("x > 0 and y >= 0 should produce a finite lower endpoint");
    assert_eq!(
        boundary.value,
        Rational::zero(),
        "strict boundary endpoint should stay at the zero boundary"
    );
    assert!(
        boundary.strict,
        "strictness must be preserved so the zero lower endpoint remains open (#6582)"
    );
    assert!(
        ub.is_none(),
        "no upper bounds were asserted, so x + y should remain unbounded above"
    );
}

#[test]
fn test_compound_interval_open_zero_lower_propagates_false_upper_atom_6582() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());

    let x_gt_0 = terms.mk_gt(x, zero);
    let y_ge_0 = terms.mk_ge(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_0 = terms.mk_le(sum, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_0);
    solver.assert_literal(x_gt_0, true);
    solver.assert_literal(y_ge_0, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x > 0, y >= 0 should stay SAT before propagating x + y <= 0, got {result:?}"
    );

    let propagations = solver.propagate();
    let propagated = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(sum_le_0, false))
        .unwrap_or_else(|| {
            panic!("expected x > 0 and y >= 0 to imply not(x + y <= 0), got {propagations:?}")
        });
    // #8467: With lazy justification, reason may be empty when reason_data is set.
    assert!(
        !propagated.reason.is_empty() || propagated.is_lazy(),
        "strict open-zero contradiction must carry reasons or lazy reason_data"
    );
}

#[test]
fn test_compound_interval_open_zero_upper_propagates_false_lower_atom_6582() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());

    let x_lt_0 = terms.mk_lt(x, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let sum_ge_0 = terms.mk_ge(sum, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_ge_0);
    solver.assert_literal(x_lt_0, true);
    solver.assert_literal(y_le_0, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x < 0, y <= 0 should stay SAT before propagating x + y >= 0, got {result:?}"
    );

    let propagations = solver.propagate();
    let propagated = propagations
        .iter()
        .find(|prop| prop.literal == TheoryLit::new(sum_ge_0, false))
        .unwrap_or_else(|| {
            panic!("expected x < 0 and y <= 0 to imply not(x + y >= 0), got {propagations:?}")
        });
    // #8467: With lazy justification, reason may be empty when reason_data is set.
    assert!(
        !propagated.reason.is_empty() || propagated.is_lazy(),
        "strict open-zero contradiction must carry reasons or lazy reason_data"
    );
}

/// Regression test for #8187: verify the `post_simplex_bounds_added`
/// flag is DEFINED (the split landed) and cleared after a clean Sat.
///
/// Contract (see lib.rs: `post_simplex_bounds_added` docstring):
/// - Every `assert_var_bound[_with_reasons]` setter that actually tightens
///   must raise both `bounds_tightened_since_simplex` (for "need simplex")
///   and `post_simplex_bounds_added` (for the Sat-return soundness gate).
/// - Before #8187, only the former was raised, so direct-bound tightenings
///   that happened inside `run_post_simplex_propagation` after the simplex
///   completion clear were invisible to the Sat-return gate, yielding
///   false-SAT on QF_LRA benchmarks (#8810 / #5534 / #8187).
///
/// This test ensures the field exists and is cleared at simplex completion.
#[test]
fn test_post_simplex_bounds_added_field_cleared_on_sat_issue_8187() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let x_ge_5 = terms.mk_ge(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_5);
    solver.assert_literal(x_ge_5, true);

    // check() triggers process_check_atoms -> assert_var_bound (which
    // raises both flags), then the simplex completion clear resets both.
    let result = solver.check();
    assert!(is_sat_like(&result), "x >= 5 is SAT, got {result:?}");

    // Both flags MUST be cleared after a clean Sat: simplex ran to
    // completion and no post-simplex cascade fired.
    assert!(
        !solver.bounds_tightened_since_simplex,
        "bounds_tightened_since_simplex must clear after simplex completion"
    );
    assert!(
        !solver.post_simplex_bounds_added,
        "post_simplex_bounds_added must clear after simplex completion (#8187)"
    );
}

/// Regression test for #8187: verify the two simplex-flag semantics are
/// independently cleared at their proper sites. Specifically:
///   - `bounds_tightened_since_simplex` is cleared when a simplex actually
///     completes (post-simplex clears in check_impl / BCP / refresh).
///   - `post_simplex_bounds_added` is cleared at each check-entry and at
///     simplex completion.
///
/// Previously these two semantics were conflated in
/// `bounds_tightened_since_simplex`, causing the Sat-return gate to miss
/// post-simplex bound tightenings that happened after a fresh simplex run.
#[test]
fn test_simplex_flag_split_semantics_issue_8187() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_5);
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_5, true);

    // After check() runs simplex to completion, BOTH flags must be cleared.
    let result = solver.check();
    assert!(
        is_sat_like(&result),
        "x in [0, 5] should be SAT, got {result:?}"
    );
    assert!(
        !solver.bounds_tightened_since_simplex,
        "bounds_tightened_since_simplex must be cleared after simplex completion"
    );
    assert!(
        !solver.post_simplex_bounds_added,
        "post_simplex_bounds_added must be cleared after simplex completion"
    );
}

/// Regression for #8810: the !dirty SAT fast path must run the release
/// current-assignment bounds guard, not only the debug assertion. A stale
/// assignment can otherwise return Sat and rely on model validation to catch the
/// bad model downstream.
#[test]
fn test_not_dirty_sat_guard_demotes_stale_assignment_issue_8810() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let x_ge_5 = terms.mk_ge(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_5);
    solver.assert_literal(x_ge_5, true);

    let result = solver.check();
    assert!(is_sat_like(&result), "x >= 5 is SAT, got {result:?}");

    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    solver.vars[x_var as usize].value = InfRational::from_rational(BigRational::zero());
    solver.dirty = false;
    solver.bounds_tightened_since_simplex = false;
    solver.post_simplex_bounds_added = false;
    solver.last_simplex_feasible = true;

    let stale = solver.check();
    assert!(
        matches!(stale, TheoryResult::Unknown),
        "stale assignment x=0 under x>=5 must fail closed to Unknown, got {stale:?}"
    );
    assert!(
        solver.dirty && solver.bounds_tightened_since_simplex && !solver.last_simplex_feasible,
        "guard must force the next check to re-run simplex after stale Sat demotion"
    );
}

/// Regression for #8810: final SAT returns must check the current assignment
/// even when `post_simplex_bounds_added` is false. The original #8187 guard only
/// covered the post-simplex cascade race; this covers any stale-cache path that
/// reaches the final check with freshness flags accidentally clear.
#[test]
fn test_final_sat_guard_demotes_stale_assignment_without_post_flag_issue_8810() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let x_ge_5 = terms.mk_ge(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_5);
    solver.assert_literal(x_ge_5, true);

    let result = solver.check();
    assert!(is_sat_like(&result), "x >= 5 is SAT, got {result:?}");

    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    solver.vars[x_var as usize].value = InfRational::from_rational(BigRational::zero());
    solver.dirty = true;
    solver.bounds_tightened_since_simplex = false;
    solver.post_simplex_bounds_added = false;
    solver.last_simplex_feasible = true;

    let stale = solver.check();
    assert!(
        matches!(stale, TheoryResult::Unknown),
        "final Sat path with stale x=0 under x>=5 must fail closed to Unknown, got {stale:?}"
    );
    assert!(
        solver.dirty && solver.bounds_tightened_since_simplex && !solver.last_simplex_feasible,
        "guard must force the next check to re-run simplex after stale final Sat demotion"
    );
}
