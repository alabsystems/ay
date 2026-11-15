// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Delivered implied-bound propagations must carry exact explanations.
//!
//! These mirror the five synthetic probes (tA..tE) of the QF_LRA-simplex
//! diagnosis (the development design notes,
//! section 3.2): the freshness gate used to re-derive compound-atom
//! entailment from DIRECT bounds of the atom's original variables, so any
//! propagation whose entailment rests on an implied bound (tD's chain, tE's
//! compound atom through `x = z`) was discarded — 100% of them on sc-*.
//! Every test asserts that the propagation is delivered and, independently
//! of the explanation machinery, that its reason literals entail the
//! propagated literal (a fresh solver asserting the reasons plus the
//! negated literal is infeasible).

use super::*;
use ay_core::TheoryPropagation;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// Drain `solver` and return the delivered propagation of `lit`, panicking
/// with the full delivered set when it is missing.
fn expect_delivered(solver: &mut LraSolver, lit: TheoryLit, what: &str) -> TheoryPropagation {
    let propagations = solver.propagate();
    propagations
        .iter()
        .find(|p| p.literal == lit)
        .cloned()
        .unwrap_or_else(|| {
            panic!("expected {what} ({lit:?}) to be delivered, got {propagations:?}")
        })
}

/// Materialize the reason of a delivered propagation exactly as the DPLL
/// layer would at conflict analysis, and check it is a sound justification:
/// non-empty, every literal asserted, and — solved independently — the
/// reasons entail the literal.
fn assert_sound_reason(
    terms: &TermStore,
    solver: &mut LraSolver,
    prop: &TheoryPropagation,
) -> Vec<TheoryLit> {
    let reason = if prop.is_lazy() {
        let reason_data = prop
            .reason_data
            .expect("lazy propagation carries reason_data");
        solver
            .explain_propagation(prop.literal.term, reason_data)
            .unwrap_or_else(|| panic!("explain_propagation must succeed for {:?}", prop.literal))
    } else {
        prop.reason.clone()
    };
    assert!(
        !reason.is_empty(),
        "reason for {:?} must be non-empty",
        prop.literal
    );
    assert!(
        reason
            .iter()
            .all(|r| solver.asserted.get(&r.term) == Some(&r.value)),
        "reason literals must be asserted: {reason:?}"
    );
    assert!(
        !reason.iter().any(|r| r.term == prop.literal.term),
        "reason must not be circular: {reason:?}"
    );
    assert_propagation_entailed(terms, &reason, prop.literal);
    reason
}

/// Independent semantic check: `reason ∧ ¬lit` is infeasible.
fn assert_propagation_entailed(terms: &TermStore, reason: &[TheoryLit], lit: TheoryLit) {
    let mut probe = LraSolver::new(terms);
    for r in reason {
        probe.assert_literal(r.term, r.value);
    }
    probe.assert_literal(lit.term, !lit.value);
    let verdict = probe.check();
    assert!(
        matches!(
            verdict,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "reason {reason:?} does not entail {lit:?}: probe verdict {verdict:?}"
    );
}

fn stat(solver: &LraSolver, name: &str) -> u64 {
    TheorySolver::collect_statistics(solver)
        .into_iter()
        .find(|(n, _)| *n == name)
        .map(|(_, v)| v)
        .unwrap_or(0)
}

/// tA: single-variable atom implied through one row.
/// `x + y <= 1, y >= 1/2, x >= 0` propagates `x <= 7/10`.
#[test]
fn single_var_atom_implied_through_one_row_is_delivered_with_exact_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(rat(1, 1));
    let zero = terms.mk_rational(rat(0, 1));
    let half = terms.mk_rational(rat(1, 2));
    let seven_tenths = terms.mk_rational(rat(7, 10));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one);
    let y_ge_half = terms.mk_ge(y, half);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_7_10 = terms.mk_le(x, seven_tenths);

    let mut solver = LraSolver::new(&terms);
    for atom in [sum_le_1, y_ge_half, x_ge_0, x_le_7_10] {
        solver.register_atom(atom);
    }
    solver.assert_literal(sum_le_1, true);
    solver.assert_literal(y_ge_half, true);
    solver.assert_literal(x_ge_0, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let lit = TheoryLit::new(x_le_7_10, true);
    let prop = expect_delivered(&mut solver, lit, "x <= 7/10");
    let reason = assert_sound_reason(&terms, &mut solver, &prop);
    assert!(
        reason.contains(&TheoryLit::new(sum_le_1, true))
            && reason.contains(&TheoryLit::new(y_ge_half, true)),
        "reason must cite the row bound and y's lower bound, got {reason:?}"
    );
    assert_eq!(stat(&solver, "lra_stale_reason_filtered"), 0);
}

/// tA after the SAT core assigned the propagated literal: the theory has
/// asserted `x <= 7/10`, which is now `x`'s own direct upper bound, so
/// strategy 0 decides the atom with the atom itself. That circular reason is
/// rejected, and returning it ended the search: the SAT core demoted the
/// literal and every conflict analysis through it failed closed (the
/// session-persistent QF_LRA lane livelocked on it). The explanation must
/// fall through to the row.
#[test]
fn lazy_explanation_after_the_atom_is_asserted_does_not_cite_the_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(rat(1, 1));
    let zero = terms.mk_rational(rat(0, 1));
    let half = terms.mk_rational(rat(1, 2));
    let seven_tenths = terms.mk_rational(rat(7, 10));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one);
    let y_ge_half = terms.mk_ge(y, half);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_7_10 = terms.mk_le(x, seven_tenths);

    let mut solver = LraSolver::new(&terms);
    for atom in [sum_le_1, y_ge_half, x_ge_0, x_le_7_10] {
        solver.register_atom(atom);
    }
    solver.assert_literal(sum_le_1, true);
    solver.assert_literal(y_ge_half, true);
    solver.assert_literal(x_ge_0, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let lit = TheoryLit::new(x_le_7_10, true);
    let prop = expect_delivered(&mut solver, lit, "x <= 7/10");
    assert!(
        prop.is_lazy(),
        "the probe needs a lazy implied-bound propagation, got {prop:?}"
    );
    solver.assert_literal(x_le_7_10, true);
    // `assert_literal` only records the literal; the bound is installed by
    // the next check, which the SAT integration runs before any conflict.
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");
    let reason = assert_sound_reason(&terms, &mut solver, &prop);
    assert!(
        reason.contains(&TheoryLit::new(sum_le_1, true))
            && reason.contains(&TheoryLit::new(y_ge_half, true)),
        "the reason must come from the row, got {reason:?}"
    );
}

/// tB: compound atom whose original variables all carry DIRECT bounds.
/// `x >= 1/2, y >= 3/5, x <= 5` decides `x + y <= 1` (false) and
/// `x + y >= 1` (true).
#[test]
fn compound_atom_with_direct_bounds_is_delivered_with_exact_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(rat(1, 1));
    let five = terms.mk_rational(rat(5, 1));
    let half = terms.mk_rational(rat(1, 2));
    let three_fifths = terms.mk_rational(rat(3, 5));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one);
    let sum_ge_1 = terms.mk_ge(sum, one);
    let x_ge_half = terms.mk_ge(x, half);
    let y_ge_3_5 = terms.mk_ge(y, three_fifths);
    let x_le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    for atom in [sum_le_1, sum_ge_1, x_ge_half, y_ge_3_5, x_le_5] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_ge_half, true);
    solver.assert_literal(y_ge_3_5, true);
    solver.assert_literal(x_le_5, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let propagations = solver.propagate();
    for (lit, what) in [
        (TheoryLit::new(sum_le_1, false), "¬(x + y <= 1)"),
        (TheoryLit::new(sum_ge_1, true), "x + y >= 1"),
    ] {
        let prop = propagations
            .iter()
            .find(|p| p.literal == lit)
            .cloned()
            .unwrap_or_else(|| panic!("expected {what} delivered, got {propagations:?}"));
        let reason = assert_sound_reason(&terms, &mut solver, &prop);
        assert!(
            reason.contains(&TheoryLit::new(x_ge_half, true))
                && reason.contains(&TheoryLit::new(y_ge_3_5, true)),
            "reason for {what} must cite both lower bounds, got {reason:?}"
        );
    }
    assert_eq!(stat(&solver, "lra_stale_reason_filtered"), 0);
}

/// tC: an equality fixes `x` through `x = y, y ∈ [1/2, 1/2]`; the atom
/// `x >= 1` is refuted through the equality slack.
#[test]
fn atom_refuted_through_equality_is_delivered_with_exact_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let one = terms.mk_rational(rat(1, 1));
    let half = terms.mk_rational(rat(1, 2));
    let x_eq_y = terms.mk_eq(x, y);
    let y_ge_half = terms.mk_ge(y, half);
    let y_le_half = terms.mk_le(y, half);
    let x_eq_z = terms.mk_eq(x, z);
    let x_ge_1 = terms.mk_ge(x, one);

    let mut solver = LraSolver::new(&terms);
    for atom in [x_eq_y, y_ge_half, y_le_half, x_eq_z, x_ge_1] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_eq_y, true);
    solver.assert_literal(y_ge_half, true);
    solver.assert_literal(y_le_half, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let lit = TheoryLit::new(x_ge_1, false);
    let prop = expect_delivered(&mut solver, lit, "¬(x >= 1)");
    let reason = assert_sound_reason(&terms, &mut solver, &prop);
    assert!(
        reason.contains(&TheoryLit::new(x_eq_y, true))
            && reason.contains(&TheoryLit::new(y_le_half, true)),
        "reason must cite the equality and y's upper bound, got {reason:?}"
    );
    assert_eq!(stat(&solver, "lra_stale_reason_filtered"), 0);
}

/// tD: single-variable atom whose implied bound is a two-step chain:
/// `x + y <= 1, y = z, z >= 1/2, x >= 0` propagates `x <= 7/10` and the
/// reason grounds through `y = z` to `z >= 1/2`.
#[test]
fn single_var_atom_through_two_step_chain_is_delivered_with_exact_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let one = terms.mk_rational(rat(1, 1));
    let zero = terms.mk_rational(rat(0, 1));
    let half = terms.mk_rational(rat(1, 2));
    let seven_tenths = terms.mk_rational(rat(7, 10));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one);
    let y_eq_z = terms.mk_eq(y, z);
    let z_ge_half = terms.mk_ge(z, half);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_7_10 = terms.mk_le(x, seven_tenths);

    let mut solver = LraSolver::new(&terms);
    for atom in [sum_le_1, y_eq_z, z_ge_half, x_ge_0, x_le_7_10] {
        solver.register_atom(atom);
    }
    solver.assert_literal(sum_le_1, true);
    solver.assert_literal(y_eq_z, true);
    solver.assert_literal(z_ge_half, true);
    solver.assert_literal(x_ge_0, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let lit = TheoryLit::new(x_le_7_10, true);
    let prop = expect_delivered(&mut solver, lit, "x <= 7/10");
    let reason = assert_sound_reason(&terms, &mut solver, &prop);
    assert!(
        reason.contains(&TheoryLit::new(sum_le_1, true))
            && reason.contains(&TheoryLit::new(y_eq_z, true))
            && reason.contains(&TheoryLit::new(z_ge_half, true)),
        "reason must ground through the equality chain, got {reason:?}"
    );
    assert_eq!(stat(&solver, "lra_stale_reason_filtered"), 0);
}

/// tE: compound atom whose entailment NEEDS an implied bound on an original
/// variable: `x = z, z >= 1/2, y >= 3/5, z <= 5` decides `x + y <= 1`
/// (false) and `x + y >= 1` (true); `x` has no direct bound at all. This
/// is the sc-* shape the old gate rejected outright.
#[test]
fn compound_atom_needing_implied_bound_is_delivered_with_exact_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let one = terms.mk_rational(rat(1, 1));
    let five = terms.mk_rational(rat(5, 1));
    let half = terms.mk_rational(rat(1, 2));
    let three_fifths = terms.mk_rational(rat(3, 5));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one);
    let sum_ge_1 = terms.mk_ge(sum, one);
    let x_eq_z = terms.mk_eq(x, z);
    let z_ge_half = terms.mk_ge(z, half);
    let y_ge_3_5 = terms.mk_ge(y, three_fifths);
    let z_le_5 = terms.mk_le(z, five);

    let mut solver = LraSolver::new(&terms);
    for atom in [sum_le_1, sum_ge_1, x_eq_z, z_ge_half, y_ge_3_5, z_le_5] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_eq_z, true);
    solver.assert_literal(z_ge_half, true);
    solver.assert_literal(y_ge_3_5, true);
    solver.assert_literal(z_le_5, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let propagations = solver.propagate();
    for (lit, what) in [
        (TheoryLit::new(sum_le_1, false), "¬(x + y <= 1)"),
        (TheoryLit::new(sum_ge_1, true), "x + y >= 1"),
    ] {
        let prop = propagations
            .iter()
            .find(|p| p.literal == lit)
            .cloned()
            .unwrap_or_else(|| panic!("expected {what} delivered, got {propagations:?}"));
        let reason = assert_sound_reason(&terms, &mut solver, &prop);
        assert!(
            reason.contains(&TheoryLit::new(x_eq_z, true))
                && reason.contains(&TheoryLit::new(z_ge_half, true))
                && reason.contains(&TheoryLit::new(y_ge_3_5, true)),
            "reason for {what} must ground x through the equality, got {reason:?}"
        );
        assert!(
            !reason.contains(&TheoryLit::new(z_le_5, true)),
            "z's upper bound is not an antecedent of the lower bound on x + y: {reason:?}"
        );
    }
    assert_eq!(
        stat(&solver, "lra_stale_reason_filtered"),
        0,
        "no propagation may be dropped by the freshness gate"
    );
    assert!(
        stat(&solver, "lra_implied_reason_chain") >= 2,
        "both compound propagations should be explained by the derivation chain"
    );
}

/// tF: pure offset graph with NO direct bounds anywhere (the
/// pointer-family shape): `x = y + 1` asserted with `y` free must still
/// refute `x < y` and decide `x <= y + 1` / `x >= y + 1`, with the
/// equality itself as the entire reason. Every antecedent variable is
/// unbounded, so neither the direct-bounds interval probe nor
/// component-bounded row analysis can fire; only the shared-slack
/// direct bound (the asserted equality bounds the `x - y` slack to 1)
/// or an implied slack bound can deliver these.
#[test]
fn offset_equality_with_free_vars_decides_sibling_atoms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(rat(1, 1));
    let y_plus_1 = terms.mk_add(vec![y, one]);
    let x_eq_y1 = terms.mk_eq(x, y_plus_1);
    let x_lt_y = terms.mk_lt(x, y);
    let x_le_y1 = terms.mk_le(x, y_plus_1);
    let x_ge_y1 = terms.mk_ge(x, y_plus_1);

    let mut solver = LraSolver::new(&terms);
    for atom in [x_eq_y1, x_lt_y, x_le_y1, x_ge_y1] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_eq_y1, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let propagations = solver.propagate();
    for (lit, what) in [
        (TheoryLit::new(x_lt_y, false), "¬(x < y)"),
        (TheoryLit::new(x_le_y1, true), "x <= y + 1"),
        (TheoryLit::new(x_ge_y1, true), "x >= y + 1"),
    ] {
        let prop = propagations
            .iter()
            .find(|p| p.literal == lit)
            .cloned()
            .unwrap_or_else(|| panic!("expected {what} delivered, got {propagations:?}"));
        let reason = assert_sound_reason(&terms, &mut solver, &prop);
        assert!(
            reason.contains(&TheoryLit::new(x_eq_y1, true)),
            "reason for {what} must cite the offset equality, got {reason:?}"
        );
    }
    assert_eq!(stat(&solver, "lra_stale_reason_filtered"), 0);
}

/// tF on the BCP path: the combiner drives the solver through
/// `check_during_propagate` during search, not the full `check()`.
/// The same offset propagations must be queued there too; this is the
/// path the AUFLIA combiner exercises on the pointer family, where
/// delivered propagations measure zero.
#[test]
fn offset_equality_with_free_vars_decides_sibling_atoms_via_bcp_check() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(rat(1, 1));
    let y_plus_1 = terms.mk_add(vec![y, one]);
    let x_eq_y1 = terms.mk_eq(x, y_plus_1);
    let x_lt_y = terms.mk_lt(x, y);
    let x_le_y1 = terms.mk_le(x, y_plus_1);
    let x_ge_y1 = terms.mk_ge(x, y_plus_1);

    let mut solver = LraSolver::new(&terms);
    for atom in [x_eq_y1, x_lt_y, x_le_y1, x_ge_y1] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_eq_y1, true);
    let result = solver.check_during_propagate();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let propagations = solver.propagate();
    for (lit, what) in [
        (TheoryLit::new(x_lt_y, false), "¬(x < y)"),
        (TheoryLit::new(x_le_y1, true), "x <= y + 1"),
        (TheoryLit::new(x_ge_y1, true), "x >= y + 1"),
    ] {
        let prop = propagations
            .iter()
            .find(|p| p.literal == lit)
            .cloned()
            .unwrap_or_else(|| panic!("expected {what} delivered, got {propagations:?}"));
        let reason = assert_sound_reason(&terms, &mut solver, &prop);
        assert!(
            reason.contains(&TheoryLit::new(x_eq_y1, true)),
            "reason for {what} must cite the offset equality, got {reason:?}"
        );
    }
    assert_eq!(stat(&solver, "lra_stale_reason_filtered"), 0);
}

/// The chain walker fails closed when an antecedent's current bound is
/// looser than the one the derivation consumed (the pop-restore hole):
/// no reason is produced rather than an unsound one.
#[test]
fn chain_walker_rejects_antecedent_looser_than_consumed() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let zero = terms.mk_rational(rat(0, 1));
    let a_ge_0 = terms.mk_ge(a, zero);

    let mut solver = LraSolver::new(&terms);
    let a_id = solver.ensure_var_registered(a);
    let b_id = solver.ensure_var_registered(b);
    solver
        .implied_bounds
        .resize(solver.vars.len(), (None, None));
    // a's direct lower bound is 0 ...
    solver.vars[a_id as usize].lower = Some(Bound::new(
        Rational::from(0i32),
        vec![a_ge_0],
        vec![true],
        Vec::new(),
        false,
    ));
    solver.asserted.insert(a_ge_0, true);
    // ... but b's stored bound was derived from a >= 5 (since widened).
    solver.implied_bounds[b_id as usize].0 = Some(ImpliedBound {
        value: Rational::from(5i32),
        strict: false,
        row_idx: 0,
        explanation: Some(BoundExplanation {
            contributing_vars: smallvec::smallvec![Antecedent {
                var: a_id,
                used_upper: false,
                strict: false,
                value: Rational::from(5i32),
            }],
        }),
    });
    assert!(
        solver
            .make_eager_implied_propagation_reasons(b_id as usize, false)
            .is_none(),
        "a >= 0 does not ground a bound derived from a >= 5"
    );
    // A strict antecedent is not grounded by an equal non-strict bound ...
    solver.implied_bounds[b_id as usize].0 = Some(ImpliedBound {
        value: Rational::from(0i32),
        strict: true,
        row_idx: 0,
        explanation: Some(BoundExplanation {
            contributing_vars: smallvec::smallvec![Antecedent {
                var: a_id,
                used_upper: false,
                strict: true,
                value: Rational::from(0i32),
            }],
        }),
    });
    assert!(
        solver
            .make_eager_implied_propagation_reasons(b_id as usize, false)
            .is_none(),
        "a >= 0 does not ground a bound derived from a > 0"
    );
    // ... while an equal non-strict antecedent is.
    solver.implied_bounds[b_id as usize].0 = Some(ImpliedBound {
        value: Rational::from(0i32),
        strict: false,
        row_idx: 0,
        explanation: Some(BoundExplanation {
            contributing_vars: smallvec::smallvec![Antecedent {
                var: a_id,
                used_upper: false,
                strict: false,
                value: Rational::from(0i32),
            }],
        }),
    });
    assert_eq!(
        solver.make_eager_implied_propagation_reasons(b_id as usize, false),
        Some(vec![TheoryLit::new(a_ge_0, true)])
    );
}

/// tH: conflict-size counters record emitted core sizes. `x >= 2`
/// with `x <= 1` conflicts; the counters must count the conflict and
/// its literals so core quality is measurable from statistics alone.
#[test]
fn conflict_size_counters_record_core_literals() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(rat(2, 1));
    let one = terms.mk_rational(rat(1, 1));
    let x_ge_2 = terms.mk_ge(x, two);
    let x_le_1 = terms.mk_le(x, one);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_2);
    solver.register_atom(x_le_1);
    assert!(
        stat(&solver, "lra_conflict_lits_max") == 0
            && stat(&solver, "lra_conflict_lits_total") == 0,
        "counters start at zero"
    );
    let _ = solver.assert_literal(x_ge_2, true);
    let _ = solver.assert_literal(x_le_1, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected conflict, got {result:?}"
    );
    let total = stat(&solver, "lra_conflict_lits_total");
    let max = stat(&solver, "lra_conflict_lits_max");
    let conflicts = stat(&solver, "lra_conflicts");
    assert!(conflicts >= 1, "expected >= 1 conflict, got {conflicts}");
    assert!(max >= 1 && max <= total, "max={max} total={total}");
    assert!(total >= conflicts, "total={total} conflicts={conflicts}");
}

/// tF: a variable fixed by its bounds decides its equality atom.
/// `x >= 1/2, x <= 1/2` propagates `(= x 1/2)` true. (Two-argument
/// `distinct` canonicalizes to `Not(=)` in the term store, so it is
/// the same literal at opposite polarity.) Equality atoms are
/// excluded from atom_index, so only the interval candidate path
/// can deliver these.
#[test]
fn fixed_var_equality_atom_is_delivered_with_exact_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let half = terms.mk_rational(rat(1, 2));
    let x_ge_half = terms.mk_ge(x, half);
    let x_le_half = terms.mk_le(x, half);
    let x_eq_half = terms.mk_eq(x, half);

    let mut solver = LraSolver::new(&terms);
    for atom in [x_ge_half, x_le_half, x_eq_half] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_ge_half, true);
    solver.assert_literal(x_le_half, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let propagations = solver.propagate();
    let prop = propagations
        .iter()
        .find(|p| p.literal == TheoryLit::new(x_eq_half, true))
        .cloned()
        .unwrap_or_else(|| panic!("expected x = 1/2 delivered, got {propagations:?}"));
    let reason = assert_sound_reason(&terms, &mut solver, &prop);
    assert!(
        reason.contains(&TheoryLit::new(x_ge_half, true))
            && reason.contains(&TheoryLit::new(x_le_half, true)),
        "reason must cite both fixing bounds, got {reason:?}"
    );
    assert_eq!(stat(&solver, "lra_stale_reason_filtered"), 0);
}

/// tG: bounds excluding the equality value refute the equality atom.
/// `x >= 1` propagates `(= x 1/2)` false (equivalently distinct true).
#[test]
fn excluded_var_equality_atom_is_refuted_with_exact_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(rat(1, 1));
    let half = terms.mk_rational(rat(1, 2));
    let x_ge_1 = terms.mk_ge(x, one);
    let x_eq_half = terms.mk_eq(x, half);

    let mut solver = LraSolver::new(&terms);
    for atom in [x_ge_1, x_eq_half] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_ge_1, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "expected SAT-like, got {result:?}");

    let propagations = solver.propagate();
    let prop = propagations
        .iter()
        .find(|p| p.literal == TheoryLit::new(x_eq_half, false))
        .cloned()
        .unwrap_or_else(|| panic!("expected ¬(x = 1/2) delivered, got {propagations:?}"));
    let reason = assert_sound_reason(&terms, &mut solver, &prop);
    assert!(
        reason.contains(&TheoryLit::new(x_ge_1, true)),
        "reason must cite the excluding bound, got {reason:?}"
    );
    assert_eq!(stat(&solver, "lra_stale_reason_filtered"), 0);
}
