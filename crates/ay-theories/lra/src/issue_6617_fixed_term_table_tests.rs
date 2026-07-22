// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;

fn issue_6617_fixed_term_bound(reason: TermId, value: i64) -> Bound {
    Bound::new(
        BigRational::from(BigInt::from(value)).into(),
        vec![reason],
        vec![true],
        Vec::new(),
        false,
    )
}

fn issue_6617_register_fixed_term_var(
    solver: &mut LraSolver,
    term: TermId,
    value: i64,
    status: VarStatus,
) -> u32 {
    let var = solver.ensure_var_registered(term);
    solver.vars[var as usize].value =
        InfRational::from_rational(BigRational::from(BigInt::from(value)));
    solver.vars[var as usize].status = Some(status);
    var
}

#[test]
fn test_compute_implied_bounds_registers_fixed_term_representatives_issue_6617() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let x_eq_5 = terms.mk_var("x_eq_5", Sort::Bool);
    let y_eq_5 = terms.mk_var("y_eq_5", Sort::Bool);
    let z_eq_5 = terms.mk_var("z_eq_5", Sort::Bool);

    let mut solver = LraSolver::new(&terms);
    let x_var = issue_6617_register_fixed_term_var(&mut solver, x, 5, VarStatus::NonBasic);
    let y_var = issue_6617_register_fixed_term_var(&mut solver, y, 5, VarStatus::NonBasic);
    let z_var = issue_6617_register_fixed_term_var(&mut solver, z, 5, VarStatus::NonBasic);

    solver.vars[x_var as usize].lower = Some(issue_6617_fixed_term_bound(x_eq_5, 5));
    solver.vars[x_var as usize].upper = Some(issue_6617_fixed_term_bound(x_eq_5, 5));
    solver.vars[y_var as usize].lower = Some(issue_6617_fixed_term_bound(y_eq_5, 5));
    solver.vars[y_var as usize].upper = Some(issue_6617_fixed_term_bound(y_eq_5, 5));
    solver.vars[z_var as usize].lower = Some(issue_6617_fixed_term_bound(z_eq_5, 5));
    solver.vars[z_var as usize].upper = Some(issue_6617_fixed_term_bound(z_eq_5, 5));

    let result = solver.compute_implied_bounds();
    assert!(
        result.newly_bounded.is_empty(),
        "direct tight bounds should not manufacture new implied bounds, got {:?}",
        result.newly_bounded
    );
    assert_eq!(
        solver.fixed_term_value_table.len(),
        1,
        "same-value fixed terms should share one representative table entry"
    );
    assert_eq!(
        solver.fixed_term_value_members.len(),
        3,
        "all fixed term-backed vars should be tracked as members"
    );
    assert_eq!(
        solver.pending_fixed_term_equalities.len(),
        2,
        "three equal fixed terms should queue a representative chain, not pairwise duplicates"
    );

    let first_pending = solver.pending_fixed_term_equalities.clone();
    let second_result = solver.compute_implied_bounds();
    assert!(
        second_result.newly_bounded.is_empty(),
        "re-running compute_implied_bounds should stay quiescent, got {:?}",
        second_result.newly_bounded
    );
    assert_eq!(
        solver.pending_fixed_term_equalities, first_pending,
        "re-registering the same fixed terms must not enqueue duplicate representative equalities"
    );
}

#[test]
fn test_check_same_value_fixed_terms_emit_representative_chain_issue_6617() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let five = BigRational::from(BigInt::from(5));

    let x_ge_bound = terms.mk_rational(five.clone());
    let x_ge_5 = terms.mk_ge(x, x_ge_bound);
    let x_le_bound = terms.mk_rational(five.clone());
    let x_le_5 = terms.mk_le(x, x_le_bound);
    let y_ge_bound = terms.mk_rational(five.clone());
    let y_ge_5 = terms.mk_ge(y, y_ge_bound);
    let y_le_bound = terms.mk_rational(five.clone());
    let y_le_5 = terms.mk_le(y, y_le_bound);
    let z_ge_bound = terms.mk_rational(five.clone());
    let z_ge_5 = terms.mk_ge(z, z_ge_bound);
    let z_le_bound = terms.mk_rational(five);
    let z_le_5 = terms.mk_le(z, z_le_bound);

    let mut solver = LraSolver::new(&terms);
    for lit in [x_ge_5, x_le_5, y_ge_5, y_le_5, z_ge_5, z_le_5] {
        solver.assert_literal(lit, true);
    }

    let result = solver.check();
    let eqs = match result {
        TheoryResult::NeedModelEqualities(eqs) => eqs,
        other => panic!("three fixed equal terms should emit NeedModelEqualities, got {other:?}"),
    };

    assert_eq!(
        eqs.len(),
        2,
        "same-value fixed terms should emit a representative chain, not all pairwise equalities"
    );

    let mut seen_xy = false;
    let mut seen_xz = false;
    let mut seen_yz = false;
    for eq in &eqs {
        assert!(
            !eq.reason.is_empty(),
            "fixed-term equality must keep its direct-bound reasons: {eq:?}"
        );
        let pair = if eq.lhs.0 < eq.rhs.0 {
            (eq.lhs, eq.rhs)
        } else {
            (eq.rhs, eq.lhs)
        };
        if pair == (x, y) {
            seen_xy = true;
        } else if pair == (x, z) {
            seen_xz = true;
        } else if pair == (y, z) {
            seen_yz = true;
        } else {
            panic!("unexpected equality pair from representative chain: {pair:?}");
        }
    }

    let pair_count = usize::from(seen_xy) + usize::from(seen_xz) + usize::from(seen_yz);
    assert_eq!(
        pair_count, 2,
        "representative chain should emit exactly two distinct pairs for three same-value terms: {eqs:?}"
    );
}

#[test]
fn test_soft_reset_warm_preserves_fixed_term_model_equality_pairs_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let five = BigRational::from(BigInt::from(5));

    let x_ge_bound = terms.mk_rational(five.clone());
    let x_ge_5 = terms.mk_ge(x, x_ge_bound);
    let x_le_bound = terms.mk_rational(five.clone());
    let x_le_5 = terms.mk_le(x, x_le_bound);
    let y_ge_bound = terms.mk_rational(five.clone());
    let y_ge_5 = terms.mk_ge(y, y_ge_bound);
    let y_le_bound = terms.mk_rational(five.clone());
    let y_le_5 = terms.mk_le(y, y_le_bound);
    let z_ge_bound = terms.mk_rational(five.clone());
    let z_ge_5 = terms.mk_ge(z, z_ge_bound);
    let z_le_bound = terms.mk_rational(five);
    let z_le_5 = terms.mk_le(z, z_le_bound);

    let mut solver = LraSolver::new(&terms);
    for lit in [x_ge_5, x_le_5, y_ge_5, y_le_5, z_ge_5, z_le_5] {
        solver.assert_literal(lit, true);
    }

    let first = solver.check();
    let pairs = match first {
        TheoryResult::NeedModelEqualities(eqs) => eqs
            .into_iter()
            .map(|eq| {
                if eq.lhs.0 < eq.rhs.0 {
                    (eq.lhs, eq.rhs)
                } else {
                    (eq.rhs, eq.lhs)
                }
            })
            .collect::<Vec<_>>(),
        other => {
            panic!("expected first check to request fixed-term model equalities, got {other:?}")
        }
    };
    assert_eq!(
        pairs.len(),
        2,
        "three equal fixed terms should produce a representative chain"
    );
    for pair in &pairs {
        assert!(
            solver.propagated_equality_pairs.contains(pair),
            "first fixed-term request should record the encoded pair {pair:?}"
        );
    }

    solver.soft_reset_warm();
    for pair in &pairs {
        assert!(
            solver.propagated_equality_pairs.contains(pair),
            "soft_reset_warm must preserve already-encoded fixed-term equality pair {pair:?}"
        );
    }

    for lit in [x_ge_5, x_le_5, y_ge_5, y_le_5, z_ge_5, z_le_5] {
        solver.assert_literal(lit, true);
    }

    let second = solver.check();
    assert!(
        matches!(second, TheoryResult::Sat),
        "soft_reset_warm should not re-request the same fixed-term model equality, got {second:?}"
    );
}

#[test]
fn test_structural_snapshot_preserves_model_equality_pairs_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let five = BigRational::from(BigInt::from(5));

    let x_ge_bound = terms.mk_rational(five.clone());
    let x_ge_5 = terms.mk_ge(x, x_ge_bound);
    let x_le_bound = terms.mk_rational(five.clone());
    let x_le_5 = terms.mk_le(x, x_le_bound);
    let y_ge_bound = terms.mk_rational(five.clone());
    let y_ge_5 = terms.mk_ge(y, y_ge_bound);
    let y_le_bound = terms.mk_rational(five.clone());
    let y_le_5 = terms.mk_le(y, y_le_bound);
    let z_ge_bound = terms.mk_rational(five.clone());
    let z_ge_5 = terms.mk_ge(z, z_ge_bound);
    let z_le_bound = terms.mk_rational(five);
    let z_le_5 = terms.mk_le(z, z_le_bound);
    let literals = [x_ge_5, x_le_5, y_ge_5, y_le_5, z_ge_5, z_le_5];

    let mut solver = LraSolver::new(&terms);
    for lit in literals {
        solver.register_atom(lit);
        solver.assert_literal(lit, true);
    }

    let first = solver.check();
    let pairs = match first {
        TheoryResult::NeedModelEqualities(eqs) => eqs
            .into_iter()
            .map(|eq| {
                if eq.lhs.0 < eq.rhs.0 {
                    (eq.lhs, eq.rhs)
                } else {
                    (eq.rhs, eq.lhs)
                }
            })
            .collect::<Vec<_>>(),
        other => {
            panic!("expected first check to request fixed-term model equalities, got {other:?}")
        }
    };
    assert_eq!(pairs.len(), 2);

    let snapshot = solver
        .export_structural_snapshot_inner()
        .expect("registered fixed-term atoms should export an LRA snapshot");
    let mut restored = LraSolver::restore_from_structural_snapshot_inner(&terms, snapshot)
        .expect("snapshot should restore into an LRA solver");
    for pair in &pairs {
        assert!(
            restored.propagated_equality_pairs.contains(pair),
            "snapshot restore must preserve already-requested model equality pair {pair:?}"
        );
    }

    for lit in literals {
        restored.register_atom(lit);
        restored.assert_literal(lit, true);
    }
    let second = restored.check();
    assert!(
        matches!(second, TheoryResult::Sat),
        "snapshot-restored solver should not re-request the same model equalities, got {second:?}"
    );
}

#[test]
fn test_model_value_equalities_suppress_repeated_zero_reason_pairs_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);

    let mut solver = LraSolver::new(&terms);
    solver.set_combined_theory_mode(true);
    issue_6617_register_fixed_term_var(&mut solver, x, 0, VarStatus::NonBasic);
    issue_6617_register_fixed_term_var(&mut solver, y, 0, VarStatus::NonBasic);
    issue_6617_register_fixed_term_var(&mut solver, z, 0, VarStatus::NonBasic);

    let first = solver.discover_model_value_equalities();
    assert_eq!(
        first.len(),
        2,
        "three equal model values should emit an anchor chain of zero-reason guesses"
    );
    assert!(
        first.iter().all(|req| req.reason.is_empty()),
        "model-value equality guesses must remain zero-reason: {first:?}"
    );
    for req in &first {
        let pair = if req.lhs.0 < req.rhs.0 {
            (req.lhs, req.rhs)
        } else {
            (req.rhs, req.lhs)
        };
        assert!(
            solver.propagated_equality_pairs.contains(&pair),
            "first zero-reason request should record pair {pair:?}"
        );
    }

    let second = solver.discover_model_value_equalities();
    assert!(
        second.is_empty(),
        "repeated zero-reason model-value guesses should be suppressed, got {second:?}"
    );
}

#[test]
fn test_model_value_equalities_skip_false_decided_pairs_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let eq_xy = terms.mk_eq(x, y);
    let pair = if x.0 < y.0 { (x, y) } else { (y, x) };

    let mut lra_asserted = LraSolver::new(&terms);
    lra_asserted.set_combined_theory_mode(true);
    issue_6617_register_fixed_term_var(&mut lra_asserted, x, 0, VarStatus::NonBasic);
    issue_6617_register_fixed_term_var(&mut lra_asserted, y, 0, VarStatus::NonBasic);
    lra_asserted.assert_literal(eq_xy, false);

    let from_lra_trail = lra_asserted.discover_model_value_equalities();
    assert!(
        from_lra_trail.is_empty(),
        "zero-reason model equality must not re-propose an LRA-asserted false pair: {from_lra_trail:?}"
    );
    assert!(
        !lra_asserted.propagated_equality_pairs.contains(&pair),
        "false-decided pair should not be recorded as propagated"
    );

    let mut cross_asserted = LraSolver::new(&terms);
    cross_asserted.set_combined_theory_mode(true);
    issue_6617_register_fixed_term_var(&mut cross_asserted, x, 0, VarStatus::NonBasic);
    issue_6617_register_fixed_term_var(&mut cross_asserted, y, 0, VarStatus::NonBasic);
    cross_asserted.record_cross_theory_reasons(&[(eq_xy, false)]);

    let from_cross_trail = cross_asserted.discover_model_value_equalities();
    assert!(
        from_cross_trail.is_empty(),
        "zero-reason model equality must not re-propose a cross-theory asserted false pair: {from_cross_trail:?}"
    );
    assert!(
        !cross_asserted.propagated_equality_pairs.contains(&pair),
        "cross-theory false-decided pair should not be recorded as propagated"
    );
}

#[test]
fn test_compute_implied_bounds_rekeys_fixed_term_representative_issue_6617() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let x_eq_5 = terms.mk_var("x_eq_5", Sort::Bool);
    let x_eq_6 = terms.mk_var("x_eq_6", Sort::Bool);
    let y_eq_5 = terms.mk_var("y_eq_5", Sort::Bool);

    let mut solver = LraSolver::new(&terms);
    let x_var = issue_6617_register_fixed_term_var(&mut solver, x, 5, VarStatus::NonBasic);
    let y_var = issue_6617_register_fixed_term_var(&mut solver, y, 5, VarStatus::NonBasic);

    solver.vars[x_var as usize].lower = Some(issue_6617_fixed_term_bound(x_eq_5, 5));
    solver.vars[x_var as usize].upper = Some(issue_6617_fixed_term_bound(x_eq_5, 5));
    solver.vars[y_var as usize].lower = Some(issue_6617_fixed_term_bound(y_eq_5, 5));
    solver.vars[y_var as usize].upper = Some(issue_6617_fixed_term_bound(y_eq_5, 5));

    let result = solver.compute_implied_bounds();
    assert!(
        result.newly_bounded.is_empty(),
        "unexpected implied bounds on initial pass: {:?}",
        result.newly_bounded
    );
    assert_eq!(
        solver.pending_fixed_term_equalities,
        vec![(y_var, x_var)],
        "second same-value term should initially chain to the first representative"
    );

    solver.vars[x_var as usize].value =
        InfRational::from_rational(BigRational::from(BigInt::from(6)));
    solver.vars[x_var as usize].lower = Some(issue_6617_fixed_term_bound(x_eq_6, 6));
    solver.vars[x_var as usize].upper = Some(issue_6617_fixed_term_bound(x_eq_6, 6));
    // Signal that direct bounds changed (normally set by assert_var_bound).
    solver.direct_bounds_changed_since_implied = true;

    let second_result = solver.compute_implied_bounds();
    assert!(
        second_result.newly_bounded.is_empty(),
        "rekeying a direct fixed term should not derive new implied bounds: {:?}",
        second_result.newly_bounded
    );

    let key_five = (Rational::from(5i64), false);
    let key_six = (Rational::from(6i64), false);
    assert_eq!(
        solver.fixed_term_value_table.get(&key_five),
        Some(&y_var),
        "the remaining 5-valued term should be promoted after the old representative changes value"
    );
    assert_eq!(
        solver.fixed_term_value_table.get(&key_six),
        Some(&x_var),
        "the rekeyed term should become the representative for its new value"
    );
    assert_eq!(
        solver.fixed_term_value_members.get(&x_var),
        Some(&key_six),
        "membership must track the new key for the rekeyed term"
    );
    assert_eq!(
        solver.fixed_term_value_members.get(&y_var),
        Some(&key_five),
        "unmodified same-value members must keep their original key"
    );
    assert!(
        solver.pending_fixed_term_equalities.is_empty(),
        "stale pending equalities must be removed when a representative changes value: {:?}",
        solver.pending_fixed_term_equalities
    );
}
