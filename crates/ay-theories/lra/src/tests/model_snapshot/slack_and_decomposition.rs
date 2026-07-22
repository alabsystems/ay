// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_model_seeded_propagation_closes_two_row_cycle_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());

    let x_plus_y = terms.mk_add(vec![x, y]);
    let x_minus_y = terms.mk_sub(vec![x, y]);
    let eq_sum_zero = terms.mk_eq(x_plus_y, zero);
    let eq_diff_zero = terms.mk_eq(x_minus_y, zero);
    let x_le_0 = terms.mk_le(x, zero);
    let x_ge_0 = terms.mk_ge(x, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    for atom in [eq_sum_zero, eq_diff_zero, x_le_0, x_ge_0, y_le_0, y_ge_0] {
        solver.register_atom(atom);
    }

    solver.assert_literal(eq_sum_zero, true);
    solver.assert_literal(eq_diff_zero, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "two-row cycle should stay SAT before propagated bounds, got {result:?}"
    );

    let propagations = solver.propagate();
    for expected in [
        TheoryLit::new(x_le_0, true),
        TheoryLit::new(x_ge_0, true),
        TheoryLit::new(y_le_0, true),
        TheoryLit::new(y_ge_0, true),
    ] {
        let propagation = propagations
            .iter()
            .find(|prop| prop.literal == expected)
            .unwrap_or_else(|| {
                panic!("expected model-seeded propagation for {expected:?}, got {propagations:?}")
            });
        assert!(
            !propagation.reason.is_empty(),
            "model-seeded propagation for {expected:?} must carry reasons"
        );
        assert!(
            propagation
                .reason
                .iter()
                .all(|lit| matches!(lit.term, t if t == eq_sum_zero || t == eq_diff_zero)),
            "expected equality reasons for {:?}, got {:?}",
            expected,
            propagation.reason
        );
    }
}

#[test]
fn test_stricter_existing_atom_blocks_weaker_bound_refinement_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());

    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let x_lt_3 = terms.mk_lt(x, three);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(y_ge_0);
    solver.register_atom(y_le_0);
    solver.register_atom(x_lt_3);
    solver.register_atom(sum_le_3);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(sum_le_3, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after fixing y = 0 and asserting x + y <= 3, got {result:?}"
    );

    let refinements = solver.take_bound_refinements();
    assert!(
        !refinements
            .iter()
            .any(|req| req.variable == x && req.is_upper && req.bound_value == three_value),
        "existing stricter atom x < 3 should block weaker x <= 3 refinement, got {refinements:?}"
    );
}

#[test]
fn test_registered_additive_slack_stays_disabled_issue_6566() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let sum = terms.mk_add(vec![x, y]);
    let x_le_1 = terms.mk_le(x, one);
    let y_le_2 = terms.mk_le(y, two);
    let sum_le_10 = terms.mk_le(sum, ten);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_1);
    solver.register_atom(y_le_2);
    solver.register_atom(sum_le_10);
    solver.assert_literal(x_le_1, true);
    solver.assert_literal(y_le_2, true);
    solver.assert_literal(sum_le_10, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT after asserting x <= 1, y <= 2, x + y <= 10, got {result:?}"
    );

    let slack = *solver
        .expr_to_slack
        .values()
        .next()
        .map(|(slack, _)| slack)
        .expect("compound atom should create a slack variable");
    let row_idx = *solver
        .basic_var_to_row
        .get(&slack)
        .expect("slack variable should stay basic in its definition row");
    solver.queue_bound_refinement_request(
        slack,
        BigRational::from(BigInt::from(-7)),
        true,
        row_idx,
    );

    let refinements = solver.take_bound_refinements();
    assert!(
        refinements.is_empty(),
        "registered additive slack refinements must stay disabled, got {refinements:?}"
    );
}

// test_eager_relative_slack_queues_refinement_without_simplex_issue_6586:
// Removed in #6617 — the inline per-variable eager refinement path was deleted.
// Relative slack refinements are now handled by the post-simplex batch path
// (compute_implied_bounds + queue_post_simplex_refinements).

#[test]
fn test_eager_additive_slack_stays_disabled_without_simplex_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let sum = terms.mk_add(vec![x, y]);
    let x_le_1 = terms.mk_le(x, one);
    let y_le_2 = terms.mk_le(y, two);
    let sum_le_10 = terms.mk_le(sum, ten);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_1);
    solver.register_atom(y_le_2);
    solver.register_atom(sum_le_10);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    solver.assert_var_bound(
        x_var,
        BigRational::from(BigInt::from(1)).into(),
        BoundType::Upper,
        false,
        x_le_1,
        true,
        Rational::one(),
    );
    assert!(
        solver.take_bound_refinements().is_empty(),
        "one additive endpoint bound alone must not queue a refinement"
    );

    solver.assert_var_bound(
        y_var,
        BigRational::from(BigInt::from(2)).into(),
        BoundType::Upper,
        false,
        y_le_2,
        true,
        Rational::one(),
    );

    assert!(
        solver.take_bound_refinements().is_empty(),
        "additive slack targets must stay disabled before simplex"
    );
}

#[test]
fn test_unregistered_slack_is_not_materializable_issue_6548() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let sum = terms.mk_add(vec![x, y]);

    let mut solver = LraSolver::new(&terms);
    let expr = solver.parse_linear_expr(sum);
    let (slack, _) = solver.get_or_create_slack(&expr);

    assert!(
        !solver.can_materialize_bound_refinement_var(slack),
        "internal-only slack rows should not be treated as bound-refinement targets"
    );
}

/// #9031: Bound refinements are disabled for soundness. Verify that
/// queue_bound_refinement_request correctly returns empty results.
/// The implied bound derivation path (compute_implied_bounds) handles
/// the equivalent functionality via the implied_bounds array.
#[test]
fn test_registered_relative_slack_refinement_disabled_issue_9031() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let x_le_y = terms.mk_le(x, y);
    let x_le_0 = terms.mk_le(x, zero);
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_y);
    solver.register_atom(x_le_0);
    solver.register_atom(y_ge_0);
    let x_var = solver.ensure_var_registered(x) as usize;
    let y_var = solver.ensure_var_registered(y) as usize;
    solver.vars[x_var].upper = Some(Bound::new(
        BigRational::zero().into(),
        vec![x_le_0],
        vec![true],
        Vec::new(),
        false,
    ));
    solver.vars[y_var].lower = Some(Bound::new(
        BigRational::zero().into(),
        vec![y_ge_0],
        vec![true],
        Vec::new(),
        false,
    ));

    let slack = *solver
        .expr_to_slack
        .values()
        .next()
        .map(|(slack, _)| slack)
        .expect("relative atom should create a slack variable");
    let row_idx = *solver
        .basic_var_to_row
        .get(&slack)
        .expect("slack variable should stay basic in its definition row");
    // #9031: Bound refinements are disabled for soundness.
    solver.queue_bound_refinement_request(slack, BigRational::zero(), true, row_idx);

    let refinements = solver.take_bound_refinements();
    assert!(
        refinements.is_empty(),
        "bound refinements are disabled (#9031), expected empty, got {refinements:?}"
    );
}

/// #9031: Bound refinements are disabled for soundness. Verify that
/// queue_bound_refinement_request on offset relative slack returns empty.
#[test]
fn test_registered_offset_lhs_relative_slack_refinement_disabled_issue_9031() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let five_value = BigRational::from(BigInt::from(5));
    let five = terms.mk_rational(five_value.clone());
    let lhs = terms.mk_add(vec![x, five]);
    let lhs_le_y = terms.mk_le(lhs, y);
    let x_le_0 = terms.mk_le(x, zero);
    let y_ge_5 = terms.mk_ge(y, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(lhs_le_y);
    solver.register_atom(x_le_0);
    solver.register_atom(y_ge_5);
    let x_var = solver.ensure_var_registered(x) as usize;
    let y_var = solver.ensure_var_registered(y) as usize;
    solver.vars[x_var].upper = Some(Bound::new(
        BigRational::zero().into(),
        vec![x_le_0],
        vec![true],
        Vec::new(),
        false,
    ));
    solver.vars[y_var].lower = Some(Bound::new(
        five_value.into(),
        vec![y_ge_5],
        vec![true],
        Vec::new(),
        false,
    ));

    let slack = *solver
        .expr_to_slack
        .values()
        .next()
        .map(|(slack, _)| slack)
        .expect("offset relative atom should create a slack variable");
    let row_idx = *solver
        .basic_var_to_row
        .get(&slack)
        .expect("offset relative slack should stay basic in its definition row");
    // #9031: Bound refinements are disabled for soundness.
    solver.queue_bound_refinement_request(slack, BigRational::zero(), true, row_idx);

    let refinements = solver.take_bound_refinements();
    assert!(
        refinements.is_empty(),
        "bound refinements are disabled (#9031), expected empty, got {refinements:?}"
    );
}

#[test]
fn test_registered_relative_slack_respects_direction_guard_issue_6548() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let x_le_y = terms.mk_le(x, y);
    let x_ge_0 = terms.mk_ge(x, zero);
    let y_le_0 = terms.mk_le(y, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_y);
    solver.register_atom(x_ge_0);
    solver.register_atom(y_le_0);
    let x_var = solver.ensure_var_registered(x) as usize;
    let y_var = solver.ensure_var_registered(y) as usize;
    solver.vars[x_var].lower = Some(Bound::new(
        BigRational::zero().into(),
        vec![x_ge_0],
        vec![true],
        Vec::new(),
        false,
    ));
    solver.vars[y_var].upper = Some(Bound::new(
        BigRational::zero().into(),
        vec![y_le_0],
        vec![true],
        Vec::new(),
        false,
    ));

    let slack = *solver
        .expr_to_slack
        .values()
        .next()
        .map(|(slack, _)| slack)
        .expect("relative atom should create a slack variable");
    let row_idx = *solver
        .basic_var_to_row
        .get(&slack)
        .expect("slack variable should stay basic in its definition row");
    solver.queue_bound_refinement_request(slack, BigRational::zero(), false, row_idx);

    let refinements = solver.take_bound_refinements();
    assert!(
        refinements.is_empty(),
        "polarity-mismatched relative refinements must stay disabled, got {refinements:?}"
    );
}

/// #9031: Bound refinements are disabled for soundness. The post-simplex
/// refinement pipeline (queue_post_simplex_refinements) calls
/// queue_bound_refinement_request which immediately returns. Verify that
/// the pipeline correctly produces no refinements.
#[test]
fn test_post_simplex_relative_slack_refinement_disabled_issue_9031() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let neg_one_value = BigRational::from(BigInt::from(-1));
    let neg_one = terms.mk_rational(neg_one_value.clone());
    let x_le_y = terms.mk_le(x, y);
    let x_le_neg_one = terms.mk_le(x, neg_one);
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_y);
    solver.register_atom(x_le_neg_one);
    solver.register_atom(y_ge_0);
    let x_var = solver.ensure_var_registered(x) as usize;
    let y_var = solver.ensure_var_registered(y) as usize;
    solver.vars[x_var].upper = Some(Bound::new(
        neg_one_value.into(),
        vec![x_le_neg_one],
        vec![true],
        Vec::new(),
        false,
    ));
    solver.vars[y_var].lower = Some(Bound::new(
        BigRational::zero().into(),
        vec![y_ge_0],
        vec![true],
        Vec::new(),
        false,
    ));

    let slack = *solver
        .expr_to_slack
        .values()
        .next()
        .map(|(slack, _)| slack)
        .expect("relative atom should create a slack variable");
    let row_idx = *solver
        .basic_var_to_row
        .get(&slack)
        .expect("relative slack should stay basic in its definition row");
    solver
        .implied_bounds
        .resize(solver.vars.len(), (None, None));
    solver.implied_bounds[slack as usize].1 = Some(ImpliedBound {
        value: Rational::from(-1i32),
        strict: false,
        row_idx,
        explanation: None,
    });

    solver.queue_post_simplex_refinements(&DenseU32Set::default(), false);

    let refinements = solver.take_bound_refinements();
    // #9031: Bound refinements are disabled for soundness.
    assert!(
        refinements.is_empty(),
        "bound refinements are disabled (#9031), expected empty, got {refinements:?}"
    );
}

#[test]
fn test_collect_row_reasons_dedup_handles_long_explanation_chain_issue_6617() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let chain_len = 10usize;

    let vars: Vec<TermId> = (0..=chain_len)
        .map(|idx| terms.mk_var(format!("x{idx}"), Sort::Real))
        .collect();
    let root_reason = terms.mk_ge(vars[0], zero);

    let mut solver = LraSolver::new(&terms);
    let var_ids: Vec<u32> = vars
        .iter()
        .map(|&term| solver.ensure_var_registered(term))
        .collect();
    solver
        .implied_bounds
        .resize(solver.vars.len(), (None, None));

    solver.vars[var_ids[0] as usize].lower = Some(Bound::new(
        BigRational::zero().into(),
        vec![root_reason],
        vec![true],
        Vec::new(),
        false,
    ));
    // #8511: Mark root_reason as asserted so collect_reasons_from_explanation
    // can validate the direct bound's reasons are still asserted.
    solver.asserted.insert(root_reason, true);
    solver.implied_bounds[var_ids[0] as usize].0 = Some(ImpliedBound {
        value: Rational::from(0i32),
        strict: false,
        row_idx: usize::MAX,
        explanation: None,
    });

    for idx in 1..=chain_len {
        solver.implied_bounds[var_ids[idx] as usize].0 = Some(ImpliedBound {
            value: Rational::from(idx as i32),
            strict: false,
            row_idx: idx,
            explanation: Some(BoundExplanation {
                contributing_vars: smallvec::smallvec![(var_ids[idx - 1], false)],
            }),
        });
    }

    let mut reasons = Vec::new();
    let mut seen = HashSet::default();
    let ok = solver.collect_row_reasons_dedup(var_ids[chain_len], false, &mut reasons, &mut seen);

    assert!(
        ok,
        "eager explanations should justify chains longer than the recursive MAX_DEPTH fallback"
    );
    assert_eq!(
        reasons,
        vec![TheoryLit::new(root_reason, true)],
        "reason collection should reach the root direct bound witness"
    );
}

#[test]
fn test_decompose_arithmetic_eq_raw_ge_shares_slack_with_le_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let sum = terms.mk_add(vec![x, y]);
    let eq = terms.mk_eq(sum, ten);

    let decomposed = terms.decompose_arithmetic_eq(eq);
    let (sum_le, raw_sum_ge) = match terms.get(decomposed) {
        TermData::App(Symbol::Named(name), args) if name == "and" && args.len() == 2 => {
            (args[0], args[1])
        }
        other => panic!("expected decomposed equality conjunction, got {other:?}"),
    };

    assert!(
        matches!(terms.get(sum_le), TermData::App(Symbol::Named(name), _) if name == "<="),
        "first equality half should stay as <="
    );
    assert!(
        matches!(terms.get(raw_sum_ge), TermData::App(Symbol::Named(name), _) if name == ">="),
        "second equality half should be a raw >= app"
    );

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le);
    solver.register_atom(raw_sum_ge);

    let le_info = solver
        .atom_cache
        .get(&sum_le)
        .and_then(|info| info.as_ref())
        .unwrap_or_else(|| panic!("missing parsed info for <= half {sum_le:?}"));
    let ge_info = solver
        .atom_cache
        .get(&raw_sum_ge)
        .and_then(|info| info.as_ref())
        .unwrap_or_else(|| panic!("missing parsed info for >= half {raw_sum_ge:?}"));

    assert!(le_info.is_le, "<= half should parse as upper-bound atom");
    assert!(
        !ge_info.is_le,
        "raw >= half should parse as lower-bound atom after #4919"
    );
    assert_eq!(
        le_info.expr.coeffs, ge_info.expr.coeffs,
        "decomposed equality halves must use the same normalized coefficients"
    );
    assert_eq!(
        le_info.expr.constant, ge_info.expr.constant,
        "decomposed equality halves must use the same normalized constant"
    );

    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);
    let shared_entries: Vec<_> = solver
        .atom_index
        .iter()
        .filter_map(|(&var, atoms)| {
            let le_atom = atoms.iter().find(|atom| atom.term == sum_le)?;
            let ge_atom = atoms.iter().find(|atom| atom.term == raw_sum_ge)?;
            Some((var, le_atom, ge_atom))
        })
        .collect();

    assert_eq!(
        shared_entries.len(),
        1,
        "expected <= and raw >= halves to share exactly one slack index entry, got {shared_entries:?}"
    );

    let (shared_var, le_atom, ge_atom) = shared_entries[0];
    assert_ne!(
        shared_var, x_var,
        "compound equality should register on a slack variable, not x"
    );
    assert_ne!(
        shared_var, y_var,
        "compound equality should register on a slack variable, not y"
    );
    assert!(
        le_atom.is_upper,
        "<= half should be indexed as the upper-bound direction"
    );
    assert!(
        !ge_atom.is_upper,
        "raw >= half should be indexed as the lower-bound direction"
    );
    assert_eq!(
        le_atom.bound_value, ge_atom.bound_value,
        "shared slack bounds must line up across equality halves"
    );
}

#[test]
fn test_decompose_disequality_raw_gt_shares_slack_with_lt_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let sum = terms.mk_add(vec![x, y]);
    let distinct = terms.mk_distinct(vec![sum, zero]);

    let decomposed = terms.decompose_disequality(distinct);
    let (sum_lt, raw_sum_gt) = match terms.get(decomposed) {
        TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2 => {
            (args[0], args[1])
        }
        other => panic!("expected decomposed disequality disjunction, got {other:?}"),
    };

    assert!(
        matches!(terms.get(sum_lt), TermData::App(Symbol::Named(name), _) if name == "<"),
        "first disequality branch should stay as <"
    );
    assert!(
        matches!(terms.get(raw_sum_gt), TermData::App(Symbol::Named(name), _) if name == ">"),
        "second disequality branch should be a raw > app"
    );

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_lt);
    solver.register_atom(raw_sum_gt);

    let lt_info = solver
        .atom_cache
        .get(&sum_lt)
        .and_then(|info| info.as_ref())
        .unwrap_or_else(|| panic!("missing parsed info for < branch {sum_lt:?}"));
    let gt_info = solver
        .atom_cache
        .get(&raw_sum_gt)
        .and_then(|info| info.as_ref())
        .unwrap_or_else(|| panic!("missing parsed info for > branch {raw_sum_gt:?}"));

    assert!(lt_info.is_le, "< branch should parse as upper-bound atom");
    assert!(
        !gt_info.is_le,
        "raw > branch should parse as lower-bound atom after #4919"
    );
    assert_eq!(
        lt_info.expr.coeffs, gt_info.expr.coeffs,
        "decomposed disequality branches must use the same normalized coefficients"
    );
    assert_eq!(
        lt_info.expr.constant, gt_info.expr.constant,
        "decomposed disequality branches must use the same normalized constant"
    );

    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);
    let shared_entries: Vec<_> = solver
        .atom_index
        .iter()
        .filter_map(|(&var, atoms)| {
            let lt_atom = atoms.iter().find(|atom| atom.term == sum_lt)?;
            let gt_atom = atoms.iter().find(|atom| atom.term == raw_sum_gt)?;
            Some((var, lt_atom, gt_atom))
        })
        .collect();

    assert_eq!(
        shared_entries.len(),
        1,
        "expected < and raw > branches to share exactly one slack index entry, got {shared_entries:?}"
    );

    let (shared_var, lt_atom, gt_atom) = shared_entries[0];
    assert_ne!(
        shared_var, x_var,
        "compound disequality should register on a slack variable, not x"
    );
    assert_ne!(
        shared_var, y_var,
        "compound disequality should register on a slack variable, not y"
    );
    assert!(
        lt_atom.is_upper,
        "< branch should be indexed as the upper-bound direction"
    );
    assert!(
        !gt_atom.is_upper,
        "raw > branch should be indexed as the lower-bound direction"
    );
    assert_eq!(
        lt_atom.bound_value, gt_atom.bound_value,
        "shared slack bounds must line up across disequality branches"
    );
}
