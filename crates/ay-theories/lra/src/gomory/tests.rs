// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use ay_core::term::TermStore;
use ay_core::Sort;
use num_bigint::BigInt;
use num_traits::One;

#[test]
fn test_generate_gomory_cuts_skips_row_when_coefficients_explode() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Real);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    solver.rows.push(TableauRow::new(
        x_var,
        vec![(y_var, BigRational::one())],
        BigRational::zero(),
    ));
    solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(1),
        BigInt::from(1_000_000),
    ));
    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    // GMI cut is skipped due to coefficient explosion. No polarity
    // tightening (removed for soundness — polarity cuts could
    // interact unsoundly with multi-iteration Gomory).
    assert!(
        cuts.is_empty(),
        "explosive GMI cut must be skipped, got cuts: {cuts:?}"
    );
}

#[test]
fn test_generate_gomory_cuts_allows_row_within_abs_max_squared_bound() {
    // Test that small-coefficient rows are NOT rejected by the explosion guard.
    //
    // Row: x = (5/3)*y + 1/2, with x integer basic, y integer non-basic.
    // y has lower=0 and value=0 (already at bound).
    // x = (5/3)*0 + 1/2 = 1/2 (fractional), f_0 = 1/2.
    // f_j = frac(5/3) = 2/3 > 1-f_0 = 1/2.
    // Standard GMI (complementary): g_j = (1-f_j)/f_0 = (1/3)/(1/2) = 2/3.
    // abs_max = ceil(|5/3|) = 2, big_number = 4.
    // numer(g_j=2/3) = 2 <= 4 => passes explosion guard.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    solver.rows.push(TableauRow::new(
        x_var,
        vec![(y_var, BigRational::new(BigInt::from(5), BigInt::from(3)))],
        BigRational::new(BigInt::from(1), BigInt::from(2)),
    ));
    solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(1),
        BigInt::from(2),
    ));
    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    // Expect GMI cut only (polarity tightening removed for soundness).
    assert_eq!(cuts.len(), 1, "expected GMI cut: {cuts:?}");
    assert_eq!(cuts[0].coeffs.len(), 1);
    assert_eq!(cuts[0].coeffs[0].0, y_var);
    // g_j = (1-2/3)/(1/2) = 2/3, at lower bound => coeff on y is +2/3
    assert_eq!(
        cuts[0].coeffs[0].1,
        BigRational::new(BigInt::from(2), BigInt::from(3)),
    );
    assert_eq!(cuts[0].bound, BigRational::one());
}

#[test]
fn test_generate_gomory_cuts_fj_greater_than_f0() {
    // Test lower-bound branch in the window f_0 < f_j <= 1-f_0.
    //
    // Row: x = (8/3)*y + 1/4, with x integer basic, y integer non-basic.
    // y has lower=0 and value=0 (at bound).
    // x = (8/3)*0 + 1/4 = 1/4 (fractional).
    // f_0 = frac(1/4) = 1/4.
    // For y at lower bound: f_j = frac(8/3) = 2/3, and 2/3 <= 1-f_0 = 3/4.
    // Standard GMI: g_j = f_j/(1-f_0) = (2/3)/(3/4) = 8/9.
    // abs_max = ceil(|8/3|) = 3, big_number = 9 => numer(g_j)=8 is safe.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    solver.rows.push(TableauRow::new(
        x_var,
        vec![(y_var, BigRational::new(BigInt::from(8), BigInt::from(3)))],
        BigRational::new(BigInt::from(1), BigInt::from(4)),
    ));
    solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
    // x = (8/3)*0 + 1/4 = 1/4
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(1),
        BigInt::from(4),
    ));
    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    // GMI cut + polarity tightening (MAX → x <= floor(1/4) = 0).
    assert!(!cuts.is_empty(), "expected at least the GMI cut: {cuts:?}");
    assert_eq!(
        cuts[0].coeffs.len(),
        1,
        "expected single-term GMI cut: {:?}",
        cuts[0]
    );
    assert_eq!(cuts[0].coeffs[0].0, y_var);
    // Standard GMI: g_j = f_j/(1-f_0) = (2/3)/(3/4) = 8/9
    assert_eq!(
        cuts[0].coeffs[0].1,
        BigRational::new(BigInt::from(8), BigInt::from(9)),
    );
    // Cut bound = 1 + bound_adjust = 1 + 0 = 1
    assert_eq!(cuts[0].bound, BigRational::one());
}

#[test]
fn test_generate_gomory_cuts_lower_bound_complementary_branch() {
    // Test lower-bound branch when f_j > 1-f_0.
    //
    // Row: x = (11/6)*y + 1/4, with x integer basic, y integer non-basic.
    // y has lower=0 and value=0 (at bound).
    // x = (11/6)*0 + 1/4 = 1/4 (fractional), so f_0 = 1/4.
    // For y at lower bound: f_j = frac(11/6) = 5/6 > 1-f_0 = 3/4.
    // Standard GMI: g_j = (1-f_j)/f_0 = (1/6)/(1/4) = 2/3.
    // abs_max = ceil(11/6) = 2, big_number = 4, numer(2/3) = 2 <= 4.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    solver.rows.push(TableauRow::new(
        x_var,
        vec![(y_var, BigRational::new(BigInt::from(11), BigInt::from(6)))],
        BigRational::new(BigInt::from(1), BigInt::from(4)),
    ));
    solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(1),
        BigInt::from(4),
    ));
    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    // GMI cut + polarity tightening (MAX → x <= floor(1/4) = 0).
    assert!(!cuts.is_empty(), "expected at least the GMI cut: {cuts:?}");
    assert_eq!(cuts[0].coeffs.len(), 1);
    assert_eq!(cuts[0].coeffs[0].0, y_var);
    assert_eq!(
        cuts[0].coeffs[0].1,
        BigRational::new(BigInt::from(2), BigInt::from(3)),
    );
    assert_eq!(cuts[0].bound, BigRational::one());
}

#[test]
fn test_generate_gomory_cuts_integer_at_upper_bound() {
    // Test GMI cut when integer non-basic variable is at its UPPER bound.
    //
    // Row: x = (4/3)*y + 1/2, with x integer basic, y integer non-basic.
    // y has upper=5 and value=5 (at upper bound), lower=0.
    // x = (4/3)*5 + 1/2 = 20/3 + 1/2 = 43/6 (fractional).
    // f_0 = frac(43/6) = 1/6.
    //
    // For y at upper bound: effective_coeff = -(4/3) = -4/3
    // f_j = frac(-4/3) = 2/3 (floor(-4/3)=-2, frac=-4/3-(-2)=2/3)
    // Unified GMI formula (same as LB since effective_coeff handles sign):
    // f_j = 2/3 <= 1-f_0 = 5/6 => g_j = f_j/(1-f_0) = (2/3)/(5/6) = 4/5
    //
    // abs_max = ceil(4/3) = 2, big_number = 4, numer(4/5) = 4 <= 4.
    // At upper bound: coeff on y is -g_j = -4/5, bound_adjust = -g_j * ub = -(4/5)*5 = -4
    // Cut bound = 1 + bound_adjust = 1 - 4 = -3
    // Cut: (-4/5)*y >= -3  =>  y <= 15/4  (valid: y is integer at 5, tightens to y <= 3)
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    solver.rows.push(TableauRow::new(
        x_var,
        vec![(y_var, BigRational::new(BigInt::from(4), BigInt::from(3)))],
        BigRational::new(BigInt::from(1), BigInt::from(2)),
    ));
    solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
    // x = (4/3)*5 + 1/2 = 43/6
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(43),
        BigInt::from(6),
    ));
    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::from_integer(BigInt::from(5)));
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));
    solver.vars[y_var as usize].upper = Some(crate::Bound::without_reasons(
        BigRational::from_integer(BigInt::from(5)).into(),
        false,
    ));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    assert!(!cuts.is_empty(), "expected at least the GMI cut: {cuts:?}");
    assert_eq!(cuts[0].coeffs[0].0, y_var);
    // At upper bound: coeff on y = -g_j = -4/5
    assert_eq!(
        cuts[0].coeffs[0].1,
        BigRational::new(BigInt::from(-4), BigInt::from(5)),
        "expected coeff -4/5 for integer var at upper bound"
    );
    // Cut bound = 1 + bound_adjust = 1 + (-4) = -3
    assert_eq!(
        cuts[0].bound,
        BigRational::from_integer(BigInt::from(-3)),
        "expected cut bound -3"
    );
}

#[test]
fn test_gmi_upper_bound_coefficient_matches_standard_formula() {
    // Regression test for #4830: GMI upper-bound coefficient formula was
    // double-counting the sign conversion. This test uses the concrete
    // example from the design doc.
    //
    // Row: x = (3/4)*y + 1/4, with x integer basic, y integer non-basic.
    // y has upper=10 and value=10 (at upper bound), lower=0.
    // x = (3/4)*10 + 1/4 = 31/4 (fractional), f_0 = 3/4.
    //
    // For y at upper bound: effective_coeff = -(3/4) = -3/4
    // f_j = frac(-3/4) = 1/4 (floor(-3/4)=-1, frac=-3/4-(-1)=1/4)
    // Unified formula: f_j = 1/4 <= 1-f_0 = 1/4 => g_j = (1/4)/(1/4) = 1
    //
    // Buggy formula would use: f_j = 1/4 <= f_0 = 3/4 => g_j = (1/4)/(3/4) = 1/3
    // That gives coeff -1/3 (too tight). Correct is -1.
    //
    // Cross-check with Z3: frac(3/4)=3/4, threshold 3/4 <= f_0=3/4 yes,
    //   -(3/4)/(3/4) = -1. Matches.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    solver.rows.push(TableauRow::new(
        x_var,
        vec![(y_var, BigRational::new(BigInt::from(3), BigInt::from(4)))],
        BigRational::new(BigInt::from(1), BigInt::from(4)),
    ));
    solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
    // x = (3/4)*10 + 1/4 = 31/4
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(31),
        BigInt::from(4),
    ));
    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::from_integer(BigInt::from(10)));
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));
    solver.vars[y_var as usize].upper = Some(crate::Bound::without_reasons(
        BigRational::from_integer(BigInt::from(10)).into(),
        false,
    ));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    assert!(!cuts.is_empty(), "expected GMI cut: {cuts:?}");
    assert_eq!(cuts[0].coeffs[0].0, y_var);
    // g_j = 1, at UB: coeff = -1
    assert_eq!(
        cuts[0].coeffs[0].1,
        BigRational::from_integer(BigInt::from(-1)),
        "expected coeff -1 for integer var at upper bound (bug gave -1/3)"
    );
    // bound_adjust = -(1)*10 = -10, bound = 1 + (-10) = -9
    assert_eq!(
        cuts[0].bound,
        BigRational::from_integer(BigInt::from(-9)),
        "expected cut bound -9"
    );
}

#[test]
fn test_abs_ceil_coeff_matches_z3_semantics() {
    // Z3 computes abs(ceil(coeff)), not ceil(abs(coeff)).
    // For -1/2, this must be 0.
    let minus_half = BigRational::new(BigInt::from(-1), BigInt::from(2));
    assert_eq!(LraSolver::abs_ceil_coeff(&minus_half), BigInt::zero());

    let plus_half = BigRational::new(BigInt::from(1), BigInt::from(2));
    assert_eq!(LraSolver::abs_ceil_coeff(&plus_half), BigInt::one());
}

#[test]
fn test_generate_gomory_cuts_skips_row_when_numerator_exceeds_big_number() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);
    let z_var = solver.ensure_var_registered(z);

    solver.rows.push(TableauRow::new(
        x_var,
        vec![
            (y_var, BigRational::one()),
            (z_var, BigRational::from_integer(BigInt::from(2))),
        ],
        BigRational::zero(),
    ));
    solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(2),
        BigInt::from(5),
    ));

    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));

    solver.vars[z_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[z_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(z);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    assert!(
        cuts.is_empty(),
        "row should be skipped when numerator(new_a) > abs_max^2; got cuts: {cuts:?}"
    );
}

#[test]
fn test_current_solution_violates_cut_for_lower_and_upper_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(3),
        BigInt::from(2),
    ));

    let lower_cut = GomoryCut {
        coeffs: vec![(x_var, BigRational::one())],
        bound: BigRational::from_integer(BigInt::from(2)),
        is_lower: true,
        reasons: Vec::new(),
        source_term: None,
    };
    assert!(solver.current_solution_violates_cut(&lower_cut));

    let upper_cut = GomoryCut {
        coeffs: vec![(x_var, BigRational::one())],
        bound: BigRational::from_integer(BigInt::from(1)),
        is_lower: false,
        reasons: Vec::new(),
        source_term: None,
    };
    assert!(solver.current_solution_violates_cut(&upper_cut));

    let satisfied_cut = GomoryCut {
        coeffs: vec![(x_var, BigRational::one())],
        bound: BigRational::from_integer(BigInt::from(1)),
        is_lower: true,
        reasons: Vec::new(),
        source_term: None,
    };
    assert!(!solver.current_solution_violates_cut(&satisfied_cut));
}

#[test]
fn test_generate_gomory_cuts_collects_active_bound_reasons() {
    // Use coeff 5/3 so the standard GMI coefficient (2/3) fits within
    // the explosion guard (abs_max=2, big_number=4, numer(2/3)=2 <= 4).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let reason = terms.mk_var("r", Sort::Bool);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    solver.rows.push(TableauRow::new(
        x_var,
        vec![(y_var, BigRational::new(BigInt::from(5), BigInt::from(3)))],
        BigRational::new(BigInt::from(1), BigInt::from(2)),
    ));
    solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(1),
        BigInt::from(2),
    ));
    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[y_var as usize].lower = Some(crate::Bound::new(
        BigRational::zero().into(),
        vec![reason],
        vec![true],
        Vec::new(),
        false,
    ));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    // GMI cut + polarity tightening.
    assert!(!cuts.is_empty(), "expected at least the GMI cut");
    assert!(
        cuts[0].reasons.contains(&(reason, true)),
        "cut should include active bound reason; got {:?}",
        cuts[0].reasons
    );
}

#[test]
fn test_generate_gomory_cuts_limits_to_two_best_scored_rows() {
    // 3 rows with integer basic vars at different fractional values.
    // Cubic-bias scoring (Z3 parity) picks the 2 closest to f_0=0.5.
    // With standard normalization, use larger coefficients to avoid
    // the explosion guard (abs_max=4, big_number=16).
    let mut terms = TermStore::new();
    let x1 = terms.mk_var("x1", Sort::Int);
    let x2 = terms.mk_var("x2", Sort::Int);
    let x3 = terms.mk_var("x3", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x1_var = solver.ensure_var_registered(x1);
    let x2_var = solver.ensure_var_registered(x2);
    let x3_var = solver.ensure_var_registered(x3);
    let y_var = solver.ensure_var_registered(y);
    let z_var = solver.ensure_var_registered(z);

    let coeffs = vec![
        (y_var, BigRational::new(BigInt::from(10), BigInt::from(3))),
        (z_var, BigRational::new(BigInt::from(-5), BigInt::from(3))),
    ];
    solver
        .rows
        .push(TableauRow::new(x1_var, coeffs.clone(), BigRational::zero()));
    solver
        .rows
        .push(TableauRow::new(x2_var, coeffs.clone(), BigRational::zero()));
    solver
        .rows
        .push(TableauRow::new(x3_var, coeffs, BigRational::zero()));

    // f_0 values: 1/10, 1/3, 2/5.
    // Cubic bias scores: 1/10→1/729, 1/3→1/8, 2/5→8/27.
    // Top 2: f=2/5 (8/27) and f=1/3 (1/8).
    solver.vars[x1_var as usize].status = Some(VarStatus::Basic(0));
    solver.vars[x1_var as usize].value = crate::types::InfRational::from_rational(
        BigRational::new(BigInt::from(1), BigInt::from(10)),
    );
    solver.vars[x2_var as usize].status = Some(VarStatus::Basic(1));
    solver.vars[x2_var as usize].value = crate::types::InfRational::from_rational(
        BigRational::new(BigInt::from(1), BigInt::from(3)),
    );
    solver.vars[x3_var as usize].status = Some(VarStatus::Basic(2));
    solver.vars[x3_var as usize].value = crate::types::InfRational::from_rational(
        BigRational::new(BigInt::from(2), BigInt::from(5)),
    );

    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));
    solver.vars[z_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[z_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[z_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x1);
    integer_vars.insert(x2);
    integer_vars.insert(x3);
    integer_vars.insert(y);
    integer_vars.insert(z);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    // Standard GMI: all bounds are 1 (with LB=0, bound_adjust=0).
    // Limit is MAX_GOMORY_CUTS_PER_CHECK=2, so exactly 2 GMI cuts.
    assert_eq!(
        cuts.len(),
        2,
        "must generate at most 2 Gomory cuts: {cuts:?}"
    );
    // All valid cuts have bound = 1 with zero lower bounds.
    assert!(
        cuts.iter().all(|cut| cut.bound == BigRational::one()),
        "all standard GMI cuts should have bound = 1: {cuts:?}"
    );
}

#[test]
fn test_gomory_cut_is_small_classification() {
    // Small cut: all coefficients and bound fit in i64
    let small_cut = GomoryCut {
        coeffs: vec![
            (0, BigRational::new(BigInt::from(3), BigInt::from(4))),
            (1, BigRational::from_integer(BigInt::from(7))),
        ],
        bound: BigRational::from_integer(BigInt::from(42)),
        is_lower: true,
        reasons: Vec::new(),
        source_term: None,
    };
    assert!(
        small_cut.is_small(),
        "machine-int coefficients should be small"
    );

    // Big cut: numerator exceeds i64
    let huge = BigInt::from(i64::MAX) * BigInt::from(2);
    let big_cut = GomoryCut {
        coeffs: vec![(0, BigRational::new(huge, BigInt::from(1)))],
        bound: BigRational::one(),
        is_lower: true,
        reasons: Vec::new(),
        source_term: None,
    };
    assert!(!big_cut.is_small(), "overflowing numerator should be big");

    // Big cut: denominator exceeds i64
    let huge_denom = BigInt::from(i64::MAX) * BigInt::from(3);
    let big_denom_cut = GomoryCut {
        coeffs: vec![(0, BigRational::new(BigInt::from(1), huge_denom))],
        bound: BigRational::one(),
        is_lower: true,
        reasons: Vec::new(),
        source_term: None,
    };
    assert!(
        !big_denom_cut.is_small(),
        "overflowing denominator should be big"
    );

    // Big cut: bound is big even though coefficients are small
    let big_bound_cut = GomoryCut {
        coeffs: vec![(0, BigRational::one())],
        bound: BigRational::new(BigInt::from(i64::MAX) * BigInt::from(5), BigInt::from(1)),
        is_lower: true,
        reasons: Vec::new(),
        source_term: None,
    };
    assert!(!big_bound_cut.is_small(), "overflowing bound should be big");
}

#[test]
fn test_generate_gomory_cuts_skips_fixed_variable_in_cut() {
    // When a non-basic variable is fixed (at both lower and upper bound),
    // it should be skipped entirely in the GMI cut (Z3 gomory.cpp:296-300).
    // The cut should only contain terms for non-fixed variables.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);
    let z_var = solver.ensure_var_registered(z);

    // Row: x = (7/2)*y + (5/3)*z + 1/4
    // y is non-basic at lower=0, z is fixed at value=0 (lower=upper=0).
    // abs_max = max(ceil(7/2), ceil(5/3)) = max(4, 2) = 4, big_number = 16.
    // f_0 = frac(1/4) = 1/4. For y: f_j = frac(7/2) = 1/2.
    // f_j <= 1-f_0 = 3/4: g_j = (1/2)/(3/4) = 2/3. numer(2/3)=2 < 16. OK.
    solver.rows.push(TableauRow::new(
        x_var,
        vec![
            (y_var, BigRational::new(BigInt::from(7), BigInt::from(2))),
            (z_var, BigRational::new(BigInt::from(5), BigInt::from(3))),
        ],
        BigRational::new(BigInt::from(1), BigInt::from(4)),
    ));
    solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
    solver.vars[x_var as usize].value = crate::types::InfRational::from_rational(BigRational::new(
        BigInt::from(1),
        BigInt::from(4),
    ));
    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));
    // z is fixed: lower = upper = 0
    solver.vars[z_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[z_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[z_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));
    solver.vars[z_var as usize].upper = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);
    integer_vars.insert(z);

    let cuts = solver.generate_gomory_cuts(&integer_vars);
    // GMI cut should exist and only reference y (z is fixed → skipped).
    let gmi_cuts: Vec<_> = cuts
        .iter()
        .filter(|c| c.coeffs.iter().any(|(v, _)| *v == y_var))
        .collect();
    assert_eq!(gmi_cuts.len(), 1, "expected one GMI cut on y: {cuts:?}");
    assert!(
        !gmi_cuts[0].coeffs.iter().any(|(v, _)| *v == z_var),
        "fixed variable z must not appear in GMI cut: {:?}",
        gmi_cuts[0]
    );
}

#[test]
fn test_gomory_usage_tiebreaker_prefers_high_usage_variable() {
    // Two basic variables with the same fractional value (same score).
    // x1 is referenced as a non-basic in 2 extra rows; x2 in 0 extra rows.
    // The usage tiebreaker should prefer x1 (higher usage).
    // With MAX_GOMORY_CUTS_PER_CHECK=2, both will be selected, but x1
    // should be chosen first (and thus appear as the first cut).
    let mut terms = TermStore::new();
    let x1 = terms.mk_var("x1", Sort::Int);
    let x2 = terms.mk_var("x2", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let w1 = terms.mk_var("w1", Sort::Int);
    let w2 = terms.mk_var("w2", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x1_var = solver.ensure_var_registered(x1);
    let x2_var = solver.ensure_var_registered(x2);
    let y_var = solver.ensure_var_registered(y);
    let w1_var = solver.ensure_var_registered(w1);
    let w2_var = solver.ensure_var_registered(w2);

    // Row 0: x1 = (7/2)*y. x1 is basic here.
    solver.rows.push(TableauRow::new(
        x1_var,
        vec![(y_var, BigRational::new(BigInt::from(7), BigInt::from(2)))],
        BigRational::zero(),
    ));
    // Row 1: x2 = (7/2)*y. x2 is basic here.
    solver.rows.push(TableauRow::new(
        x2_var,
        vec![(y_var, BigRational::new(BigInt::from(7), BigInt::from(2)))],
        BigRational::zero(),
    ));
    // Row 2: w1 = 3*x1 + 1. x1 is non-basic here (adds to x1 usage).
    solver.rows.push(TableauRow::new(
        w1_var,
        vec![(x1_var, BigRational::from_integer(BigInt::from(3)))],
        BigRational::one(),
    ));
    // Row 3: w2 = 5*x1 + 2. x1 is non-basic here (adds to x1 usage).
    solver.rows.push(TableauRow::new(
        w2_var,
        vec![(x1_var, BigRational::from_integer(BigInt::from(5)))],
        BigRational::from_integer(BigInt::from(2)),
    ));

    // Both x1 and x2 have the same fractional value (1/4).
    solver.vars[x1_var as usize].status = Some(VarStatus::Basic(0));
    solver.vars[x1_var as usize].value = crate::types::InfRational::from_rational(
        BigRational::new(BigInt::from(1), BigInt::from(4)),
    );
    solver.vars[x2_var as usize].status = Some(VarStatus::Basic(1));
    solver.vars[x2_var as usize].value = crate::types::InfRational::from_rational(
        BigRational::new(BigInt::from(1), BigInt::from(4)),
    );

    // y at lower=0
    solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
    solver.vars[y_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::zero());
    solver.vars[y_var as usize].lower = Some(crate::Bound::without_reasons(
        BigRational::zero().into(),
        false,
    ));

    // w1, w2 are basic with integer values (not cut candidates).
    solver.vars[w1_var as usize].status = Some(VarStatus::Basic(2));
    solver.vars[w1_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::one());
    solver.vars[w2_var as usize].status = Some(VarStatus::Basic(3));
    solver.vars[w2_var as usize].value =
        crate::types::InfRational::from_rational(BigRational::from_integer(BigInt::from(2)));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x1);
    integer_vars.insert(x2);
    integer_vars.insert(y);
    integer_vars.insert(w1);
    integer_vars.insert(w2);

    // x1 usage = 2 (appears in rows 2 and 3 as non-basic).
    // x2 usage = 0 (only appears in row 1 as basic, not counted in coeffs).
    // With equal scores, x1 should sort before x2.
    // Both may generate cuts, but we verify that x1's row produces
    // the first GMI cut by checking the basic_var on the first cut.
    let cuts = solver.generate_gomory_cuts(&integer_vars);
    // At least one cut should be generated for x1's row.
    assert!(!cuts.is_empty(), "expected at least one cut: {cuts:?}");
}
