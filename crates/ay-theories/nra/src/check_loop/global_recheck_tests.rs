// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::NraSolver;
use ay_core::term::{Symbol, TermStore};
use ay_core::{Sort, TheoryLit, TheoryResult, TheorySolver};
use ay_lra::GomoryCut;
use num_rational::BigRational;
use num_traits::{One, Zero};

fn normalized_lra_check(solver: &mut NraSolver<'_>) -> TheoryResult {
    let result = solver.lra.check();
    solver.normalize_lra_result(result)
}

fn rat(value: i64) -> BigRational {
    BigRational::from_integer(value.into())
}

#[test]
fn model_sign_branch_only_unsat_fails_closed() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let one = terms.mk_rational(rat(1));
    let minus_one = terms.mk_rational(rat(-1));
    let ay = terms.mk_mul(vec![a, y]);
    let y_plus_z = terms.mk_add(vec![y, z]);
    let a_eq_one = terms.mk_eq(a, one);
    let ay_eq_minus_one = terms.mk_eq(ay, minus_one);
    let sum_eq_one = terms.mk_eq(y_plus_z, one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(a_eq_one, true);
    solver.assert_literal(ay_eq_minus_one, true);
    solver.assert_literal(sum_eq_one, true);
    assert!(matches!(
        normalized_lra_check(&mut solver),
        TheoryResult::Sat
    ));
    assert_eq!(solver.var_value(y), Some(rat(1)));
    assert_eq!(solver.var_value(z), Some(rat(0)));
    solver.snapshot_fixed_factors_on_first_iteration(0);
    let sign_vars = crate::sign::vars_needing_model_sign(
        &solver.monomials,
        &solver.aux_to_monomial,
        &solver.var_sign_constraints,
    );
    assert!(sign_vars.contains(&y));

    // The relaxed model has y > 0, so the actual sign phase chooses y >= 0.
    // The exact identity a*y = y then forces y = -1 and refutes only that
    // branch. The opposite branch has the genuine witness y=-1, z=2.
    solver.lra.push();
    solver.tentative_depth += 1;
    assert!(solver.inject_tentative_sign_cuts() >= 1);
    let mut key = vec![a, y];
    key.sort_unstable_by_key(|term| term.0);
    let monomial = solver
        .monomials
        .get(&key)
        .expect("a*y must be registered")
        .clone();
    assert_eq!(solver.add_fixed_factor_linearization(&monomial), 2);
    assert_eq!(rat(1) * rat(-1), rat(-1));
    assert_eq!(rat(-1) + rat(2), rat(1));

    assert!(matches!(
        solver.recheck_with_global_lemmas(),
        TheoryResult::Unknown
    ));
    assert_eq!(solver.tentative_depth, 0);
    let end_to_end = solver.check();
    assert!(
        !matches!(
            end_to_end,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "the sign-opposite witness makes the original formula SAT: {end_to_end:?}"
    );
}

#[test]
fn division_tangent_only_unsat_fails_closed() {
    let mut terms = TermStore::new();
    let d = terms.mk_var("d", Sort::Real);
    let one = terms.mk_rational(rat(1));
    let two = terms.mk_rational(rat(2));
    let three = terms.mk_rational(rat(3));
    let seven = terms.mk_rational(rat(7));
    let q = terms.mk_div(one, d);
    let lower = terms.mk_le(one, d);
    let upper = terms.mk_le(d, two);
    let three_d = terms.mk_mul(vec![three, d]);
    let two_q = terms.mk_mul(vec![two, q]);
    let affine = terms.mk_add(vec![three_d, two_q]);
    let affine_eq_seven = terms.mk_eq(affine, seven);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(lower, true);
    solver.assert_literal(upper, true);
    solver.assert_literal(affine_eq_seven, true);
    assert_eq!(solver.div_purifications.len(), 1);
    assert!(matches!(
        normalized_lra_check(&mut solver),
        TheoryResult::Sat
    ));

    // The feasible relaxed point (d,q)=(1,2) generates 2d+q<=3. The cut
    // excludes the original problem's exact witness (d,q)=(2,1/2).
    assert_eq!(rat(3) * rat(1) + rat(2) * rat(2), rat(7));
    assert!(rat(2) * rat(1) + rat(2) > rat(3));
    let half = BigRational::new(1.into(), 2.into());
    assert_eq!(rat(2) * &half, rat(1));
    assert_eq!(rat(3) * rat(2) + rat(2) * &half, rat(7));
    assert!(rat(2) * rat(2) + &half > rat(3));

    solver.lra.push();
    solver.tentative_depth += 1;
    let d_var = solver.lra.ensure_var_registered(d);
    let q_var = solver.lra.ensure_var_registered(q);
    solver.lra.add_gomory_cut(
        &GomoryCut {
            coeffs: vec![(d_var, rat(2)), (q_var, rat(1))],
            bound: rat(3),
            is_lower: false,
            reasons: Vec::new(),
            source_term: None,
        },
        q,
    );

    assert!(matches!(
        solver.recheck_with_global_lemmas(),
        TheoryResult::Unknown
    ));
    assert_eq!(solver.tentative_depth, 0);
    let end_to_end = solver.check();
    assert!(
        !matches!(
            end_to_end,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "the reciprocal witness makes the original formula SAT: {end_to_end:?}"
    );
}

#[test]
fn exact_fixed_factor_unsat_survives_global_recheck() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let one = terms.mk_rational(BigRational::one());
    let xy = terms.mk_mul(vec![x, y]);
    let x_eq_zero = terms.mk_eq(x, zero);
    let xy_ge_one = terms.mk_ge(xy, one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(x_eq_zero, true);
    solver.assert_literal(xy_ge_one, true);
    assert!(matches!(
        normalized_lra_check(&mut solver),
        TheoryResult::Sat
    ));
    solver.snapshot_fixed_factors_on_first_iteration(0);
    assert_eq!(
        solver.fixed_factor_values.get(&x),
        Some(&BigRational::zero())
    );

    let replay = solver.recheck_with_global_lemmas();
    let conflict = match &replay {
        TheoryResult::Unsat(conflict) => conflict.as_slice(),
        TheoryResult::UnsatWithFarkas(conflict) => conflict.literals.as_slice(),
        _ => panic!("expected exact fixed-factor UNSAT, got {replay:?}"),
    };
    assert!(conflict.contains(&TheoryLit::new(x_eq_zero, true)));
    assert!(conflict.contains(&TheoryLit::new(xy_ge_one, true)));
    assert_eq!(solver.tentative_depth, 0);
}

#[test]
fn shared_equality_pin_is_not_forged_as_nra_authority() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let one = terms.mk_rational(BigRational::one());
    let f_zero = terms.mk_app(Symbol::named("f"), vec![zero], Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let product = terms.mk_mul(vec![f_zero, y]);
    let product_ge_one = terms.mk_ge(product, one);
    let equality_reason = terms.mk_eq(f_zero, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(product_ge_one, true);
    solver.assert_shared_equality(f_zero, zero, &[TheoryLit::new(equality_reason, true)]);
    assert!(matches!(
        normalized_lra_check(&mut solver),
        TheoryResult::Sat
    ));
    let (lower, upper) = solver.lra.get_bounds(f_zero).expect("shared LRA bounds");
    assert_eq!(
        lower.expect("shared lower").value_big(),
        BigRational::zero()
    );
    assert_eq!(
        upper.expect("shared upper").value_big(),
        BigRational::zero()
    );

    solver.snapshot_fixed_factors_on_first_iteration(0);
    assert!(!solver.fixed_factor_values.contains_key(&f_zero));
    assert!(matches!(
        solver.recheck_with_global_lemmas(),
        TheoryResult::Unknown
    ));
    assert_eq!(solver.tentative_depth, 0);
    let end_to_end = solver.check();
    assert!(
        matches!(end_to_end, TheoryResult::Unknown),
        "the shared-premise contradiction must decline without replayable authority: {end_to_end:?}"
    );
}

#[test]
fn even_power_global_recheck_preserves_asserted_core() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let square = terms.mk_mul(vec![x, x]);
    let square_lt_zero = terms.mk_lt(square, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(square_lt_zero, true);
    assert!(matches!(
        normalized_lra_check(&mut solver),
        TheoryResult::Sat
    ));
    solver.snapshot_fixed_factors_on_first_iteration(0);

    let replay = solver.recheck_with_global_lemmas();
    let conflict = match &replay {
        TheoryResult::Unsat(conflict) => conflict.as_slice(),
        TheoryResult::UnsatWithFarkas(conflict) => conflict.literals.as_slice(),
        _ => panic!("expected even-power UNSAT, got {replay:?}"),
    };
    assert_eq!(conflict, &[TheoryLit::new(square_lt_zero, true)]);
    assert_eq!(solver.tentative_depth, 0);
}

#[test]
fn empty_nra_authority_declines_even_with_shared_aux_bound() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let minus_one = terms.mk_rational(rat(-1));
    let square = terms.mk_mul(vec![x, x]);
    let square_lt_zero = terms.mk_lt(square, zero);
    let shared_reason = terms.mk_eq(square, minus_one);

    let mut solver = NraSolver::new(&terms);
    solver.internalize_atom(square_lt_zero);
    solver.assert_shared_equality(square, minus_one, &[TheoryLit::new(shared_reason, true)]);
    assert!(solver.asserted.is_empty());
    assert!(!solver.monomials.is_empty());
    assert!(matches!(
        normalized_lra_check(&mut solver),
        TheoryResult::Sat
    ));
    assert_eq!(solver.var_value(square), Some(rat(-1)));

    assert!(matches!(
        solver.recheck_with_global_lemmas(),
        TheoryResult::Unknown
    ));
    assert_eq!(solver.tentative_depth, 0);
}
