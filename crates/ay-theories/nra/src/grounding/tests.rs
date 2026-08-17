// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::term::{Symbol, TermId, TermStore};
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::cover::{bipartite_sides, free_factor_count, greedy_cover, grounding_covers};
use super::residual::{solve_grounded_residual, substitute_pins, Interval};
use super::*;
use crate::univariate::{MultiPoly, Rel};

fn monomial(variables: &[u32]) -> Vec<TermId> {
    variables.iter().map(|&variable| TermId(variable)).collect()
}

fn pin(variable: u32, value: i64) -> (TermId, BigRational) {
    (TermId(variable), BigRational::from_integer(value.into()))
}

fn term(coefficient: i64, variables: &[u32]) -> (Vec<TermId>, BigRational) {
    (
        monomial(variables),
        BigRational::from_integer(coefficient.into()),
    )
}

fn pin_map(pins: &[(TermId, BigRational)]) -> crate::HashMap<TermId, &BigRational> {
    pins.iter()
        .map(|(variable, value)| (*variable, value))
        .collect()
}

#[test]
fn bipartite_sides_split_a_template_grid() {
    let monomials = vec![
        monomial(&[1, 10]),
        monomial(&[1, 11]),
        monomial(&[2, 10]),
        monomial(&[2, 11]),
    ];
    let (left, right) = bipartite_sides(&monomials).expect("grid is bipartite");
    let mut sides = [left, right];
    sides.sort();
    assert_eq!(sides[0], vec![TermId(1), TermId(2)]);
    assert_eq!(sides[1], vec![TermId(10), TermId(11)]);
}

#[test]
fn bipartite_sides_decline_squares_and_odd_cycles() {
    assert!(bipartite_sides(&[monomial(&[1, 1])]).is_none());
    let triangle = vec![monomial(&[1, 2]), monomial(&[2, 3]), monomial(&[1, 3])];
    assert!(bipartite_sides(&triangle).is_none());
}

#[test]
fn greedy_cover_is_deterministic_and_covers_every_factor_tail() {
    let monomials = vec![
        monomial(&[1, 1]),
        monomial(&[1, 2, 3]),
        monomial(&[2, 3]),
        monomial(&[4, 5]),
    ];
    let cover = greedy_cover(&monomials);
    for item in &monomials {
        assert!(free_factor_count(item, &cover) <= 1);
    }
    assert_eq!(cover, greedy_cover(&monomials));
    assert_eq!(greedy_cover(&[monomial(&[7, 7])]), vec![TermId(7)]);
}

#[test]
fn candidate_covers_are_unique_nonempty_and_valid() {
    let monomials = vec![monomial(&[1, 10]), monomial(&[2, 10])];
    let covers = grounding_covers(&monomials);
    assert!(!covers.is_empty());
    for (position, cover) in covers.iter().enumerate() {
        assert!(!cover.is_empty());
        assert!(monomials
            .iter()
            .all(|item| free_factor_count(item, cover) <= 1));
        assert!(!covers[position + 1..].contains(cover));
    }
}

#[test]
fn pin_substitution_linearizes_and_combines_exactly() {
    // 3*x*y + 2*y - 5 with x=4 becomes 14*y - 5.
    let polynomial = MultiPoly {
        terms: vec![term(3, &[1, 2]), term(2, &[2]), term(-5, &[])],
    };
    let pins = [pin(1, 4)];
    let (constant, linear) =
        substitute_pins(&polynomial, &pin_map(&pins)).expect("linear residual");
    assert_eq!(constant, BigRational::from_integer((-5).into()));
    assert_eq!(linear, vec![pin(2, 14)]);

    // x*y - 2*y with x=2 cancels completely.
    let cancelling = MultiPoly {
        terms: vec![term(1, &[1, 2]), term(-2, &[2])],
    };
    let pins = [pin(1, 2)];
    let (constant, linear) = substitute_pins(&cancelling, &pin_map(&pins)).expect("linear");
    assert!(constant.is_zero());
    assert!(linear.is_empty());
}

#[test]
fn pin_substitution_handles_fully_pinned_and_zero_annihilated_terms() {
    // x*y + x with x=2,y=3 is the constant 8.
    let fully_pinned = MultiPoly {
        terms: vec![term(1, &[1, 2]), term(1, &[1])],
    };
    let pins = [pin(1, 2), pin(2, 3)];
    let (constant, linear) = substitute_pins(&fully_pinned, &pin_map(&pins)).expect("fully pinned");
    assert_eq!(constant, BigRational::from_integer(8.into()));
    assert!(linear.is_empty());

    // x*y + y with x=0 drops the annihilated product and leaves y.
    let annihilated = MultiPoly {
        terms: vec![term(1, &[1, 2]), term(1, &[2])],
    };
    let pins = [pin(1, 0)];
    let (constant, linear) =
        substitute_pins(&annihilated, &pin_map(&pins)).expect("linear after zero pin");
    assert!(constant.is_zero());
    assert_eq!(linear, vec![pin(2, 1)]);
}

#[test]
fn pin_substitution_declines_a_nonlinear_residual() {
    let polynomial = MultiPoly {
        terms: vec![term(1, &[1, 2])],
    };
    let pins = [pin(3, 1)];
    assert!(substitute_pins(&polynomial, &pin_map(&pins)).is_none());
}

#[test]
fn intervals_detect_empty_and_sample_strict_ranges() {
    let mut empty = Interval::unbounded();
    assert!(empty.tighten(&BigRational::from_integer(2.into()), Rel::Ge));
    assert!(!empty.tighten(&BigRational::one(), Rel::Le));

    let mut strict = Interval::unbounded();
    assert!(strict.tighten(&BigRational::zero(), Rel::Gt));
    assert!(strict.tighten(&BigRational::from_integer(2.into()), Rel::Lt));
    let sample = strict.sample().expect("nonempty strict interval");
    assert!(sample > BigRational::zero());
    assert!(sample < BigRational::from_integer(2.into()));
    assert!(!strict.tighten(&BigRational::zero(), Rel::Ne));
}

#[test]
fn private_lra_residual_preserves_strict_bounds_and_model_values() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let mut linear = ay_lra::LraSolver::new(&terms);
    linear.set_combined_theory_mode(true);
    let vx = linear.ensure_var_registered(x);
    let vy = linear.ensure_var_registered(y);
    linear.assert_linear_bound(
        &[(vx, BigRational::one()), (vy, BigRational::one())],
        &BigRational::from_integer(3.into()),
        true,
        false,
        x,
    );
    linear.assert_linear_bound(
        &[(vx, BigRational::one())],
        &BigRational::one(),
        false,
        false,
        x,
    );
    linear.assert_linear_bound(
        &[(vy, BigRational::one())],
        &BigRational::zero(),
        true,
        true,
        y,
    );
    assert!(matches!(
        linear.check(),
        TheoryResult::Sat | TheoryResult::Unknown
    ));
    let xv = linear.get_value(x).expect("x value");
    let yv = linear.get_value(y).expect("y value");
    assert!(&xv + &yv >= BigRational::from_integer(3.into()));
    assert!(xv <= BigRational::one());
    assert!(yv > BigRational::zero());
}

/// Pin the exact negative boundary that requires [`Interval`]: a bare private
/// simplex with only direct bounds does not notice a contradiction on a
/// row-less variable.
#[test]
fn bare_lra_solver_misses_a_row_less_bound_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let mut linear = ay_lra::LraSolver::new(&terms);
    linear.set_combined_theory_mode(true);
    let vx = linear.ensure_var_registered(x);
    linear.assert_linear_bound(
        &[(vx, BigRational::one())],
        &BigRational::from_integer(2.into()),
        true,
        false,
        x,
    );
    linear.assert_linear_bound(
        &[(vx, BigRational::one())],
        &BigRational::one(),
        false,
        false,
        x,
    );

    assert!(matches!(linear.check(), TheoryResult::Sat));
    assert_eq!(
        linear.get_value(x),
        Some(BigRational::from_integer(2.into())),
        "documented row-less gap must remain explicit; residuals use Interval"
    );
}

#[test]
fn grounding_plan_fails_closed_on_division() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(BigRational::one());
    let product = terms.mk_mul(vec![x, y]);
    let division = terms.mk_div(x, y);
    let product_eq = terms.mk_eq(product, one);
    let division_eq = terms.mk_eq(division, one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(product_eq, true);
    solver.assert_literal(division_eq, true);
    assert!(solver.build_grounding_plan().is_none());
}

#[test]
fn grounding_plan_fails_closed_on_unsupported_arithmetic() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(BigRational::one());
    let product = terms.mk_mul(vec![x, y]);
    let absolute = terms.mk_abs(x);
    let product_eq = terms.mk_eq(product, one);
    let abs_eq = terms.mk_eq(absolute, one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(product_eq, true);
    solver.assert_literal(abs_eq, true);
    assert!(solver.build_grounding_plan().is_none());
}

/// An `Int`-sorted factor must take the whole plan down.
///
/// The Real control is what makes this a test of the SORT and not of the
/// shape: the identical bilinear system over `Real` variables does produce a
/// plan, so the only thing separating the two is the guard.
#[test]
fn grounding_plan_fails_closed_on_an_integer_sorted_factor() {
    let plan_for = |sort: Sort| {
        let mut terms = TermStore::new();
        let left = terms.mk_var("left", sort.clone());
        let right = terms.mk_var("right", sort.clone());
        let six = match sort {
            Sort::Int => terms.mk_int(BigInt::from(6)),
            _ => terms.mk_rational(BigRational::from_integer(BigInt::from(6))),
        };
        let product = terms.mk_mul(vec![left, right]);
        let atom = terms.mk_eq(product, six);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(atom, true);
        solver.build_grounding_plan().is_some()
    };
    assert!(plan_for(Sort::Real), "Real control must plan");
    assert!(
        !plan_for(Sort::Int),
        "an Int factor has no rational witness: fail closed"
    );
}

#[test]
fn grounded_model_overwrites_representative_and_scaled_alias_auxiliaries() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let two = terms.mk_rational(BigRational::from_integer(2.into()));
    let bare = terms.mk_mul(vec![x, y]);
    let scaled = terms.mk_mul(vec![two, x, y]);
    let bare_atom = terms.mk_ge(bare, zero);
    let scaled_atom = terms.mk_ge(scaled, zero);

    let mut solver = NraSolver::new(&terms);
    solver.internalize_atom(bare_atom);
    solver.internalize_atom(scaled_atom);
    assert_eq!(solver.products().count(), 2);

    let stale = BigRational::from_integer(999.into());
    assert!(solver.install_grounded_model(vec![
        (x, BigRational::from_integer(3.into())),
        (y, BigRational::from_integer(5.into())),
        (bare, stale.clone()),
        (scaled, -stale),
    ]));
    assert_eq!(
        solver.var_value(bare),
        Some(BigRational::from_integer(15.into()))
    );
    assert_eq!(
        solver.var_value(scaled),
        Some(BigRational::from_integer(30.into()))
    );
}

#[test]
fn original_atom_gate_rejects_a_relaxed_disequality_candidate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(BigRational::one());
    let product = terms.mk_mul(vec![x, y]);
    let product_eq_one = terms.mk_eq(product, one);
    let y_eq_one = terms.mk_eq(y, one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(product_eq_one, true);
    solver.assert_literal(y_eq_one, false);
    let plan = solver.build_grounding_plan().expect("bilinear plan");

    // Pinning x=1 makes the exact residual choose y=1. The disequality is not
    // a linear half-space and is intentionally relaxed by the private LRA, so
    // only verification of the ORIGINAL atom can reject this candidate.
    assert!(solve_grounded_residual(&solver, &[(x, BigRational::one())], &plan).is_none());
}

#[test]
fn polynomial_preflight_rejects_deep_and_explosive_terms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let mut deep = x;
    for _ in 0..=MAX_TERM_DEPTH {
        deep = terms.mk_app(Symbol::Named("-".into()), [deep], Sort::Real);
    }
    let solver = NraSolver::new(&terms);
    assert!(solver
        .inspect_arithmetic_term(deep, &mut Vec::new())
        .is_none());

    let mut terms = TermStore::new();
    let mut factors = Vec::new();
    for index in 0..13 {
        let a = terms.mk_var(format!("a{index}"), Sort::Real);
        let b = terms.mk_var(format!("b{index}"), Sort::Real);
        factors.push(terms.mk_app(Symbol::Named("+".into()), [a, b], Sort::Real));
    }
    let explosive = terms.mk_app(Symbol::Named("*".into()), factors, Sort::Real);
    let solver = NraSolver::new(&terms);
    assert!(solver
        .inspect_arithmetic_term(explosive, &mut Vec::new())
        .is_none());
}

#[test]
fn snap_order_prefers_exact_model_then_integer_then_zero() {
    assert_eq!(
        PinSnap::ORDERED,
        [PinSnap::Model, PinSnap::Integer, PinSnap::Zero]
    );
    let value = BigRational::new(7.into(), 2.into());
    assert_eq!(PinSnap::Model.apply(value.clone()), value);
    assert_eq!(
        PinSnap::Integer.apply(value.clone()),
        BigRational::from_integer(4.into())
    );
    assert!(PinSnap::Zero.apply(value).is_zero());
}

#[test]
fn grounding_schedule_is_dense_then_sparse_in_iteration_order() {
    let iterations: Vec<usize> = (0..=32).filter(|&iteration| scheduled(iteration)).collect();
    assert_eq!(iterations, vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 16, 24, 32]);
}

/// Full theory-solver regression for the targeted template shape.  The LRA
/// relaxation can satisfy the two product sums with opaque auxiliary values
/// while all four factors sit at unrelated defaults.  Grounding pins the
/// multiplier side and solves the template side exactly; the test-only counter
/// proves this was not discharged by another NRA pre-phase.
#[test]
fn model_guided_grounding_turns_bilinear_template_system_sat() {
    let mut terms = TermStore::new();
    let multipliers: Vec<TermId> = (0..7)
        .map(|index| terms.mk_var(format!("m{index}"), Sort::Real))
        .collect();
    let templates: Vec<TermId> = (0..7)
        .map(|index| terms.mk_var(format!("t{index}"), Sort::Real))
        .collect();
    let one = terms.mk_rational(BigRational::one());
    let multiplier_sum = terms.mk_add(multipliers.clone());
    let normalize = terms.mk_eq(multiplier_sum, one);
    let mut template_atoms = Vec::new();
    for shift in 0..7 {
        let products: Vec<TermId> = (0..7)
            .map(|index| terms.mk_mul(vec![multipliers[index], templates[(index + shift) % 7]]))
            .collect();
        let sum = terms.mk_add(products);
        let target = terms.mk_rational(BigRational::from_integer(BigInt::from((shift + 1) as i64)));
        template_atoms.push(terms.mk_eq(sum, target));
    }

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(normalize, true);
    for atom in template_atoms {
        solver.assert_literal(atom, true);
    }
    assert!(matches!(
        solver.try_linear_substitution_decide(),
        crate::univariate::UniResult::Unknown
    ));
    assert!(matches!(
        solver.try_univariate_decide(),
        crate::univariate::UniResult::Unknown
    ));
    assert!(matches!(
        solver.try_multivariate_witness_search(),
        crate::univariate::UniResult::Unknown
    ));
    assert!(matches!(
        solver.try_icp_branch_and_prune(),
        crate::univariate::UniResult::Unknown
    ));
    reset_test_successes();
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat), "got {result:?}");
    assert_eq!(
        test_successes(),
        1,
        "the regression must exercise model-guided grounding"
    );
}

#[cfg(test)]
#[path = "tests/live_refinement.rs"]
mod live_refinement;
