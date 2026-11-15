// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::sos::budget::{MAX_SOS_COEFFICIENT_BITS, MAX_SOS_LP_CELLS, MAX_SOS_LP_UPDATES};
use num_bigint::BigInt;

mod progress;

fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

#[test]
fn phase1_finds_an_exact_rational_solution() {
    let a = vec![vec![rational(2, 1), one()], vec![one(), rational(3, 1)]];
    let b = vec![one(), one()];
    let solution = lp_phase1_feasible(a.clone(), b.clone(), 2).expect("feasible rational system");
    assert_eq!(solution, vec![rational(2, 5), rational(1, 5)]);
    for (row, rhs) in a.iter().zip(&b) {
        let value: BigRational = row.iter().zip(&solution).map(|(a, x)| a * x).sum();
        assert_eq!(&value, rhs);
    }
    assert!(solution.iter().all(|value| !value.is_negative()));
}

#[test]
fn phase1_normalizes_negative_rhs_exactly() {
    assert_eq!(
        lp_phase1_feasible(vec![vec![rational(-2, 1)]], vec![-one()], 1),
        Some(vec![rational(1, 2)]),
    );
}

#[test]
fn phase1_declines_infeasible_nonnegative_and_conflicting_systems() {
    assert!(lp_phase1_feasible(vec![vec![-one()]], vec![one()], 1).is_none());
    assert!(lp_phase1_feasible(
        vec![vec![one()], vec![one()]],
        vec![one(), rational(2, 1)],
        1
    )
    .is_none());
    assert!(lp_phase1_feasible(vec![vec![]], vec![one()], 0).is_none());
}

#[test]
fn phase1_handles_redundant_zero_and_degenerate_rows() {
    assert_eq!(
        lp_phase1_feasible(vec![vec![]], vec![zero()], 0),
        Some(vec![])
    );
    assert_eq!(
        lp_phase1_feasible(vec![], vec![], 2),
        Some(vec![zero(), zero()])
    );
    let a = vec![
        vec![one(), one(), zero()],
        vec![one(), zero(), one()],
        vec![zero(); 3],
    ];
    assert_eq!(
        lp_phase1_feasible(a, vec![one(), one(), zero()], 3),
        Some(vec![one(), zero(), zero()])
    );
}

#[test]
fn phase1_rejects_malformed_input_shapes() {
    assert!(lp_phase1_feasible(vec![vec![one()]], vec![], 1).is_none());
    assert!(lp_phase1_feasible(vec![], vec![zero()], 0).is_none());
    assert!(lp_phase1_feasible(vec![vec![]], vec![zero()], 1).is_none());
    assert!(lp_phase1_feasible(vec![vec![one(), one()]], vec![zero()], 1).is_none());
    assert!(lp_phase1_feasible(vec![vec![one()], vec![]], vec![zero(), zero()], 1).is_none());
}

#[test]
fn phase1_checks_the_exact_tableau_cell_boundary() {
    assert_eq!(128 * (383 + 128 + 1), MAX_SOS_LP_CELLS);
    assert!(lp_phase1_feasible(vec![vec![zero(); 383]; 128], vec![zero(); 128], 383).is_some());
    assert!(lp_phase1_feasible(vec![vec![zero(); 384]; 128], vec![zero(); 128], 384).is_none());
    assert!(lp_phase1_feasible(vec![vec![zero()]; 256], vec![zero(); 256], 1).is_none());
    assert!(lp_phase1_feasible(vec![], vec![], usize::MAX).is_none());
}

#[test]
fn phase1_rejects_oversized_and_malformed_rationals() {
    let over_limit = BigRational::from_integer(BigInt::one() << MAX_SOS_COEFFICIENT_BITS as usize);
    let malformed = BigRational::new_raw(BigInt::one(), BigInt::zero());
    for value in [over_limit.clone(), over_limit.recip(), malformed] {
        assert!(lp_phase1_feasible(vec![vec![value.clone()]], vec![zero()], 1).is_none());
        assert!(lp_phase1_feasible(vec![vec![one()]], vec![value], 1).is_none());
    }
}

#[test]
fn ratio_ties_use_the_smallest_leaving_basis_index() {
    let tableau = vec![vec![one(), one()], vec![one(), one()]];
    assert_eq!(
        choose_leaving_row(&tableau, &[3, 2], 0, 1, &mut SosLpBudget::default()),
        Some(1)
    );
}

#[test]
fn exact_lp_helpers_decline_exhaustion_and_division_by_zero() {
    let mut exhausted = SosLpBudget::default();
    assert!(exhausted.charge_updates(MAX_SOS_LP_UPDATES));
    assert!(lp_add(&one(), &one(), &mut exhausted).is_none());
    assert!(lp_sub(&one(), &one(), &mut exhausted).is_none());
    assert!(lp_mul(&one(), &one(), &mut exhausted).is_none());
    assert!(lp_div(&one(), &one(), &mut exhausted).is_none());
    assert!(lp_neg(&one(), &mut exhausted).is_none());
    assert!(lp_div(&one(), &zero(), &mut SosLpBudget::default()).is_none());
}

#[test]
fn exact_lp_helpers_bound_inputs_and_intermediate_results() {
    let at_limit =
        BigRational::from_integer(BigInt::one() << (MAX_SOS_COEFFICIENT_BITS as usize - 1));
    let over_limit = &at_limit + &at_limit;
    assert!(lp_add(&at_limit, &at_limit, &mut SosLpBudget::default()).is_none());
    assert!(lp_mul(&at_limit, &at_limit, &mut SosLpBudget::default()).is_none());
    assert!(lp_sub(&over_limit, &over_limit, &mut SosLpBudget::default()).is_none());
    assert!(lp_mul(&over_limit, &zero(), &mut SosLpBudget::default()).is_none());
    assert_eq!(
        lp_sub(&at_limit, &at_limit, &mut SosLpBudget::default()),
        Some(zero())
    );
    assert_eq!(
        lp_mul(
            &rational(2, 3),
            &rational(9, 4),
            &mut SosLpBudget::default()
        ),
        Some(rational(3, 2))
    );
}
