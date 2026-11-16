// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{Bound, InfRational};
use ay_core::{Sort, TermStore};
use ay_core::{TheoryResult, TheorySolver};

#[test]
fn fractional_integer_bound_shift_cuts_preserve_integer_witnesses() {
    // x = 3*y/2 - 2, y >= 5/3 has integer witness (x,y)=(1,2).
    // Treating y-5/3 as integer yields y >= 8/3 and cuts that witness off.
    // Reflect both variables for the upper-bound case.
    for direction in [BoundType::Lower, BoundType::Upper] {
        let sign = if direction == BoundType::Lower { 1 } else { -1 };
        let bound = BigRational::new((sign * 5).into(), 3.into());
        let constant = BigRational::from_integer((-sign * 2).into());
        let coefficient = BigRational::new(3.into(), 2.into());
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let mut solver = LraSolver::new(&terms);
        let x_var = solver.ensure_var_registered(x);
        let y_var = solver.ensure_var_registered(y);
        solver.rows.push(TableauRow::new(
            x_var,
            vec![(y_var, coefficient.clone())],
            constant.clone(),
        ));
        solver.vars[x_var as usize].status = Some(VarStatus::Basic(0));
        solver.vars[x_var as usize].value =
            InfRational::from_rational(&coefficient * &bound + &constant);
        solver.vars[y_var as usize].status = Some(VarStatus::NonBasic);
        solver.vars[y_var as usize].value = InfRational::from_rational(bound.clone());
        let active = Some(Bound::without_reasons(bound.clone().into(), false));
        match direction {
            BoundType::Lower => solver.vars[y_var as usize].lower = active,
            BoundType::Upper => solver.vars[y_var as usize].upper = active,
        }
        let integer_vars: HashSet<_> = [x, y].into_iter().collect();
        let cuts = solver.generate_gomory_cuts(&integer_vars);
        assert!(!cuts.is_empty(), "a valid separating cut remains available");
        for cut in &cuts {
            assert!(solver.current_solution_violates_cut(cut));
            for y_value in -8..=8 {
                let y_value = BigRational::from_integer(y_value.into());
                if (direction == BoundType::Lower && y_value < bound)
                    || (direction == BoundType::Upper && y_value > bound)
                {
                    continue;
                }
                let x_value = &coefficient * &y_value + &constant;
                if !x_value.is_integer() {
                    continue;
                }
                let lhs: BigRational = cut
                    .coeffs
                    .iter()
                    .map(|(var, coeff)| {
                        let value = if *var == y_var {
                            &y_value
                        } else {
                            assert_eq!(*var, x_var);
                            &x_value
                        };
                        coeff * value
                    })
                    .sum();
                assert!(
                    cut.is_lower && lhs >= cut.bound,
                    "valid integer point ({x_value},{y_value}) excluded by {cut:?}"
                );
            }
        }
    }
}

#[test]
fn fractional_integer_bound_term_cuts_keep_witness_and_complete_guards() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    let four = terms.mk_int(4.into());
    let five = terms.mk_int(5.into());
    let two_x = terms.mk_mul(vec![two, x]);
    let three_y = terms.mk_mul(vec![three, y]);
    let rhs = terms.mk_sub(vec![three_y, four]);
    let equation = terms.mk_eq(two_x, rhs);
    let lower = terms.mk_ge(three_y, five);
    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(equation, true);
    solver.assert_literal(lower, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    let cuts = solver.gomory_term_cuts(4);
    assert!(
        !cuts.is_empty(),
        "fractional shifts retain valid guarded cuts"
    );
    for cut in cuts {
        assert!(cut.reasons.contains(&(equation, true)), "{cut:?}");
        assert!(cut.reasons.contains(&(lower, true)), "{cut:?}");
        let lhs: BigInt = cut
            .coeffs
            .iter()
            .map(|(term, coeff)| {
                let value = if *term == x {
                    1
                } else {
                    assert_eq!(*term, y);
                    2
                };
                coeff * value
            })
            .sum();
        assert!(
            lhs >= cut.bound,
            "integer witness (1,2) excluded by {cut:?}"
        );
    }
}
