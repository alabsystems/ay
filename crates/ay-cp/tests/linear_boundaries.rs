// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_cp::engine::CpSolveResult;
use ay_cp::propagator::Constraint;
use ay_cp::{CpSatEngine, Domain};

#[test]
fn linear_le_uses_exact_accumulation_beyond_i128() {
    let mut engine = CpSatEngine::new();
    let vars: Vec<_> = (0..3)
        .map(|index| engine.new_int_var(Domain::singleton(i64::MAX), Some(&format!("x{index}"))))
        .collect();
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![i64::MAX; 3],
        vars,
        rhs: i64::MAX,
    });

    assert!(matches!(engine.solve(), CpSolveResult::Unsat));
}

#[test]
fn linear_equality_negates_minimum_integer_exactly() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::singleton(1), Some("x"));
    engine.add_constraint(Constraint::LinearEq {
        coeffs: vec![i64::MIN],
        vars: vec![x],
        rhs: i64::MIN,
    });

    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));
}

#[test]
fn linear_ge_with_minimum_coefficient_detects_violation() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::singleton(2), Some("x"));
    engine.add_constraint(Constraint::LinearGe {
        coeffs: vec![i64::MIN],
        vars: vec![x],
        rhs: i64::MIN,
    });

    assert!(matches!(engine.solve(), CpSolveResult::Unsat));
}

#[test]
fn linear_not_equal_does_not_saturate_products() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::singleton(i64::MAX), Some("x"));
    engine.add_constraint(Constraint::LinearNotEqual {
        coeffs: vec![i64::MAX],
        vars: vec![x],
        rhs: i64::MAX,
    });

    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));
}

#[test]
fn linear_not_equal_can_exclude_maximum_integer() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(i64::MAX - 1, i64::MAX), Some("x"));
    engine.add_constraint(Constraint::LinearNotEqual {
        coeffs: vec![1],
        vars: vec![x],
        rhs: i64::MAX,
    });

    match engine.solve() {
        CpSolveResult::Sat(assignment) => {
            assert_eq!(
                assignment.iter().find(|(var, _)| *var == x),
                Some(&(x, i64::MAX - 1))
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn linear_not_equal_handles_minimum_i128_remainder() {
    let mut engine = CpSatEngine::new();
    let max = i64::MAX;
    let fixed_values = [max, max, max, 1];
    let fixed: Vec<_> = fixed_values
        .iter()
        .enumerate()
        .map(|(index, &value)| {
            engine.new_int_var(Domain::singleton(value), Some(&format!("fixed{index}")))
        })
        .collect();
    let x = engine.new_int_var(Domain::new(0, 1), Some("x"));

    // max*max + max*max + 4*max + 1 equals i128::MAX exactly. With rhs=-1,
    // the remainder for coefficient -1 is i128::MIN, whose mathematical
    // quotient is +2^127 and therefore cannot be an i64 forbidden value.
    let mut vars = fixed;
    vars.push(x);
    engine.add_constraint(Constraint::LinearNotEqual {
        coeffs: vec![max, max, 4, 1, -1],
        vars,
        rhs: -1,
    });

    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));
}
