// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn constraint(coeffs: &[(u32, i64)], rhs: i64) -> Constraint {
    Constraint {
        coeffs: coeffs
            .iter()
            .map(|(v, c)| (VarId(*v), BigInt::from(*c)))
            .collect(),
        rhs: BigInt::from(rhs),
    }
}

fn bounds(vars: &[(u32, i64, i64)]) -> Vec<(VarId, BigInt, BigInt)> {
    vars.iter()
        .map(|(v, lb, ub)| (VarId(*v), BigInt::from(*lb), BigInt::from(*ub)))
        .collect()
}

#[test]
fn test_solve_ilp_sat() {
    // x + y <= 10, x >= 1, y >= 1
    let constraints = vec![
        constraint(&[(0, 1), (1, 1)], 10),
        constraint(&[(0, -1)], -1),
        constraint(&[(1, -1)], -1),
    ];
    let initial = bounds(&[(0, 0, 100), (1, 0, 100)]);

    let result = solve_ilp(constraints, 2, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let x = &model[&VarId(0)];
            let y = &model[&VarId(1)];
            assert!(x + y <= BigInt::from(10), "x={x}, y={y}");
            assert!(x >= &BigInt::from(1), "x={x}");
            assert!(y >= &BigInt::from(1), "y={y}");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_solve_ilp_unsat() {
    // x + y <= 3, x >= 2, y >= 2 (infeasible: 2+2=4 > 3)
    let constraints = vec![
        constraint(&[(0, 1), (1, 1)], 3),
        constraint(&[(0, -1)], -2),
        constraint(&[(1, -1)], -2),
    ];
    let initial = bounds(&[(0, 0, 100), (1, 0, 100)]);

    let result = solve_ilp(constraints, 2, &initial);
    assert!(matches!(result, IntSatResult::Unsat));
}

#[test]
fn test_solve_ilp_equality() {
    // x + y = 5 (encoded as x+y <= 5 AND -x-y <= -5)
    // x >= 0, y >= 0
    let constraints = vec![
        constraint(&[(0, 1), (1, 1)], 5),
        constraint(&[(0, -1), (1, -1)], -5),
        constraint(&[(0, -1)], 0),
        constraint(&[(1, -1)], 0),
    ];
    let initial = bounds(&[(0, 0, 10), (1, 0, 10)]);

    let result = solve_ilp(constraints, 2, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let x = &model[&VarId(0)];
            let y = &model[&VarId(1)];
            assert_eq!(x + y, BigInt::from(5), "x={x}, y={y}");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_gcd_normalization_infeasibility() {
    // 2x + 2y <= 3 normalizes to x + y <= 1 (GCD=2, floor(3/2)=1)
    // x >= 1, y >= 1 => x+y >= 2 > 1 => UNSAT
    let constraints = vec![
        constraint(&[(0, 2), (1, 2)], 3),
        constraint(&[(0, -1)], -1),
        constraint(&[(1, -1)], -1),
    ];
    let initial = bounds(&[(0, 0, 100), (1, 0, 100)]);

    let result = solve_ilp(constraints, 2, &initial);
    assert!(matches!(result, IntSatResult::Unsat));
}

#[test]
fn test_three_variable() {
    // x + y + z <= 10, x >= 2, y >= 3, z >= 4
    let constraints = vec![
        constraint(&[(0, 1), (1, 1), (2, 1)], 10),
        constraint(&[(0, -1)], -2),
        constraint(&[(1, -1)], -3),
        constraint(&[(2, -1)], -4),
    ];
    let initial = bounds(&[(0, 0, 20), (1, 0, 20), (2, 0, 20)]);

    let result = solve_ilp(constraints, 3, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let x = &model[&VarId(0)];
            let y = &model[&VarId(1)];
            let z = &model[&VarId(2)];
            assert!(x + y + z <= BigInt::from(10));
            assert!(x >= &BigInt::from(2));
            assert!(y >= &BigInt::from(3));
            assert!(z >= &BigInt::from(4));
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_single_variable_defined() {
    // x = 7: x <= 7 AND -x <= -7
    let constraints = vec![constraint(&[(0, 1)], 7), constraint(&[(0, -1)], -7)];
    let initial = bounds(&[(0, 0, 100)]);

    let result = solve_ilp(constraints, 1, &initial);
    match result {
        IntSatResult::Sat(model) => {
            assert_eq!(model[&VarId(0)], BigInt::from(7));
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// --- Larger problems (5+ variables) ---

#[test]
fn test_five_variable_sat() {
    // Sum of 5 vars <= 20, each >= 1
    let constraints = vec![
        constraint(&[(0, 1), (1, 1), (2, 1), (3, 1), (4, 1)], 20),
        constraint(&[(0, -1)], -1),
        constraint(&[(1, -1)], -1),
        constraint(&[(2, -1)], -1),
        constraint(&[(3, -1)], -1),
        constraint(&[(4, -1)], -1),
    ];
    let initial = bounds(&[(0, 0, 20), (1, 0, 20), (2, 0, 20), (3, 0, 20), (4, 0, 20)]);

    let result = solve_ilp(constraints, 5, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let sum: BigInt = (0..5).map(|i| model[&VarId(i)].clone()).sum();
            assert!(sum <= BigInt::from(20), "sum = {sum}");
            for i in 0..5 {
                assert!(model[&VarId(i)] >= BigInt::from(1));
            }
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_five_variable_tight_unsat() {
    // Sum of 5 vars <= 4, each >= 1. Since 5*1=5 > 4, UNSAT.
    let constraints = vec![
        constraint(&[(0, 1), (1, 1), (2, 1), (3, 1), (4, 1)], 4),
        constraint(&[(0, -1)], -1),
        constraint(&[(1, -1)], -1),
        constraint(&[(2, -1)], -1),
        constraint(&[(3, -1)], -1),
        constraint(&[(4, -1)], -1),
    ];
    let initial = bounds(&[(0, 0, 20), (1, 0, 20), (2, 0, 20), (3, 0, 20), (4, 0, 20)]);

    let result = solve_ilp(constraints, 5, &initial);
    assert!(matches!(result, IntSatResult::Unsat));
}

#[test]
fn test_six_variable_mixed_coefficients() {
    // 2x0 - 3x1 + x2 - x3 + 4x4 - 2x5 <= 10
    // -2x0 + 3x1 - x2 + x3 - 4x4 + 2x5 <= 10 (i.e., expression >= -10)
    // Each var in [0, 5]
    let constraints = vec![
        constraint(&[(0, 2), (1, -3), (2, 1), (3, -1), (4, 4), (5, -2)], 10),
        constraint(&[(0, -2), (1, 3), (2, -1), (3, 1), (4, -4), (5, 2)], 10),
    ];
    let initial = bounds(&[
        (0, 0, 5),
        (1, 0, 5),
        (2, 0, 5),
        (3, 0, 5),
        (4, 0, 5),
        (5, 0, 5),
    ]);

    let result = solve_ilp(constraints, 6, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let expr: BigInt = BigInt::from(2) * &model[&VarId(0)]
                - BigInt::from(3) * &model[&VarId(1)]
                + &model[&VarId(2)]
                - &model[&VarId(3)]
                + BigInt::from(4) * &model[&VarId(4)]
                - BigInt::from(2) * &model[&VarId(5)];
            assert!(expr <= BigInt::from(10), "expr = {expr}");
            assert!(expr >= BigInt::from(-10), "expr = {expr}");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// --- Problems requiring backtracking ---

#[test]
fn test_backtracking_required() {
    // x + y <= 3, x + y >= 3 (so x+y = 3)
    // 2x - y <= 4
    // -2x + y <= 1 (so y - 2x <= 1)
    // x, y in [0, 10]
    //
    // x+y = 3 and y-2x <= 1 => 3-x-2x <= 1 => 3-3x <= 1 => x >= 2/3 => x >= 1
    // Also 2x-y <= 4 and y = 3-x => 2x-(3-x) <= 4 => 3x <= 7 => x <= 2
    // So x in {1,2} and y = 3-x in {1,2}
    let constraints = vec![
        constraint(&[(0, 1), (1, 1)], 3),
        constraint(&[(0, -1), (1, -1)], -3),
        constraint(&[(0, 2), (1, -1)], 4),
        constraint(&[(0, -2), (1, 1)], 1),
    ];
    let initial = bounds(&[(0, 0, 10), (1, 0, 10)]);

    let result = solve_ilp(constraints, 2, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let x = &model[&VarId(0)];
            let y = &model[&VarId(1)];
            assert_eq!(x + y, BigInt::from(3));
            assert!(BigInt::from(2) * x - y <= BigInt::from(4));
            assert!(y - BigInt::from(2) * x <= BigInt::from(1));
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// --- GCD normalization edge cases ---

#[test]
fn test_large_gcd_normalization() {
    // 12x + 18y <= 29 normalizes to 2x + 3y <= 4 (GCD=6, floor(29/6)=4)
    // x >= 0, y >= 0
    let constraints = vec![
        constraint(&[(0, 12), (1, 18)], 29),
        constraint(&[(0, -1)], 0),
        constraint(&[(1, -1)], 0),
    ];
    let initial = bounds(&[(0, 0, 10), (1, 0, 10)]);

    let result = solve_ilp(constraints, 2, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let x = &model[&VarId(0)];
            let y = &model[&VarId(1)];
            assert!(
                BigInt::from(12) * x + BigInt::from(18) * y <= BigInt::from(29),
                "12*{x} + 18*{y} > 29"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_gcd_makes_unsat() {
    // 6x + 6y <= 5 normalizes to x + y <= 0 (GCD=6, floor(5/6)=0)
    // x >= 1 => UNSAT (x+y >= 1 > 0)
    let constraints = vec![
        constraint(&[(0, 6), (1, 6)], 5),
        constraint(&[(0, -1)], -1),
        constraint(&[(1, -1)], 0),
    ];
    let initial = bounds(&[(0, 0, 100), (1, 0, 100)]);

    let result = solve_ilp(constraints, 2, &initial);
    assert!(matches!(result, IntSatResult::Unsat));
}

// --- Corner solution tests ---

#[test]
fn test_corner_solution() {
    // x + y <= 10, x >= 0, y >= 0
    // x + y >= 10 (i.e., -x - y <= -10)
    // Solution must be on the face x + y = 10.
    let constraints = vec![
        constraint(&[(0, 1), (1, 1)], 10),
        constraint(&[(0, -1), (1, -1)], -10),
        constraint(&[(0, -1)], 0),
        constraint(&[(1, -1)], 0),
    ];
    let initial = bounds(&[(0, 0, 10), (1, 0, 10)]);

    let result = solve_ilp(constraints, 2, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let x = &model[&VarId(0)];
            let y = &model[&VarId(1)];
            assert_eq!(x + y, BigInt::from(10));
            assert!(x >= &BigInt::from(0));
            assert!(y >= &BigInt::from(0));
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// --- Degenerate cases ---

#[test]
fn test_empty_constraints() {
    // No constraints, just bounds: x in [3, 3]
    let constraints = vec![];
    let initial = bounds(&[(0, 3, 3)]);

    let result = solve_ilp(constraints, 1, &initial);
    match result {
        IntSatResult::Sat(model) => {
            assert_eq!(model[&VarId(0)], BigInt::from(3));
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_conflicting_initial_bounds() {
    // x in [5, 3] (impossible: lower > upper)
    // With constraint -x <= -5 and x <= 3
    let constraints = vec![constraint(&[(0, -1)], -5), constraint(&[(0, 1)], 3)];
    let initial = bounds(&[(0, 0, 100)]);

    let result = solve_ilp(constraints, 1, &initial);
    assert!(matches!(result, IntSatResult::Unsat));
}

#[test]
fn test_single_constraint_sat() {
    // 3x <= 15, x in [0, 10] => x <= 5
    let constraints = vec![constraint(&[(0, 3)], 15)];
    let initial = bounds(&[(0, 0, 10)]);

    let result = solve_ilp(constraints, 1, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let x = &model[&VarId(0)];
            assert!(BigInt::from(3) * x <= BigInt::from(15));
            assert!(x >= &BigInt::from(0));
            assert!(x <= &BigInt::from(10));
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// --- Mixed positive/negative coefficients ---

#[test]
fn test_difference_constraint() {
    // x - y <= 2, -x + y <= 3, x in [0, 10], y in [0, 10]
    // This means -3 <= x - y <= 2.
    let constraints = vec![
        constraint(&[(0, 1), (1, -1)], 2),
        constraint(&[(0, -1), (1, 1)], 3),
    ];
    let initial = bounds(&[(0, 0, 10), (1, 0, 10)]);

    let result = solve_ilp(constraints, 2, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let x = &model[&VarId(0)];
            let y = &model[&VarId(1)];
            assert!(x - y <= BigInt::from(2), "x-y = {}", x - y);
            assert!(y - x <= BigInt::from(3), "y-x = {}", y - x);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_pigeon_hole_3_into_2() {
    // Pigeonhole: 3 pigeons into 2 holes. Each pigeon in exactly one hole.
    // Variables: p_ij = 1 if pigeon i is in hole j, 0 otherwise.
    // Encoding: p_ij in [0, 1], sum_j p_ij = 1 for each i, sum_i p_ij <= 1 for each j.
    //
    // Variables: p00=0, p01=1, p10=2, p11=3, p20=4, p21=5
    //
    // Pigeon 0: p00 + p01 = 1 => p00+p01 <= 1 and -p00-p01 <= -1
    // Pigeon 1: p10 + p11 = 1
    // Pigeon 2: p20 + p21 = 1
    // Hole 0: p00 + p10 + p20 <= 1
    // Hole 1: p01 + p11 + p21 <= 1
    let constraints = vec![
        // Pigeon 0 in exactly one hole
        constraint(&[(0, 1), (1, 1)], 1),
        constraint(&[(0, -1), (1, -1)], -1),
        // Pigeon 1 in exactly one hole
        constraint(&[(2, 1), (3, 1)], 1),
        constraint(&[(2, -1), (3, -1)], -1),
        // Pigeon 2 in exactly one hole
        constraint(&[(4, 1), (5, 1)], 1),
        constraint(&[(4, -1), (5, -1)], -1),
        // Hole 0 capacity
        constraint(&[(0, 1), (2, 1), (4, 1)], 1),
        // Hole 1 capacity
        constraint(&[(1, 1), (3, 1), (5, 1)], 1),
    ];
    let initial = bounds(&[
        (0, 0, 1),
        (1, 0, 1),
        (2, 0, 1),
        (3, 0, 1),
        (4, 0, 1),
        (5, 0, 1),
    ]);

    let result = solve_ilp(constraints, 6, &initial);
    assert!(matches!(result, IntSatResult::Unsat));
}

#[test]
fn test_negative_rhs() {
    // -x - y <= -10 means x + y >= 10
    // x <= 4, y <= 4 => x+y <= 8 < 10 => UNSAT
    let constraints = vec![
        constraint(&[(0, -1), (1, -1)], -10),
        constraint(&[(0, 1)], 4),
        constraint(&[(1, 1)], 4),
    ];
    let initial = bounds(&[(0, 0, 10), (1, 0, 10)]);

    let result = solve_ilp(constraints, 2, &initial);
    assert!(matches!(result, IntSatResult::Unsat));
}

#[test]
fn test_large_coefficient_sat() {
    // 100x + 200y <= 500, x >= 1, y >= 1
    // GCD(100, 200) = 100, normalizes to x + 2y <= 5
    // x=1, y=1 works: 1+2=3 <= 5
    let constraints = vec![
        constraint(&[(0, 100), (1, 200)], 500),
        constraint(&[(0, -1)], -1),
        constraint(&[(1, -1)], -1),
    ];
    let initial = bounds(&[(0, 0, 100), (1, 0, 100)]);

    let result = solve_ilp(constraints, 2, &initial);
    match result {
        IntSatResult::Sat(model) => {
            let x = &model[&VarId(0)];
            let y = &model[&VarId(1)];
            assert!(
                BigInt::from(100) * x + BigInt::from(200) * y <= BigInt::from(500),
                "100*{x} + 200*{y} > 500"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}
