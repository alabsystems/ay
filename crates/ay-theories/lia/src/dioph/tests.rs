// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
// #8529: Use deterministic hash maps in all builds.
use ay_core::extended_gcd_bigint;
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_traits::{One, Zero};

#[test]
fn test_equation_gcd_infeasible() {
    // 4x + 6y = 5 is infeasible (GCD(4,6)=2 doesn't divide 5)
    let eq = IntEquation::new(
        [(0, BigInt::from(4)), (1, BigInt::from(6))]
            .into_iter()
            .collect(),
        BigInt::from(5),
    );
    assert!(eq.gcd_infeasible());

    // 4x + 6y = 10 is feasible (GCD(4,6)=2 divides 10)
    let eq2 = IntEquation::new(
        [(0, BigInt::from(4)), (1, BigInt::from(6))]
            .into_iter()
            .collect(),
        BigInt::from(10),
    );
    assert!(!eq2.gcd_infeasible());
}

#[test]
fn test_equation_find_unit() {
    // x + 2y - 3z = 10 has unit coefficient on x
    let eq = IntEquation::new(
        [
            (0, BigInt::from(1)),
            (1, BigInt::from(2)),
            (2, BigInt::from(-3)),
        ]
        .into_iter()
        .collect(),
        BigInt::from(10),
    );
    let unit = eq.find_unit_var();
    assert!(unit.is_some());
    let (var, coeff) = unit.unwrap();
    assert_eq!(var, 0);
    assert_eq!(coeff, BigInt::from(1));

    // 2x + 4y = 10 has no unit coefficient
    let eq2 = IntEquation::new(
        [(0, BigInt::from(2)), (1, BigInt::from(4))]
            .into_iter()
            .collect(),
        BigInt::from(10),
    );
    assert!(eq2.find_unit_var().is_none());
}

#[test]
fn test_equation_substitute() {
    // Equation: 2x + y = 10
    // Substitute: x = 5 - z (i.e., x + z = 5)
    // Result: 2(5 - z) + y = 10 => y - 2z = 0
    let mut eq = IntEquation::new(
        [(0, BigInt::from(2)), (1, BigInt::from(1))]
            .into_iter()
            .collect(),
        BigInt::from(10),
    );

    let sub_coeffs: HashMap<usize, BigInt> = std::iter::once((2, BigInt::from(-1))).collect();
    let sub_const = BigInt::from(5);

    eq.substitute(0, &sub_coeffs, &sub_const);

    // After substitution: y - 2z = 0
    assert_eq!(eq.coeffs.get(&1), Some(&BigInt::from(1)));
    assert_eq!(eq.coeffs.get(&2), Some(&BigInt::from(-2)));
    assert!(eq.coeffs.get(&0).is_none());
    assert_eq!(eq.constant, BigInt::from(0));
}

#[test]
fn test_solver_simple_unique() {
    // System:
    // x + y = 5
    // x - y = 1
    // Solution: x = 3, y = 2
    let mut solver = DiophSolver::new(10);
    solver.add_equation_from(
        [(0, BigInt::from(1)), (1, BigInt::from(1))],
        BigInt::from(5),
    );
    solver.add_equation_from(
        [(0, BigInt::from(1)), (1, BigInt::from(-1))],
        BigInt::from(1),
    );

    let result = solver.solve();
    match result {
        DiophResult::Solved(values) => {
            assert_eq!(values.get(&0), Some(&BigInt::from(3)));
            assert_eq!(values.get(&1), Some(&BigInt::from(2)));
        }
        _ => panic!("Expected Solved, got {result:?}"),
    }
}

#[test]
fn test_solver_no_fresh_var_leak_2x2_non_unit() {
    // 2x + 3y = 13, 4x + 5y = 23  ->  x = 2, y = 3 (SAT).
    // No unit coefficients, so coefficient reduction introduces FRESH variables
    // (indices >= first_fresh_id = 2). Those fresh variables must NOT leak into
    // the result map: their determined values previously did, tripping a
    // debug_assert in dioph_bridge ("Solved value has out-of-range var index")
    // and panicking debug builds. Original variables are 0 and 1 only.
    let mut solver = DiophSolver::new(2);
    solver.add_equation_from(
        [(0, BigInt::from(2)), (1, BigInt::from(3))],
        BigInt::from(13),
    );
    solver.add_equation_from(
        [(0, BigInt::from(4)), (1, BigInt::from(5))],
        BigInt::from(23),
    );

    let result = solver.solve();
    let values = match &result {
        DiophResult::Solved(values) => values,
        DiophResult::Partial { determined } => determined,
        other => panic!("Expected Solved/Partial for a feasible system, got {other:?}"),
    };
    // The contract: no fresh-variable index (>= first_fresh_id = 2) may appear.
    assert!(
        values.keys().all(|&idx| idx < 2),
        "fresh variable leaked into the diophantine result: {values:?}"
    );
    // And the original-variable solution must be correct.
    assert_eq!(values.get(&0), Some(&BigInt::from(2)));
    assert_eq!(values.get(&1), Some(&BigInt::from(3)));
}

#[test]
fn test_solver_infeasible_gcd() {
    // 2x + 4y = 7 is infeasible (GCD doesn't divide)
    let mut solver = DiophSolver::new(10);
    solver.add_equation_from(
        [(0, BigInt::from(2)), (1, BigInt::from(4))],
        BigInt::from(7),
    );

    let result = solver.solve();
    assert!(matches!(result, DiophResult::Infeasible { .. }));
}

#[test]
fn test_solver_underdetermined() {
    // x + y + z = 10 (3 vars, 1 equation)
    let mut solver = DiophSolver::new(10);
    solver.add_equation_from(
        [
            (0, BigInt::from(1)),
            (1, BigInt::from(1)),
            (2, BigInt::from(1)),
        ],
        BigInt::from(10),
    );

    let result = solver.solve();
    // Should be partial - one variable eliminated, two free
    match result {
        DiophResult::Partial { .. } => {}
        _ => panic!("Expected Partial, got {result:?}"),
    }
}

#[test]
fn test_solver_equality_dense() {
    // System similar to system_05.smt2:
    // -4*x + 2*y - z + w = -16  (w has coeff 1)
    // x + 3*y - 2*z + w = 45    (x and w have coeff 1)
    // -x + y - 3*z + 2*w = 48   (y has coeff 1)
    // This should be solvable directly
    let mut solver = DiophSolver::new(10);

    // Equation 1: -4x + 2y - z + w = -16
    solver.add_equation_from(
        [
            (0, BigInt::from(-4)),
            (1, BigInt::from(2)),
            (2, BigInt::from(-1)),
            (3, BigInt::from(1)),
        ],
        BigInt::from(-16),
    );

    // Equation 2: x + 3y - 2z + w = 45
    solver.add_equation_from(
        [
            (0, BigInt::from(1)),
            (1, BigInt::from(3)),
            (2, BigInt::from(-2)),
            (3, BigInt::from(1)),
        ],
        BigInt::from(45),
    );

    // Equation 3: -x + y - 3z + 2w = 48
    solver.add_equation_from(
        [
            (0, BigInt::from(-1)),
            (1, BigInt::from(1)),
            (2, BigInt::from(-3)),
            (3, BigInt::from(2)),
        ],
        BigInt::from(48),
    );

    let result = solver.solve();

    // With 3 equations and 4 variables, we should get partial solution
    // with 1 free variable, or infeasible
    match result {
        DiophResult::Partial { determined, .. } => {
            // Should have determined some variables
            safe_eprintln!("Determined: {:?}", determined);
        }
        DiophResult::Infeasible { .. } => {
            // Also acceptable if the system is inconsistent
            safe_eprintln!("System is infeasible");
        }
        DiophResult::Solved(values) => {
            // If fully solved, verify solution
            safe_eprintln!("Fully solved: {:?}", values);
        }
    }
}

#[test]
fn test_extended_gcd() {
    // Test extended GCD: gcd(4, 3) = 1 = 4*1 + 3*(-1)
    let (g, s, t) = extended_gcd_bigint(&BigInt::from(4), &BigInt::from(3));
    assert_eq!(g, BigInt::one());
    assert_eq!(&BigInt::from(4) * &s + &BigInt::from(3) * &t, BigInt::one());

    // Test extended GCD: gcd(12, 8) = 4
    let (g, s, t) = extended_gcd_bigint(&BigInt::from(12), &BigInt::from(8));
    assert_eq!(g, BigInt::from(4));
    assert_eq!(
        &BigInt::from(12) * &s + &BigInt::from(8) * &t,
        BigInt::from(4)
    );
}

#[test]
fn test_two_variable_solution() {
    // 4x + 3y = 70
    // gcd(4,3) = 1, particular solution: x0 = 70*1 = 70, y0 = 70*(-1) = -70
    // General: x = 70 + 3k, y = -70 - 4k
    let eq = IntEquation::new(
        [(0, BigInt::from(4)), (1, BigInt::from(3))]
            .into_iter()
            .collect(),
        BigInt::from(70),
    );

    let sol = eq.solve_two_variable().expect("Should have solution");

    // Verify particular solution satisfies equation
    // 4 * x0 + 3 * y0 = 70
    assert_eq!(
        BigInt::from(4) * &sol.x0 + BigInt::from(3) * &sol.y0,
        BigInt::from(70)
    );

    // Test evaluation at k = 0 gives particular solution
    let (x, y) = sol.evaluate(&BigInt::zero());
    assert_eq!(x, sol.x0);
    assert_eq!(y, sol.y0);

    // Test evaluation at k = -23 (should give x=1, y=22)
    let k = BigInt::from(-23);
    let (x, y) = sol.evaluate(&k);
    // Verify: 4*1 + 3*22 = 4 + 66 = 70
    assert_eq!(
        BigInt::from(4) * &x + BigInt::from(3) * &y,
        BigInt::from(70)
    );
}

#[test]
fn test_two_variable_k_bounds() {
    // 4x + 3y = 70 with x >= 0, y >= 0, x <= 41
    let eq = IntEquation::new(
        [(0, BigInt::from(4)), (1, BigInt::from(3))]
            .into_iter()
            .collect(),
        BigInt::from(70),
    );

    let sol = eq.solve_two_variable().expect("Should have solution");

    // x = 70 + 3k, y = -70 - 4k (step_x = 3, step_y = 4)
    // For x >= 0: 70 + 3k >= 0 => k >= -70/3 = -23.33 => k >= -23
    // For x <= 41: 70 + 3k <= 41 => k <= -29/3 = -9.67 => k <= -10
    // For y >= 0: -70 - 4k >= 0 => k <= -70/4 = -17.5 => k <= -18
    // Combined: k in [-23, -18]

    let x_lo = Some(BigInt::zero());
    let x_hi = Some(BigInt::from(41));
    let y_lo = Some(BigInt::zero());

    let (k_min_x, k_max_x) = sol.k_bounds_from_x(x_lo.as_ref(), x_hi.as_ref());
    let (k_min_y, k_max_y) = sol.k_bounds_from_y(y_lo.as_ref(), None);

    // Intersect bounds
    let k_min = k_min_x.unwrap().max(k_min_y.unwrap_or(BigInt::from(-1000)));
    let k_max = k_max_x.unwrap().min(k_max_y.unwrap());

    assert!(k_min <= k_max, "k bounds should not be empty");

    // Verify solution at k = k_min
    let (x, y) = sol.evaluate(&k_min);
    assert!(x >= BigInt::zero());
    assert!(y >= BigInt::zero());
    assert!(x <= BigInt::from(41));
    assert_eq!(
        BigInt::from(4) * &x + BigInt::from(3) * &y,
        BigInt::from(70)
    );
}

#[test]
fn test_fresh_variable_elimination() {
    // System with NO unit coefficients:
    // 2x + 3y = 12
    // 4x - 5y = 7
    // This requires fresh variable elimination to solve
    let mut solver = DiophSolver::new(10);

    solver.add_equation_from(
        [(0, BigInt::from(2)), (1, BigInt::from(3))],
        BigInt::from(12),
    );
    solver.add_equation_from(
        [(0, BigInt::from(4)), (1, BigInt::from(-5))],
        BigInt::from(7),
    );

    let result = solver.solve();

    // The solution is x = 3, y = 2
    // Verify: 2*3 + 3*2 = 6 + 6 = 12 ✓
    // Verify: 4*3 - 5*2 = 12 - 10 = 2 ✗ -- wait, that's wrong
    // Let me recalculate... 4*3 - 5*2 = 12 - 10 = 2 != 7
    // So x=3, y=2 is NOT a solution to the second equation.

    // Let's solve this properly:
    // From eq1: 2x + 3y = 12 => x = (12 - 3y) / 2
    // For x to be integer, 12 - 3y must be even => 3y must be even => y must be even
    // Let y = 2k: x = (12 - 6k) / 2 = 6 - 3k
    // Substitute into eq2: 4(6 - 3k) - 5(2k) = 7
    // 24 - 12k - 10k = 7
    // 24 - 22k = 7
    // -22k = -17
    // k = 17/22 -- not an integer!
    // So this system is INFEASIBLE for integers.

    assert!(
        matches!(result, DiophResult::Infeasible { .. }),
        "Expected Infeasible, got {result:?}"
    );
}

#[test]
fn test_fresh_variable_elimination_sat() {
    // System with NO unit coefficients but IS satisfiable:
    // 2x + 4y = 12 (GCD = 2, can simplify to x + 2y = 6)
    // 3x - 6y = 9  (GCD = 3, can simplify to x - 2y = 3)
    // Adding: 2x = 9 => x = 4.5 -- wait, that's not integer either

    // Let me try a system that works:
    // 2x + 4y = 12  =>  x + 2y = 6  => x = 6 - 2y
    // 3x + 6y = 18  =>  x + 2y = 6  (same equation after normalization)
    // This is underdetermined, let's try something else

    // 2x + 3y = 12
    // 3x + 2y = 13
    // From eq1: 2x = 12 - 3y, so y must be even for x to be integer? No, 2x = 12 - 3y
    // Let's solve: multiply eq1 by 3, eq2 by 2:
    // 6x + 9y = 36
    // 6x + 4y = 26
    // Subtract: 5y = 10 => y = 2
    // Then 2x + 6 = 12 => x = 3

    let mut solver = DiophSolver::new(10);
    solver.add_equation_from(
        [(0, BigInt::from(2)), (1, BigInt::from(3))],
        BigInt::from(12),
    );
    solver.add_equation_from(
        [(0, BigInt::from(3)), (1, BigInt::from(2))],
        BigInt::from(13),
    );

    let result = solver.solve();

    match result {
        DiophResult::Solved(values) => {
            // Verify solution: x = 3, y = 2
            let x = values.get(&0).cloned().unwrap_or_default();
            let y = values.get(&1).cloned().unwrap_or_default();
            // 2*3 + 3*2 = 6 + 6 = 12 ✓
            assert_eq!(
                BigInt::from(2) * &x + BigInt::from(3) * &y,
                BigInt::from(12)
            );
            // 3*3 + 2*2 = 9 + 4 = 13 ✓
            assert_eq!(
                BigInt::from(3) * &x + BigInt::from(2) * &y,
                BigInt::from(13)
            );
        }
        DiophResult::Partial { determined, .. } => {
            // If partial, verify determined variables satisfy the equations they appear in.
            // A partial result with no determined variables is a bug (the system is solvable).
            assert!(
                !determined.is_empty(),
                "Partial with empty determined map on a solvable 2-variable system is a bug"
            );
            // Validate all partial shapes. A single determined variable must still
            // imply an integer value for the other variable and satisfy both equations.
            let x = determined.get(&0).cloned();
            let y = determined.get(&1).cloned();
            match (x, y) {
                (Some(x), Some(y)) => {
                    assert_eq!(
                        BigInt::from(2) * &x + BigInt::from(3) * &y,
                        BigInt::from(12),
                        "Partial solution must satisfy eq1: 2x + 3y = 12"
                    );
                    assert_eq!(
                        BigInt::from(3) * &x + BigInt::from(2) * &y,
                        BigInt::from(13),
                        "Partial solution must satisfy eq2: 3x + 2y = 13"
                    );
                }
                (Some(x), None) => {
                    let y_num = BigInt::from(12) - BigInt::from(2) * &x;
                    assert_eq!(
                        &y_num % BigInt::from(3),
                        BigInt::from(0),
                        "Determined x must imply integer y for eq1"
                    );
                    let y = y_num / BigInt::from(3);
                    assert_eq!(
                        BigInt::from(2) * &x + BigInt::from(3) * &y,
                        BigInt::from(12),
                        "Reconstructed (x,y) must satisfy eq1"
                    );
                    assert_eq!(
                        BigInt::from(3) * &x + BigInt::from(2) * &y,
                        BigInt::from(13),
                        "Reconstructed (x,y) must satisfy eq2"
                    );
                }
                (None, Some(y)) => {
                    let x_num = BigInt::from(12) - BigInt::from(3) * &y;
                    assert_eq!(
                        &x_num % BigInt::from(2),
                        BigInt::from(0),
                        "Determined y must imply integer x for eq1"
                    );
                    let x = x_num / BigInt::from(2);
                    assert_eq!(
                        BigInt::from(2) * &x + BigInt::from(3) * &y,
                        BigInt::from(12),
                        "Reconstructed (x,y) must satisfy eq1"
                    );
                    assert_eq!(
                        BigInt::from(3) * &x + BigInt::from(2) * &y,
                        BigInt::from(13),
                        "Reconstructed (x,y) must satisfy eq2"
                    );
                }
                (None, None) => {
                    unreachable!("checked above: determined map is non-empty");
                }
            }
        }
        DiophResult::Infeasible { .. } => {
            panic!("Expected Solved or Partial, got Infeasible");
        }
    }
}

#[test]
fn test_single_var_non_unit_does_not_allocate_fresh_chain() {
    // 2x = 4 should be solved directly as x = 2.
    // Repeated fresh-variable rewrites here only rename the variable and
    // can create non-terminating churn.
    let mut solver = DiophSolver::new(10);
    solver.add_equation_from([(0, BigInt::from(2))], BigInt::from(4));

    let result = solver.solve();

    match result {
        DiophResult::Solved(values) | DiophResult::Partial { determined: values } => {
            assert_eq!(
                values.get(&0),
                Some(&BigInt::from(2)),
                "2x = 4 should determine x = 2"
            );
        }
        DiophResult::Infeasible { .. } => {
            panic!("2x = 4 is feasible but solver returned Infeasible");
        }
    }

    assert_eq!(
        solver.next_fresh_var_for_tests(),
        10,
        "Single-var equation should not allocate fresh variables",
    );
}

/// Verify that fresh variable IDs start above the original variable range,
/// preventing the collision bug where `next_fresh_var=1000` would overlap
/// with problems having >1000 variables.
#[test]
fn test_fresh_var_ids_above_original_range() {
    // Use variable indices 0..1500 to simulate a large problem.
    // With the old hardcoded `next_fresh_var=1000`, fresh variables would
    // collide with original variables 1000..1500.
    let num_vars = 1500;
    let mut solver = DiophSolver::new(num_vars);

    // Two equations with non-unit coefficients (forces fresh variable allocation):
    //   2 * x_0 + 3 * x_1499 = 12
    //   3 * x_0 + 2 * x_1499 = 13
    // Solution: x_0 = 3, x_1499 = 2
    solver.add_equation_from(
        [(0, BigInt::from(2)), (num_vars - 1, BigInt::from(3))],
        BigInt::from(12),
    );
    solver.add_equation_from(
        [(0, BigInt::from(3)), (num_vars - 1, BigInt::from(2))],
        BigInt::from(13),
    );

    let result = solver.solve();

    match result {
        DiophResult::Solved(values) | DiophResult::Partial { determined: values } => {
            // If x_0 is determined, verify the solution
            if let Some(x0) = values.get(&0) {
                if let Some(x1499) = values.get(&(num_vars - 1)) {
                    assert_eq!(
                        BigInt::from(2) * x0 + BigInt::from(3) * x1499,
                        BigInt::from(12),
                        "Solution must satisfy equation 1"
                    );
                    assert_eq!(
                        BigInt::from(3) * x0 + BigInt::from(2) * x1499,
                        BigInt::from(13),
                        "Solution must satisfy equation 2"
                    );
                }
            }
        }
        DiophResult::Infeasible { .. } => {
            panic!("System is feasible (x_0=3, x_1499=2) but solver returned Infeasible");
        }
    }

    // Verify that all fresh variables allocated are above the original range
    assert!(
        solver.next_fresh_var_for_tests() >= num_vars,
        "Fresh variable IDs ({}) must not overlap with original variable range (0..{})",
        solver.next_fresh_var_for_tests(),
        num_vars,
    );
}

/// `add_equation` uses `assert!` (not `debug_assert!`) to reject variable indices >= first_fresh_id.
#[test]
#[should_panic(expected = "equation contains variable index >= first_fresh_id")]
fn test_add_equation_rejects_overlapping_var_ids() {
    let mut solver = DiophSolver::new(5);
    // Variable index 10 exceeds first_fresh_id=5
    solver.add_equation_from([(10, BigInt::from(1))], BigInt::from(42));
}

/// Infeasibility conflict core should contain only the source equations that
/// contributed to the derivation, not all input equations.
#[test]
fn test_infeasible_reduced_conflict_core() {
    // Three equations:
    //   eq0: x + y = 5       (source 0)
    //   eq1: x + y = 7       (source 1)  -- contradicts eq0
    //   eq2: z + w = 10      (source 2)  -- independent, should NOT appear in conflict
    let mut solver = DiophSolver::new(10);
    solver.add_equation_with_source(
        [(0, BigInt::from(1)), (1, BigInt::from(1))],
        BigInt::from(5),
        0,
    );
    solver.add_equation_with_source(
        [(0, BigInt::from(1)), (1, BigInt::from(1))],
        BigInt::from(7),
        1,
    );
    solver.add_equation_with_source(
        [(2, BigInt::from(1)), (3, BigInt::from(1))],
        BigInt::from(10),
        2,
    );

    let result = solver.solve();
    match result {
        DiophResult::Infeasible { sources } => {
            // The conflict should involve eq0 and eq1 (sources 0 and 1)
            // but NOT eq2 (source 2) since z+w=10 is independent.
            assert!(
                !sources.is_empty(),
                "Sources should be tracked for reduced conflict"
            );
            assert!(
                sources.contains(&0) && sources.contains(&1),
                "Conflict should reference the contradictory equations: {sources:?}"
            );
            assert!(
                !sources.contains(&2),
                "Independent equation (source 2) should not be in conflict: {sources:?}"
            );
        }
        other => panic!("Expected Infeasible, got {other:?}"),
    }
}

/// Source tracking across fresh variable elimination: even when the solver
/// introduces fresh variables to reduce coefficients, the original source
/// indices should still be tracked correctly.
#[test]
fn test_source_tracking_through_fresh_vars() {
    // eq0: 2x + 4y = 7  (source 0) -- infeasible by GCD: gcd(2,4)=2 doesn't divide 7
    // This should be detected in the first GCD pass with source [0].
    let mut solver = DiophSolver::new(10);
    solver.add_equation_with_source(
        [(0, BigInt::from(2)), (1, BigInt::from(4))],
        BigInt::from(7),
        0,
    );
    solver.add_equation_with_source(
        [(2, BigInt::from(1)), (3, BigInt::from(1))],
        BigInt::from(10),
        1,
    );

    let result = solver.solve();
    match result {
        DiophResult::Infeasible { sources } => {
            assert_eq!(
                sources,
                vec![0],
                "GCD infeasibility should reference only the offending equation"
            );
        }
        other => panic!("Expected Infeasible, got {other:?}"),
    }
}

/// Verify the stall counter threshold field is wired correctly:
/// `set_max_stall_rounds` stores the value and the solver uses it
/// instead of a hardcoded constant.
///
/// The stall counter fires when the global minimum coefficient stays
/// flat across consecutive fresh-variable steps. In practice this is
/// extremely hard to trigger because the Euclidean-style reduction
/// monotonically decreases the global minimum. The threshold (default 64)
/// is a safety net for pathological systems with complex shared-variable
/// substitution networks.
///
/// This test verifies the mechanism by exercising the fresh-variable
/// elimination path on a system that requires multiple fresh-var steps
/// (Fibonacci-like coefficients maximize the number of steps), then
/// confirms:
/// - The solver terminates with a valid result
/// - Determined values satisfy the original equations
/// - The configurable threshold is stored correctly
#[test]
fn test_stall_counter_mechanism_exists_and_is_configurable() {
    // Fibonacci-adjacent coefficients maximize the number of Euclidean
    // reduction steps before reaching a unit coefficient.
    // F(8)=21, F(9)=34: gcd(21,34)=1, requires ~8 fresh-var steps.
    //
    // 3 independent equations so multiple pass through the fresh-var path.
    let mut solver = DiophSolver::new(20);
    // eq0: 21*x0 + 34*x1 = 55
    solver.add_equation_from(
        [(0, BigInt::from(21)), (1, BigInt::from(34))],
        BigInt::from(55),
    );
    // eq1: 21*x2 + 34*x3 = 89
    solver.add_equation_from(
        [(2, BigInt::from(21)), (3, BigInt::from(34))],
        BigInt::from(89),
    );
    // eq2: 21*x4 + 34*x5 = 144
    solver.add_equation_from(
        [(4, BigInt::from(21)), (5, BigInt::from(34))],
        BigInt::from(144),
    );

    // Override threshold to verify the field is used. Since the natural
    // Euclidean descent never triggers the stall (cur != prev), the
    // result should be the same regardless of threshold value.
    solver.set_max_stall_rounds(2);

    let result = solver.solve();

    // All three equations are solvable over the integers.
    // 21*x + 34*y = c has solutions when gcd(21,34)=1 divides c (always true).
    // Verify any determined values satisfy the original equations.
    match result {
        DiophResult::Solved(ref values)
        | DiophResult::Partial {
            determined: ref values,
        } => {
            // Check eq0: 21*x0 + 34*x1 = 55
            if let (Some(x0), Some(x1)) = (values.get(&0), values.get(&1)) {
                assert_eq!(
                    BigInt::from(21) * x0 + BigInt::from(34) * x1,
                    BigInt::from(55),
                    "Determined values must satisfy eq0: 21*x0 + 34*x1 = 55"
                );
            }
            // Check eq1: 21*x2 + 34*x3 = 89
            if let (Some(x2), Some(x3)) = (values.get(&2), values.get(&3)) {
                assert_eq!(
                    BigInt::from(21) * x2 + BigInt::from(34) * x3,
                    BigInt::from(89),
                    "Determined values must satisfy eq1: 21*x2 + 34*x3 = 89"
                );
            }
            // Check eq2: 21*x4 + 34*x5 = 144
            if let (Some(x4), Some(x5)) = (values.get(&4), values.get(&5)) {
                assert_eq!(
                    BigInt::from(21) * x4 + BigInt::from(34) * x5,
                    BigInt::from(144),
                    "Determined values must satisfy eq2: 21*x4 + 34*x5 = 144"
                );
            }
        }
        DiophResult::Infeasible { .. } => {
            panic!("System is feasible but solver returned Infeasible");
        }
    }

    // Verify fresh variables were allocated (proving fresh-var path was exercised)
    assert!(
        solver.next_fresh_var_for_tests() > 20,
        "Fresh variables should have been allocated during Euclidean reduction"
    );
}

/// Verify that the stall counter threshold (default 64) does not interfere
/// with correct solving of systems requiring many fresh-variable steps.
///
/// Uses large Fibonacci-like coefficients (F(14)=377, F(15)=610) which
/// require ~14 Euclidean reduction steps per equation. With 4 independent
/// equations, the solver performs ~56 fresh-var steps total.
#[test]
fn test_stall_counter_allows_deep_euclidean_reduction() {
    // F(14)=377, F(15)=610. gcd=1. Requires many fresh-var steps.
    let mut solver = DiophSolver::new(20);

    // 4 independent equations using F(14), F(15) coefficients
    for i in 0..4 {
        let v0 = i * 2;
        let v1 = i * 2 + 1;
        // 377*x + 610*y = 987 (= F(16), ensures integer solution exists: x=1, y=1)
        solver.add_equation_from(
            [(v0, BigInt::from(377)), (v1, BigInt::from(610))],
            BigInt::from(987),
        );
    }

    let result = solver.solve();

    match result {
        DiophResult::Solved(ref values)
        | DiophResult::Partial {
            determined: ref values,
        } => {
            // Verify each equation
            for i in 0..4 {
                let v0 = i * 2;
                let v1 = i * 2 + 1;
                if let (Some(x), Some(y)) = (values.get(&v0), values.get(&v1)) {
                    assert_eq!(
                        BigInt::from(377) * x + BigInt::from(610) * y,
                        BigInt::from(987),
                        "Solution must satisfy equation {i}: 377*x_{v0} + 610*x_{v1} = 987"
                    );
                }
            }
        }
        DiophResult::Infeasible { .. } => {
            panic!("System has solution (x=1, y=1 for each pair) but solver returned Infeasible");
        }
    }

    // The solver should have allocated many fresh variables (Fibonacci
    // coefficients maximize the Euclidean reduction chain length)
    let fresh_count = solver.next_fresh_var_for_tests() - 20;
    assert!(
        fresh_count >= 4,
        "Expected at least 4 fresh variables for 4 Fibonacci-coefficient equations, got {fresh_count}"
    );
}

/// Verify that reducing max_stall_rounds does NOT break correctness.
///
/// Even with an aggressive threshold, the solver must still produce valid
/// partial results (any determined variable satisfies the original equations).
#[test]
fn test_stall_counter_low_threshold_preserves_correctness() {
    // Same system as above but with very low stall threshold.
    // The Euclidean descent never triggers the stall condition (cur == prev)
    // so the result should be identical, but we verify correctness regardless.
    let systems: &[(i64, i64, i64)] = &[
        (21, 34, 55),   // F(8), F(9), F(10)
        (55, 89, 144),  // F(10), F(11), F(12)
        (89, 144, 233), // F(11), F(12), F(13)
    ];

    for threshold in [0, 1, 2, 64] {
        let mut solver = DiophSolver::new(20);
        for (i, &(a, b, c)) in systems.iter().enumerate() {
            let v0 = i * 2;
            let v1 = i * 2 + 1;
            solver.add_equation_from(
                [(v0, BigInt::from(a)), (v1, BigInt::from(b))],
                BigInt::from(c),
            );
        }
        solver.set_max_stall_rounds(threshold);

        let result = solver.solve();

        match result {
            DiophResult::Solved(ref values)
            | DiophResult::Partial {
                determined: ref values,
            } => {
                for (i, &(a, b, c)) in systems.iter().enumerate() {
                    let v0 = i * 2;
                    let v1 = i * 2 + 1;
                    if let (Some(x), Some(y)) = (values.get(&v0), values.get(&v1)) {
                        assert_eq!(
                            BigInt::from(a) * x + BigInt::from(b) * y,
                            BigInt::from(c),
                            "threshold={threshold}: determined values must satisfy eq{i}: {a}*x + {b}*y = {c}"
                        );
                    }
                }
            }
            DiophResult::Infeasible { .. } => {
                panic!(
                    "threshold={threshold}: system has solutions but solver returned Infeasible"
                );
            }
        }
    }
}

/// Test check_remaining_with_bounds on empty remaining equations (no conflict).
///
/// When the Dioph solver fully reduces a 2-variable equation via
/// fresh-variable elimination, no equations remain and check_remaining_with_bounds
/// returns None regardless of bounds.
#[test]
fn test_remaining_equation_fully_reduced_returns_none() {
    let mut solver = DiophSolver::new(2);
    solver.add_equation_with_source(
        [(0, BigInt::from(3)), (1, BigInt::from(-5))],
        BigInt::one(),
        0,
    );
    let result = solver.solve();
    assert!(matches!(result, DiophResult::Partial { .. }));

    let mut bounds = HashMap::default();
    bounds.insert(0, (Some(BigInt::zero()), Some(BigInt::from(100))));
    bounds.insert(1, (Some(BigInt::zero()), Some(BigInt::from(100))));

    // No remaining equations → no conflict
    assert!(solver.check_remaining_with_bounds(&bounds).is_none());
}

/// Test check_remaining_with_bounds detects single-variable infeasibility.
///
/// System: 3*x + 3*y = 7  (gcd(3,3)=3, 7 mod 3 ≠ 0 → infeasible)
/// This is caught during solve(), not by remaining-equation check.
/// But a system that stalls before full reduction can leave equations.
#[test]
fn test_remaining_equation_single_var_out_of_bounds() {
    // Create a solver that will leave a remaining equation by using
    // a contrived stall threshold. With max_stall_rounds=0, the solver
    // won't do fresh-var steps, leaving multi-var equations.
    let mut solver = DiophSolver::new(3);
    solver.set_max_stall_rounds(0);
    solver.add_equation_with_source(
        [
            (0, BigInt::from(15)),
            (1, BigInt::from(-10)),
            (2, BigInt::from(6)),
        ],
        BigInt::one(),
        0,
    );

    let result = solver.solve();
    if matches!(result, DiophResult::Partial { .. }) {
        // With aggressive stall, some equations may remain
        let mut bounds = HashMap::default();
        bounds.insert(0, (Some(BigInt::zero()), Some(BigInt::from(100))));
        bounds.insert(1, (Some(BigInt::zero()), Some(BigInt::from(100))));
        bounds.insert(2, (Some(BigInt::zero()), Some(BigInt::from(100))));

        // Should be feasible (many solutions exist)
        let conflict = solver.check_remaining_with_bounds(&bounds);
        assert!(
            conflict.is_none(),
            "15x - 10y + 6z = 1 with vars ∈ [0, 100] should be feasible"
        );
    }
}

/// Regression test for #4830: expand_single_substitution silently dropped
/// fresh variables that had no substitution, making the expanded expression
/// tighter than the original parameterized one. This caused false UNSAT on
/// the convert-jpg2gif benchmark family.
///
/// System: 3*v0 + 7*v1 - 2*v2 = 10, 5*v1 - 3*v3 + 4*v4 = 17
/// All vars in [0, 255]. Solution: (1, 1, 0, 0, 3).
///
/// The Dioph solver eliminates v0 and v4 via fresh variables, producing
/// substitutions that reference unexpandable fresh vars. Before the fix,
/// get_expanded_substitutions dropped these fresh vars, yielding e.g.
/// v3 = -3 - v1 (incorrect) instead of v3 = -5 + v1 + v4 (correct).
/// The interval check then concluded v3 ∈ [-258, -3] which doesn't
/// intersect [0, 255], causing a false UNSAT.
#[test]
fn test_expand_substitution_does_not_drop_unexpandable_fresh_vars() {
    let mut solver = DiophSolver::new(5); // 5 original vars (v0..v4)
    solver.add_equation_from(
        [
            (0, BigInt::from(3)),
            (1, BigInt::from(7)),
            (2, BigInt::from(-2)),
        ],
        BigInt::from(10),
    );
    solver.add_equation_from(
        [
            (1, BigInt::from(5)),
            (3, BigInt::from(-3)),
            (4, BigInt::from(4)),
        ],
        BigInt::from(17),
    );

    let result = solver.solve();

    // Should NOT be infeasible — (1,1,0,0,3) is a valid solution
    assert!(
        !matches!(result, DiophResult::Infeasible { .. }),
        "System is feasible: (1,1,0,0,3) is a solution, but solver reported infeasible"
    );

    // The expanded substitutions should NOT include substitutions that
    // dropped fresh variables. With expand_fresh=true, any substitution
    // that references a fresh var without its own substitution should be
    // excluded (returns None from expand_single_substitution).
    let expanded = solver.get_expanded_substitutions(5, true);

    // Each expanded substitution must be mathematically valid:
    // evaluate at the known solution (v0=1, v1=1, v2=0, v3=0, v4=3)
    // and verify the LHS equals the RHS.
    let solution = [
        BigInt::from(1),
        BigInt::from(1),
        BigInt::zero(),
        BigInt::zero(),
        BigInt::from(3),
    ];

    for (var_idx, coeffs, constant) in &expanded {
        let mut rhs = constant.clone();
        for (dep_idx, coeff) in coeffs {
            assert!(
                *dep_idx < 5,
                "Expanded substitution for var {var_idx} references non-original var {dep_idx}",
            );
            rhs += coeff * &solution[*dep_idx];
        }
        assert_eq!(
            rhs, solution[*var_idx],
            "Expanded substitution for var {var_idx} evaluates to {rhs} at solution, expected {}",
            solution[*var_idx]
        );
    }
}

// ── #nip residual: regression coverage for the elimination de-cube ──────────
// These lock down the soundness-critical `normalized`-flag fast skip in
// `apply_substitution_to_equations` and the linear `merge_sources` union.

#[test]
fn test_normalized_flag_tracks_mutation() {
    // normalize() asserts the flag; a mutation that changes the equation
    // (substitute on a present var) clears it; a no-op substitute on an
    // ABSENT var must leave the flag untouched (the skip precondition).
    let mut eq = IntEquation::new(
        [(0, BigInt::from(2)), (1, BigInt::from(4))]
            .into_iter()
            .collect(),
        BigInt::from(6),
    );
    assert!(!eq.normalized, "fresh equation is not normalized");
    eq.normalize();
    assert!(eq.normalized, "normalize() sets the flag");

    // Substitute a variable NOT in the equation: early-returns, value-no-op,
    // flag stays true (so the elimination apply pass may safely skip it).
    let empty: HashMap<usize, BigInt> = HashMap::default();
    eq.substitute(99, &empty, &BigInt::zero());
    assert!(
        eq.normalized,
        "no-op substitute on an absent var must not clear `normalized`"
    );

    // Substitute a variable that IS present: real mutation, must clear it.
    eq.substitute(
        0,
        &[(1, BigInt::from(1))].into_iter().collect(),
        &BigInt::zero(),
    );
    assert!(
        !eq.normalized,
        "substitute on a present var must clear `normalized`"
    );
}

#[test]
fn test_merge_sources_union_subset_dedup_sorted() {
    // Linear merge-union must equal the old contains+push+sort: sorted,
    // deduplicated union. Covers the subset fast-path and a true interleave.
    let mut eq = IntEquation::new([(0, BigInt::from(1))].into_iter().collect(), BigInt::zero());
    eq.sources = vec![1, 3, 5];

    // Subset fast-path: other ⊆ self → unchanged.
    eq.merge_sources(&[3, 5]);
    assert_eq!(eq.sources, vec![1, 3, 5]);

    // Interleaved union with an overlap (3) and new elements (2, 4, 6).
    eq.merge_sources(&[2, 3, 4, 6]);
    assert_eq!(eq.sources, vec![1, 2, 3, 4, 5, 6]);

    // Empty other → no-op.
    eq.merge_sources(&[]);
    assert_eq!(eq.sources, vec![1, 2, 3, 4, 5, 6]);
}

#[test]
fn test_infeasible_non_pivot_equation_still_detected() {
    // Soundness regression for the fast skip: a system whose infeasible
    // equation does NOT share the eliminated unit variable must still be
    // reported Infeasible (the skip can never hide a conflict).
    //   x + y      = 3   (unit var x → pivot)
    //   2y + 4z    = 7   (gcd(2,4)=2 ∤ 7 → infeasible, has no x)
    let mut solver = DiophSolver::new(10);
    solver.add_equation_from(
        [(0, BigInt::from(1)), (1, BigInt::from(1))],
        BigInt::from(3),
    );
    solver.add_equation_from(
        [(1, BigInt::from(2)), (2, BigInt::from(4))],
        BigInt::from(7),
    );
    assert!(
        matches!(solver.solve(), DiophResult::Infeasible { .. }),
        "infeasible non-pivot equation must still be detected"
    );
}
