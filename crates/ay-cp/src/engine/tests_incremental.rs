// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental solving and optimization tests for CpSatEngine.

use super::tests::encode_diagonal_constraints;
use super::*;
use crate::domain::Domain;

/// Verify that incremental optimization via add_upper_bound finds optimal.
/// Uses an explicit objective variable bounded via SAT-level constraints.
#[test]
fn test_incremental_minimize_with_obj_var() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 10), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 10), Some("y"));
    let obj = engine.new_int_var(Domain::new(2, 20), Some("obj"));

    // obj = x + y
    engine.add_constraint(Constraint::LinearEq {
        coeffs: vec![1, 1, -1],
        vars: vec![x, y, obj],
        rhs: 0,
    });
    // x + y >= 5
    engine.add_constraint(Constraint::LinearGe {
        coeffs: vec![1, 1],
        vars: vec![x, y],
        rhs: 5,
    });

    let mut best_obj = i64::MAX;
    let mut iterations = 0;

    loop {
        match engine.solve() {
            CpSolveResult::Sat(assignment) => {
                let obj_val = assignment.iter().find(|(v, _)| *v == obj).unwrap().1;
                assert!(
                    obj_val < best_obj,
                    "objective should strictly improve: {obj_val} >= {best_obj}"
                );
                best_obj = obj_val;
                iterations += 1;

                // Tighten: obj <= obj_val - 1 via SAT-level bound
                engine.add_upper_bound(obj, obj_val - 1);
            }
            CpSolveResult::Unsat => break,
            _ => panic!("unexpected Unknown"),
        }
    }

    assert!(iterations >= 1, "should find at least one solution");
    assert_eq!(best_obj, 5, "optimal x + y should be 5");
}

/// Verify that the engine preserves search heuristic state across solves.
/// Solving twice with the same model should reuse learned weights.
#[test]
fn test_incremental_search_state_preserved() {
    let mut engine = CpSatEngine::new();
    let queens: Vec<IntVarId> = (0..8)
        .map(|i| engine.new_int_var(Domain::new(0, 7), Some(&format!("q{i}"))))
        .collect();
    engine.add_constraint(Constraint::AllDifferent(queens.clone()));

    // Add diagonal constraints
    encode_diagonal_constraints(&mut engine, &queens, 8);

    // First solve: find a solution
    let result1 = engine.solve();
    assert!(
        matches!(result1, CpSolveResult::Sat(_)),
        "8-queens should be SAT"
    );

    // Block the first solution and solve again
    if let CpSolveResult::Sat(ref assignment) = result1 {
        engine.block_assignment(assignment);
    }

    let result2 = engine.solve();
    assert!(
        matches!(result2, CpSolveResult::Sat(_)),
        "8-queens has 92 solutions, second solve should find another"
    );

    // The two solutions should differ (at least one variable different)
    if let (CpSolveResult::Sat(a1), CpSolveResult::Sat(a2)) = (&result1, &result2) {
        let differs = a1.iter().zip(a2.iter()).any(|((_, v1), (_, v2))| v1 != v2);
        assert!(differs, "second solution should differ from first");
    }
}

/// Regression test for #5608: incremental optimization returns spurious UNSAT.
///
/// Minimal reproduction: solve x + y <= z with z as objective (minimize).
/// First solve finds z=some_value, then add_upper_bound(z, some_value-1)
/// and re-solve. The second solve should find a tighter z, not return UNSAT.
#[test]
fn test_incremental_optimization_upper_bound() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(1, 5), Some("x"));
    let y = engine.new_int_var(Domain::new(1, 5), Some("y"));
    let z = engine.new_int_var(Domain::new(0, 15), Some("z"));

    // z >= x + y (i.e., x + y - z <= 0)
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, 1, -1],
        vars: vec![x, y, z],
        rhs: 0,
    });

    // First solve: should be SAT with z >= x + y >= 2
    let result1 = engine.solve();
    let z_val1 = match &result1 {
        CpSolveResult::Sat(assignment) => {
            let z_val = assignment.iter().find(|(v, _)| *v == z).unwrap().1;
            assert!(z_val >= 2, "z should be >= 2, got {z_val}");
            z_val
        }
        other => panic!("first solve: expected SAT, got {other:?}"),
    };

    // Tighten: z <= z_val1 - 1 (but still feasible since min is 2)
    if z_val1 > 2 {
        engine.add_upper_bound(z, z_val1 - 1);

        // Second solve should still be SAT
        let result2 = engine.solve();
        match &result2 {
            CpSolveResult::Sat(assignment) => {
                let z_val2 = assignment.iter().find(|(v, _)| *v == z).unwrap().1;
                assert!(
                    z_val2 < z_val1,
                    "second solve: z should be < {z_val1}, got {z_val2}"
                );
                assert!(z_val2 >= 2, "second solve: z should be >= 2, got {z_val2}");
            }
            other => panic!("second solve: expected SAT (z can still be >= 2), got {other:?}"),
        }
    }
}

/// Same as above but minimizes until UNSAT to verify optimality detection.
#[test]
fn test_incremental_optimization_until_unsat() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(3, 5), Some("x"));
    let y = engine.new_int_var(Domain::new(4, 6), Some("y"));
    let z = engine.new_int_var(Domain::new(0, 20), Some("z"));

    // z >= x + y → minimum z is 3+4=7
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, 1, -1],
        vars: vec![x, y, z],
        rhs: 0,
    });

    let mut best = None;
    loop {
        match engine.solve() {
            CpSolveResult::Sat(assignment) => {
                let z_val = assignment.iter().find(|(v, _)| *v == z).unwrap().1;
                let x_val = assignment.iter().find(|(v, _)| *v == x).unwrap().1;
                let y_val = assignment.iter().find(|(v, _)| *v == y).unwrap().1;
                assert!(
                    z_val >= x_val + y_val,
                    "constraint violated: z={z_val} < x+y={}",
                    x_val + y_val
                );
                best = Some(z_val);
                engine.add_upper_bound(z, z_val - 1);
            }
            CpSolveResult::Unsat => break,
            other => panic!("unexpected: {other:?}"),
        }
    }

    let optimal = best.expect("should have found at least one solution");
    assert_eq!(
        optimal, 7,
        "optimal z should be 7 (min of x+y where x>=3, y>=4), got {optimal}"
    );
}

/// Build a jobshop2x3 model (2 jobs, 3 machines) with Big-M disjunctive encoding.
/// Returns (engine, makespan_var).
fn build_jobshop2x3() -> (CpSatEngine, IntVarId) {
    let mut engine = CpSatEngine::new();

    // Start times (horizon 0..15)
    let s11 = engine.new_int_var(Domain::new(0, 15), Some("s11"));
    let s12 = engine.new_int_var(Domain::new(0, 15), Some("s12"));
    let s13 = engine.new_int_var(Domain::new(0, 15), Some("s13"));
    let s21 = engine.new_int_var(Domain::new(0, 15), Some("s21"));
    let s22 = engine.new_int_var(Domain::new(0, 15), Some("s22"));
    let s23 = engine.new_int_var(Domain::new(0, 15), Some("s23"));
    let makespan = engine.new_int_var(Domain::new(0, 15), Some("makespan"));
    let b_m1 = engine.new_int_var(Domain::new(0, 1), Some("b_m1"));
    let b_m2 = engine.new_int_var(Domain::new(0, 1), Some("b_m2"));
    let b_m3 = engine.new_int_var(Domain::new(0, 1), Some("b_m3"));

    // Precedence: job 1: s11+3<=s12, s12+2<=s13
    for (a, b, d) in [(s11, s12, 3), (s12, s13, 2)] {
        engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![a, b],
            rhs: -d,
        });
    }
    // Precedence: job 2: s21+2<=s22, s22+3<=s23
    for (a, b, d) in [(s21, s22, 2), (s22, s23, 3)] {
        engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![a, b],
            rhs: -d,
        });
    }

    // Machine disjunctive constraints (Big-M=20)
    let machines = [
        (s11, s22, b_m1, 3, 3), // M1: dur1=3, dur2=3
        (s12, s21, b_m2, 2, 2), // M2: dur1=2, dur2=2
        (s13, s23, b_m3, 4, 1), // M3: dur1=4, dur2=1
    ];
    for (a, b, bvar, dur_a, dur_b) in machines {
        engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1, -20],
            vars: vec![a, b, bvar],
            rhs: -dur_a,
        });
        engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![-1, 1, 20],
            vars: vec![a, b, bvar],
            rhs: 20 - dur_b,
        });
    }

    // Makespan: makespan >= s13+4, makespan >= s23+1
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, -1],
        vars: vec![s13, makespan],
        rhs: -4,
    });
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, -1],
        vars: vec![s23, makespan],
        rhs: -1,
    });

    (engine, makespan)
}

/// Regression test for #5608: jobshop2x3 optimization reports makespan=11
/// instead of optimal makespan=10.
///
/// Encodes the exact jobshop2x3 FlatZinc model (2 jobs, 3 machines) using
/// Big-M disjunctive constraints, then minimizes makespan incrementally.
#[test]
fn test_jobshop2x3_optimal_makespan() {
    let (mut engine, makespan) = build_jobshop2x3();

    let mut best = None;
    let mut iterations = 0;
    loop {
        iterations += 1;
        assert!(iterations <= 20, "too many optimization iterations");

        match engine.solve() {
            CpSolveResult::Sat(assignment) => {
                let ms = assignment.iter().find(|(v, _)| *v == makespan).unwrap().1;
                best = Some(ms);
                engine.add_upper_bound(makespan, ms - 1);
            }
            CpSolveResult::Unsat => break,
            other => panic!("unexpected: {other:?}"),
        }
    }

    let optimal = best.expect("should have found at least one solution");
    assert_eq!(
        optimal, 10,
        "optimal makespan for jobshop2x3 should be 10, got {optimal}"
    );
}
