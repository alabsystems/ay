// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::model::{Constraint, RowKind, Sense, VarKind, Variable};

#[test]
fn test_solve_continuous() {
    // min x + y s.t. x + y >= 4, x,y >= 0. Optimal at x+y=4 with obj=4.
    let mut p = Problem::new();
    p.sense = Sense::Min;
    p.variables.push(Variable {
        name: "x".into(),
        obj_coeff: 1.0,
        lower: 0.0,
        upper: f64::INFINITY,
        kind: VarKind::Continuous,
    });
    p.variables.push(Variable {
        name: "y".into(),
        obj_coeff: 1.0,
        lower: 0.0,
        upper: f64::INFINITY,
        kind: VarKind::Continuous,
    });
    p.constraints.push(Constraint {
        name: "c".into(),
        kind: RowKind::Ge,
        coeffs: vec![(0, 1.0), (1, 1.0)],
        rhs: 4.0,
    });
    let sol = solve(&p).expect("solve");
    assert!((sol.objective - 4.0).abs() < 1e-4);
}

#[test]
fn test_solve_integer_knapsack() {
    // max 3x + 4y s.t. 2x + 3y <= 6, x,y in {0,1,2}, integer.
    // Exhaustive: (0,0)=0, (0,1)=4, (0,2)=8, (1,0)=3, (1,1)=7, (2,0)=6, (1,2)=11 (infeas 2+6=8), (2,1)=10.
    // Feasible: x=0,y=2 -> obj=8; x=2,y=0 -> 6; x=1,y=1 -> 7; x=2,y=1 -> 10 via 4+3=7<=6? 4+3=7>6 INFEAS.
    // Let's recompute: 2*2 + 3*1 = 7 > 6, infeasible. 2*0 + 3*2 = 6 feasible, obj=8. So max=8.
    let mut p = Problem::new();
    p.sense = Sense::Max;
    p.variables.push(Variable {
        name: "x".into(),
        obj_coeff: 3.0,
        lower: 0.0,
        upper: 2.0,
        kind: VarKind::Integer,
    });
    p.variables.push(Variable {
        name: "y".into(),
        obj_coeff: 4.0,
        lower: 0.0,
        upper: 2.0,
        kind: VarKind::Integer,
    });
    p.constraints.push(Constraint {
        name: "c".into(),
        kind: RowKind::Le,
        coeffs: vec![(0, 2.0), (1, 3.0)],
        rhs: 6.0,
    });
    let sol = solve(&p).expect("solve");
    assert!((sol.objective - 8.0).abs() < 1e-4, "got {}", sol.objective);
    assert!((sol.values[1] - 2.0).abs() < 1e-4);
}

#[test]
fn test_solve_upper_only_integer_bound() {
    let mut p = Problem::new();
    p.sense = Sense::Max;
    p.variables.push(Variable {
        name: "x".into(),
        obj_coeff: 1.0,
        lower: f64::NEG_INFINITY,
        upper: 3.2,
        kind: VarKind::Integer,
    });
    let sol = solve(&p).expect("solve");
    assert!((sol.objective - 3.0).abs() < 1e-4, "got {}", sol.objective);
    assert!((sol.values[0] - 3.0).abs() < 1e-4, "x = {}", sol.values[0]);
}

#[test]
fn test_integer_incumbent_materializes_rounded_values() {
    let mut p = Problem::new();
    p.sense = Sense::Max;
    p.variables.push(Variable {
        name: "x".into(),
        obj_coeff: 1.0,
        lower: 0.0,
        upper: 1.0000004,
        kind: VarKind::Integer,
    });

    let sol = solve(&p).expect("solve");

    assert_eq!(sol.values[0], 1.0);
    assert_eq!(sol.objective, 1.0);
}

#[test]
fn test_integer_search_does_not_claim_unbounded_from_relaxation_only() {
    let mut p = Problem::new();
    p.sense = Sense::Max;
    p.variables.push(Variable {
        name: "x".into(),
        obj_coeff: 0.0,
        lower: 0.5,
        upper: 0.5,
        kind: VarKind::Integer,
    });
    p.variables.push(Variable {
        name: "y".into(),
        obj_coeff: 1.0,
        lower: 0.0,
        upper: f64::INFINITY,
        kind: VarKind::Continuous,
    });

    // The LP relaxation is unbounded via y at x = 0.5, but the integer
    // model has no feasible assignment for x. Without an integer-feasible
    // ray certificate, branch-and-bound must not report MIP unboundedness.
    assert!(matches!(
        solve(&p),
        Err(LpError::Unsupported(msg))
            if msg.contains("cannot certify unboundedness")
    ));
}

#[test]
fn test_near_integer_value_outside_exact_box_is_not_an_incumbent() {
    let mut p = Problem::new();
    p.variables.push(Variable {
        name: "x".into(),
        obj_coeff: 0.0,
        lower: 1.0000004,
        upper: 1.0000004,
        kind: VarKind::Integer,
    });

    assert!(matches!(solve(&p), Err(LpError::Infeasible)));
}

#[test]
fn test_binary_near_integer_value_outside_effective_box_is_not_an_incumbent() {
    let mut p = Problem::new();
    p.variables.push(Variable {
        name: "x".into(),
        obj_coeff: 0.0,
        lower: 1.0000004,
        upper: f64::INFINITY,
        kind: VarKind::Binary,
    });

    assert!(matches!(solve(&p), Err(LpError::Infeasible)));
}

#[test]
fn test_integer_candidate_rejects_malformed_direct_inputs() {
    let mut p = Problem::new();
    p.variables.push(Variable {
        name: "x".into(),
        obj_coeff: 1.0,
        lower: 0.0,
        upper: 1.0,
        kind: VarKind::Integer,
    });
    let relaxation = Solution {
        objective: 1.0,
        values: vec![1.0],
    };

    assert!(integer_candidate_from_relaxation(
        &p,
        &Solution {
            objective: 0.0,
            values: vec![],
        },
    )
    .is_none());

    p.obj_constant = f64::NAN;
    assert!(integer_candidate_from_relaxation(&p, &relaxation).is_none());

    p.obj_constant = 0.0;
    p.variables[0].obj_coeff = f64::INFINITY;
    assert!(integer_candidate_from_relaxation(&p, &relaxation).is_none());

    p.variables[0].obj_coeff = 1.0;
    p.constraints.push(Constraint {
        name: "bad".into(),
        kind: RowKind::Le,
        coeffs: vec![(0, f64::INFINITY)],
        rhs: 1.0,
    });
    assert!(integer_candidate_from_relaxation(&p, &relaxation).is_none());
}

#[test]
fn test_pick_fractional_scores_negative_values_symmetrically() {
    let mut p = Problem::new();
    p.variables.push(Variable {
        name: "x".into(),
        obj_coeff: 0.0,
        lower: f64::NEG_INFINITY,
        upper: f64::INFINITY,
        kind: VarKind::Integer,
    });
    p.variables.push(Variable {
        name: "y".into(),
        obj_coeff: 0.0,
        lower: f64::NEG_INFINITY,
        upper: f64::INFINITY,
        kind: VarKind::Integer,
    });

    assert!((fractional_score(-2.4) - 0.4).abs() < 1e-12);
    assert!((fractional_score(2.4) - 0.4).abs() < 1e-12);
    assert_eq!(pick_fractional(&p, &[-2.4, 3.1]), Some((0, -2.4)));
}
