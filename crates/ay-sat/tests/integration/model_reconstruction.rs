// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::common::{assert_model_satisfies, generate_test_clauses};
use ay_sat::{Literal, SatResult, Solver, Variable};
use ntest::timeout;

/// Test BVE model reconstruction with a simple eliminable variable
#[test]
#[timeout(3_000)]
fn test_model_reconstruction_bve_simple() {
    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(3)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
    ];

    let mut solver = Solver::new(4);
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_model_satisfies(&original_clauses, &model, "BVE reconstruction");
        }
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test BVE model reconstruction with multiple eliminable variables
#[test]
#[timeout(3_000)]
fn test_model_reconstruction_bve_multiple_vars() {
    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(3)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(4)),
        ],
        vec![
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(5)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(4)),
        ],
        vec![
            Literal::positive(Variable::new(3)),
            Literal::positive(Variable::new(5)),
        ],
    ];

    let mut solver = Solver::new(6);
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_model_satisfies(&original_clauses, &model, "multi-var BVE reconstruction");
        }
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test sweeping model reconstruction with equivalent literals
#[test]
#[timeout(3_000)]
fn test_model_reconstruction_sweep_equivalence() {
    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
    ];

    let mut solver = Solver::new(4);
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_model_satisfies(&original_clauses, &model, "sweep reconstruction");
            assert_eq!(
                model[0], model[1],
                "Equivalence x0 <-> x1 not preserved in reconstructed model"
            );
        }
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test sweeping model reconstruction with negated equivalence (x0 <-> -x1)
#[test]
#[timeout(3_000)]
fn test_model_reconstruction_sweep_negated_equivalence() {
    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
    ];

    let mut solver = Solver::new(4);
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_model_satisfies(&original_clauses, &model, "negated sweep reconstruction");
            assert_ne!(
                model[0], model[1],
                "Negated equivalence x0 <-> -x1 not preserved: x0={}, x1={}",
                model[0], model[1]
            );
        }
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test combined BVE and sweeping model reconstruction
#[test]
#[timeout(3_000)]
fn test_model_reconstruction_combined_bve_sweep() {
    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
        vec![
            Literal::negative(Variable::new(2)),
            Literal::positive(Variable::new(4)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(3)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(4)),
        ],
    ];

    let mut solver = Solver::new(5);
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_model_satisfies(
                &original_clauses,
                &model,
                "combined BVE+sweep reconstruction",
            );
        }
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test model reconstruction with larger formula using random 3-SAT
#[test]
#[timeout(3_000)]
fn test_model_reconstruction_larger_formula() {
    let clauses = generate_test_clauses(20, 80, 12345);

    let mut solver = Solver::new(20);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_model_satisfies(&clauses, &model, "larger formula reconstruction");
        }
        SatResult::Unsat(_) => {}
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test that reconstruction correctly handles extended model size
#[test]
#[timeout(3_000)]
fn test_model_reconstruction_model_size() {
    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(5)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(5)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(6)),
        ],
        vec![
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(6)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(7)),
        ],
        vec![
            Literal::negative(Variable::new(2)),
            Literal::positive(Variable::new(7)),
        ],
        vec![
            Literal::positive(Variable::new(5)),
            Literal::positive(Variable::new(6)),
        ],
        vec![
            Literal::positive(Variable::new(6)),
            Literal::positive(Variable::new(7)),
        ],
        vec![
            Literal::positive(Variable::new(3)),
            Literal::positive(Variable::new(4)),
        ],
    ];

    let mut solver = Solver::new(8);
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(
                model.len() >= 8,
                "Model too small: expected >= 8, got {}",
                model.len()
            );

            assert_model_satisfies(&original_clauses, &model, "model size reconstruction");
        }
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test reconstruction with pure literal elimination
#[test]
#[timeout(3_000)]
fn test_model_reconstruction_pure_literal() {
    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(3)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
    ];

    let mut solver = Solver::new(4);
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_model_satisfies(&original_clauses, &model, "pure literal reconstruction");
        }
        SatResult::Unsat(_) => panic!("Formula should be SAT"),
        SatResult::Unknown => panic!("Got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Comprehensive stress test: verify reconstruction across many random formulas
#[test]
#[timeout(10_000)]
fn test_model_reconstruction_stress() {
    for seed in 0..100 {
        let clauses = generate_test_clauses(12, 48, seed);

        let mut solver = Solver::new(12);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();

        match result {
            SatResult::Sat(model) => {
                assert_model_satisfies(&clauses, &model, &format!("stress test seed {seed}"));
            }
            SatResult::Unsat(_) => {}
            SatResult::Unknown => panic!("Stress test seed {seed}: got Unknown"),
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }
}
