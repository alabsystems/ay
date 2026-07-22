// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Known-SAT regression tests.
//!
//! These tests verify that specific benchmarks known to be SAT are not
//! incorrectly reported as UNSAT when particular inprocessing features
//! are enabled. Each test documents the original bug that exposed the
//! regression.

use ay_sat::{parse_dimacs, Literal, SatResult, Variable};
use ntest::timeout;

use super::common::{assert_model_satisfies, disable_all_inprocessing};
use super::test_common;
use ay_sat::Solver;

/// Regression test for #3466: decompose causes wrong-UNSAT on AProVE09-13.
/// This SAT benchmark returns UNSATISFIABLE when decompose is enabled.
#[test]
#[timeout(60_000)]
fn gate_decompose_sat_aprove09_13() {
    let path = test_common::workspace_root()
        .join("reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/sat/AProVE09-13.cnf");
    let Some(cnf) = test_common::load_optional_benchmark(&path) else {
        return;
    };
    let formula = parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();

    // Test 1: decompose in isolation on SAT benchmark
    let mut solver = Solver::new(formula.num_vars);
    disable_all_inprocessing(&mut solver);
    solver.set_decompose_enabled(true);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            assert_model_satisfies(&original_clauses, model, "decompose-isolation/AProVE09-13");
        }
        SatResult::Unsat(_) => {
            panic!(
                "SOUNDNESS BUG #3466: decompose isolation returned UNSAT on known-SAT AProVE09-13"
            );
        }
        SatResult::Unknown => {
            panic!("decompose isolation returned Unknown on AProVE09-13");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }

    // Test 2: decompose explicitly enabled on the default feature profile.
    let formula2 = parse_dimacs(&cnf).expect("parse");
    let mut solver2 = formula2.into_solver();
    solver2.set_decompose_enabled(true);
    let result2 = solver2.solve().into_inner();
    match &result2 {
        SatResult::Sat(model) => {
            assert_model_satisfies(&original_clauses, model, "decompose-all/AProVE09-13");
        }
        SatResult::Unsat(_) => {
            panic!("SOUNDNESS BUG #3466: decompose+all returned UNSAT on known-SAT AProVE09-13");
        }
        SatResult::Unknown => {
            panic!("decompose+all returned Unknown on AProVE09-13");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Regression test for #3466: decompose + all features on stric-bmc-ibm-10.
/// This known-SAT benchmark (CaDiCaL: SAT in 0.29s) previously returned UNSAT
/// when decompose was enabled due to BVE+decompose feature interaction.
#[test]
#[timeout(120_000)]
fn gate_decompose_sat_stric_bmc_ibm_10() {
    let path =
        test_common::workspace_root().join("reference/creusat/tests/cnf-hard/stric-bmc-ibm-10.cnf");
    let Some(cnf) = test_common::load_optional_benchmark(&path) else {
        return;
    };
    let formula = parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();

    let mut solver = formula.into_solver();
    solver.set_decompose_enabled(true);
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            assert_model_satisfies(&original_clauses, model, "decompose-all/stric-bmc-ibm-10");
        }
        SatResult::Unsat(_) => {
            panic!(
                "SOUNDNESS BUG #3466: decompose+all returned UNSAT on known-SAT stric-bmc-ibm-10"
            );
        }
        SatResult::Unknown => {
            panic!("decompose+all returned Unknown on stric-bmc-ibm-10");
        }
        _ => unreachable!(),
    }
}

/// Regression test for #3466: decompose + all features on q_query_3_l37_lambda.
/// Known-SAT benchmark that previously returned wrong-UNSAT with decompose enabled.
#[test]
#[timeout(60_000)]
fn gate_decompose_sat_q_query() {
    let path = test_common::workspace_root().join(
        "reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/sat/q_query_3_l37_lambda.cnf",
    );
    let Some(cnf) = test_common::load_optional_benchmark(&path) else {
        return;
    };
    let formula = parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();

    let mut solver = formula.into_solver();
    solver.set_decompose_enabled(true);
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            assert_model_satisfies(&original_clauses, model, "decompose-all/q_query_3_l37");
        }
        SatResult::Unsat(_) => {
            panic!("SOUNDNESS BUG #3466: decompose+all returned UNSAT on known-SAT q_query_3_l37");
        }
        SatResult::Unknown => {
            panic!("decompose+all returned Unknown on q_query_3_l37");
        }
        _ => unreachable!(),
    }
}

fn add_duplicate_and_gate_formula(solver: &mut Solver) -> Vec<Vec<Literal>> {
    let a = Variable::new(0);
    let b = Variable::new(1);
    let g1 = Variable::new(2);
    let g2 = Variable::new(3);
    let clauses = vec![
        // g1 = AND(a, b)
        vec![
            Literal::negative(a),
            Literal::negative(b),
            Literal::positive(g1),
        ],
        vec![Literal::positive(a), Literal::negative(g1)],
        vec![Literal::positive(b), Literal::negative(g1)],
        // g2 = AND(a, b)
        vec![
            Literal::negative(a),
            Literal::negative(b),
            Literal::positive(g2),
        ],
        vec![Literal::positive(a), Literal::negative(g2)],
        vec![Literal::positive(b), Literal::negative(g2)],
        // Force both gates true.
        vec![Literal::positive(g1)],
        vec![Literal::positive(g2)],
    ];
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }
    clauses
}

fn assert_sat_result(result: &SatResult, original_clauses: &[Vec<Literal>], label: &str) {
    match result {
        SatResult::Sat(model) => assert_model_satisfies(original_clauses, model, label),
        SatResult::Unsat(_) => panic!("SOUNDNESS BUG: {label} returned UNSAT on SAT formula"),
        SatResult::Unknown => panic!("{label} returned Unknown"),
        _ => unreachable!(),
    }
}

/// Regression for #3428/#5031: first solve with decompose+gate+congruence must
/// return correct SAT and properly manage the feature profile.
///
/// Fix 3 (#5031) disables destructive inprocessing on second+ solve via
/// `has_solved_once`. This test verifies:
/// 1. First solve with destructive inprocessing returns correct SAT
/// 2. Congruence actually executes (non-vacuity)
/// 3. Destructive features disabled after second solve (#5031)
#[test]
fn gate_incremental_two_solve_profile_and_congruence_non_vacuity() {
    let mut solver = Solver::new(4);
    disable_all_inprocessing(&mut solver);
    solver.set_decompose_enabled(true);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);

    let setup = solver.inprocessing_feature_profile();
    assert!(
        setup.decompose && setup.gate && setup.congruence,
        "setup requires all three"
    );

    let original_clauses = add_duplicate_and_gate_formula(&mut solver);

    let first = solver.solve().into_inner();
    let first_rounds = solver.congruence_stats().rounds;
    assert_sat_result(&first, &original_clauses, "#3428/solve1");
    assert!(first_rounds > 0, "congruence must execute at least once");

    let post_first = solver.inprocessing_feature_profile();
    assert!(
        post_first.decompose && post_first.gate && post_first.congruence,
        "inprocessing features must survive first solve"
    );

    let second = solver.solve().into_inner();
    assert_sat_result(&second, &original_clauses, "#5031/solve2");

    // #5031/#5166: destructive inprocessing disabled on second solve via
    // has_been_incremental body guards. The .enabled flags remain true (the
    // user-facing profile is preserved), but the techniques don't execute.
    // Verify by checking that congruence rounds did not increase.
    let post_second = solver.inprocessing_feature_profile();
    assert!(post_second.gate, "non-destructive features must survive");
    // .enabled flags are preserved per #5166 — body guards prevent execution.
    assert!(
        post_second.decompose && post_second.congruence,
        "enabled flags preserved (#5166)"
    );
    assert_eq!(
        solver.congruence_stats().rounds,
        first_rounds,
        "congruence must not execute on second solve (#5031): got {}, first had {}",
        solver.congruence_stats().rounds,
        first_rounds,
    );
}
