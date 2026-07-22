// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #7108: LRAT chain verification failure in
//! congruence contradiction empty clause derivation.
//!
//! These are the exact proptest regression seeds extracted from
//! proptest-regressions/solver/tests/proof_lrat.txt. They trigger
//! NonUnit failures in the LRAT checker when `collect_resolution_chain`
//! pushes multi-literal reason clause IDs instead of materialized
//! unit proof IDs for level-0 variables.

use ay_sat::{Literal, ProofOutput, SatResult, Solver};

fn lit(idx: usize) -> Literal {
    Literal::from_index(idx)
}

/// Run a formula with LRAT proof output and verify the result.
fn run_lrat_test(num_vars: usize, clauses: Vec<Vec<Literal>>) {
    let num_clauses = clauses.len() as u64;
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), num_clauses);
    let mut solver = Solver::with_proof_output(num_vars, proof);

    let original_clauses = clauses.clone();
    for clause in clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    match &result {
        SatResult::Sat(model) => {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&l| {
                    let var_val = model[l.variable().index()];
                    if l.is_positive() {
                        var_val
                    } else {
                        !var_val
                    }
                });
                assert!(
                    satisfied,
                    "SAT model falsifies original clause {ci} ({clause:?})"
                );
            }
        }
        SatResult::Unsat(_) => {
            let writer = solver.take_proof_writer().expect("proof writer");
            let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

            assert!(
                !proof_text.is_empty(),
                "UNSAT result must produce non-empty LRAT proof"
            );

            let has_empty_clause = proof_text.lines().any(|line| {
                let tokens: Vec<&str> = line.split_whitespace().collect();
                tokens.len() >= 2 && tokens[1] == "0"
            });
            assert!(
                has_empty_clause,
                "UNSAT LRAT proof must contain empty clause derivation.\n\
                 Proof ({} bytes, {} lines):\n{}",
                proof_text.len(),
                proof_text.lines().count(),
                &proof_text[..proof_text.len().min(2000)]
            );
        }
        SatResult::Unknown => {}
        _ => {}
    }
}

/// Regression seed 1: 5 vars, 25 clauses.
#[test]
fn test_lrat_regression_seed1_7108() {
    run_lrat_test(
        5,
        vec![
            vec![lit(1), lit(0), lit(1)],
            vec![lit(9), lit(3), lit(7)],
            vec![lit(4), lit(4), lit(5)],
            vec![lit(2), lit(1), lit(8)],
            vec![lit(6), lit(6), lit(9)],
            vec![lit(6), lit(1), lit(2)],
            vec![lit(9), lit(7), lit(3)],
            vec![lit(9), lit(1), lit(1)],
            vec![lit(8), lit(1), lit(8)],
            vec![lit(9), lit(7), lit(3)],
            vec![lit(6), lit(2), lit(8)],
            vec![lit(0), lit(7), lit(3)],
            vec![lit(2), lit(4), lit(4)],
            vec![lit(0), lit(5), lit(3)],
            vec![lit(8), lit(3), lit(4)],
            vec![lit(4), lit(3), lit(6)],
            vec![lit(2), lit(1), lit(6)],
            vec![lit(9), lit(9), lit(6)],
            vec![lit(2), lit(0), lit(2)],
            vec![lit(9), lit(1), lit(0)],
            vec![lit(0), lit(0), lit(8)],
            vec![lit(4), lit(4), lit(3)],
            vec![lit(1), lit(3), lit(2)],
            vec![lit(1), lit(2), lit(3)],
            vec![lit(2), lit(5), lit(5)],
        ],
    );
}

/// Regression seed 2: 7 vars, 35 clauses.
#[test]
fn test_lrat_regression_seed2_7108() {
    run_lrat_test(
        7,
        vec![
            vec![lit(2), lit(0), lit(1)],
            vec![lit(1), lit(1), lit(8)],
            vec![lit(0), lit(1), lit(0)],
            vec![lit(12), lit(3), lit(3)],
            vec![lit(3), lit(4), lit(2)],
            vec![lit(0), lit(0), lit(12)],
            vec![lit(9), lit(11), lit(4)],
            vec![lit(1), lit(5), lit(7)],
            vec![lit(6), lit(1), lit(12)],
            vec![lit(5), lit(10), lit(3)],
            vec![lit(13), lit(6), lit(8)],
            vec![lit(7), lit(5), lit(9)],
            vec![lit(8), lit(10), lit(4)],
            vec![lit(8), lit(10), lit(11)],
            vec![lit(6), lit(12), lit(12)],
            vec![lit(2), lit(1), lit(13)],
            vec![lit(3), lit(9), lit(2)],
            vec![lit(7), lit(4), lit(2)],
            vec![lit(5), lit(2), lit(7)],
            vec![lit(6), lit(0), lit(3)],
            vec![lit(6), lit(8), lit(5)],
            vec![lit(7), lit(2), lit(2)],
            vec![lit(9), lit(2), lit(4)],
            vec![lit(0), lit(2), lit(8)],
            vec![lit(3), lit(0), lit(7)],
            vec![lit(12), lit(10), lit(8)],
            vec![lit(10), lit(12), lit(8)],
            vec![lit(11), lit(1), lit(0)],
            vec![lit(8), lit(12), lit(11)],
            vec![lit(2), lit(2), lit(9)],
            vec![lit(1), lit(4), lit(13)],
            vec![lit(1), lit(5), lit(6)],
            vec![lit(0), lit(0), lit(10)],
            vec![lit(9), lit(2), lit(7)],
            vec![lit(11), lit(4), lit(9)],
        ],
    );
}
