// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The #5384 replay's clause set: the formula and the lemmas, never a model
//! block, although the clause trace marks all three original.

use super::LoopSat;
use ay_sat::{Literal, Solver};

fn clause(dimacs: &[i32]) -> Vec<Literal> {
    dimacs
        .iter()
        .map(|&lit| Literal::from_dimacs(lit))
        .collect()
}

/// A solver configured like the theory loop's, holding `formula`.
fn loop_solver(formula: &[Vec<Literal>]) -> Solver {
    let mut solver = Solver::new(4);
    solver.enable_clause_trace();
    solver.set_unsat_certificate_enabled(false);
    solver.set_preprocess_enabled(false);
    for lits in formula {
        solver.add_clause(lits.clone());
    }
    solver
}

fn dimacs(clauses: &[Vec<Literal>]) -> Vec<Vec<i32>> {
    clauses
        .iter()
        .map(|lits| lits.iter().map(|lit| lit.to_dimacs()).collect())
        .collect()
}

fn trace_originals(sat: &LoopSat) -> usize {
    let trace = sat
        .clause_trace()
        .expect("the loop's solver keeps a clause trace");
    trace.original_clauses().count()
}

#[test]
fn replay_keeps_formula_and_lemmas_but_never_a_model_block() {
    let mut sat = LoopSat::new(loop_solver(&[clause(&[1, 2]), clause(&[-1, 3])]));
    sat.add_clause(clause(&[-2, 3]));
    sat.add_model_block(clause(&[-1, -3]));
    sat.add_clause(clause(&[2, 4]));
    // The trace cannot tell them apart: all five clauses are originals.
    assert_eq!(trace_originals(&sat), 5);
    let replay = sat.replay_clauses().expect("traced solver");
    let expected = [vec![1, 2], vec![-1, 3], vec![-2, 3], vec![2, 4]];
    assert_eq!(dimacs(&replay), expected);
}

#[test]
fn replacement_restarts_both_logs_from_the_replayed_formula() {
    let mut sat = LoopSat::new(loop_solver(&[clause(&[1, 2])]));
    sat.add_clause(clause(&[-2, 3]));
    sat.add_model_block(clause(&[-1, -3]));
    let replay = sat.replay_clauses().expect("traced solver");
    sat.replace_solver(loop_solver(&replay));
    assert!(sat.model_blocks().is_empty() && sat.added_clauses().is_empty());
    sat.add_model_block(clause(&[1, -3]));
    sat.add_clause(clause(&[-1, 4]));
    let replay = sat.replay_clauses().expect("traced solver");
    assert_eq!(dimacs(&replay), [vec![1, 2], vec![-2, 3], vec![-1, 4]]);
}
