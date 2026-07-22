// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_cp::engine::CpSolveResult;
use ay_cp::propagator::Constraint;
use ay_cp::{CpSatEngine, Domain, IntVarId, SearchStrategy};

fn setup_nqueens(n: usize, strategy: SearchStrategy) -> CpSatEngine {
    let mut engine = CpSatEngine::new();
    let queens: Vec<IntVarId> = (0..n)
        .map(|i| engine.new_int_var(Domain::new(0, n as i64 - 1), Some(&format!("q{i}"))))
        .collect();
    engine.add_constraint(Constraint::AllDifferent(queens.clone()));
    for i in 0..n {
        for j in (i + 1)..n {
            let diff = (j - i) as i64;
            engine.add_constraint(Constraint::PairwiseNeq {
                x: queens[i],
                y: queens[j],
                offset: diff,
            });
            engine.add_constraint(Constraint::PairwiseNeq {
                x: queens[i],
                y: queens[j],
                offset: -diff,
            });
        }
    }
    engine.set_search_strategy(strategy);
    engine
}

fn verify_nqueens_solution(assignment: &[(IntVarId, i64)], n: usize) {
    assert_eq!(assignment.len(), n);
    let vals: Vec<i64> = assignment.iter().map(|(_, value)| *value).collect();
    let mut cols = vals.clone();
    cols.sort_unstable();
    cols.dedup();
    assert_eq!(cols.len(), n, "columns not all-different: {vals:?}");
    for i in 0..n {
        for j in (i + 1)..n {
            let col_diff = (vals[j] - vals[i]).unsigned_abs();
            let row_diff = (j - i) as u64;
            assert_ne!(
                col_diff, row_diff,
                "diagonal conflict: q[{i}]={}, q[{j}]={}",
                vals[i], vals[j]
            );
        }
    }
}

#[test]
fn test_12queens_activity_completes_without_clauseref_overflow() {
    let mut engine = setup_nqueens(12, SearchStrategy::Activity);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 12),
        other => panic!("12-queens with activity should be SAT, got {other:?}"),
    }
}

#[test]
fn test_12queens_dom_wdeg_completes_without_clauseref_overflow() {
    let mut engine = setup_nqueens(12, SearchStrategy::DomWDeg);
    match engine.solve() {
        CpSolveResult::Sat(assignment) => verify_nqueens_solution(&assignment, 12),
        other => panic!("12-queens with dom/wdeg should be SAT, got {other:?}"),
    }
}
