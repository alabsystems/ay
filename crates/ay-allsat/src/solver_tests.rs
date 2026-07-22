// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_single_solution() {
    let mut solver = AllSatSolver::new();

    // x1 AND x2
    solver.add_clause(vec![1]);
    solver.add_clause(vec![2]);

    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 1);
    assert!(solutions[0].is_true(1));
    assert!(solutions[0].is_true(2));
}

#[test]
fn test_two_solutions() {
    let mut solver = AllSatSolver::new();

    // (x1 OR x2) AND NOT(x1 AND x2)
    // = (x1 OR x2) AND (NOT x1 OR NOT x2)
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, -2]);

    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 2);

    // Should have x1=T,x2=F and x1=F,x2=T
    let has_10 = solutions.iter().any(|s| s.is_true(1) && !s.is_true(2));
    let has_01 = solutions.iter().any(|s| !s.is_true(1) && s.is_true(2));
    assert!(has_10, "Should have solution x1=T, x2=F");
    assert!(has_01, "Should have solution x1=F, x2=T");
}

#[test]
fn test_unsat() {
    let mut solver = AllSatSolver::new();

    // x1 AND NOT x1
    solver.add_clause(vec![1]);
    solver.add_clause(vec![-1]);

    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 0);
}

#[test]
fn test_all_assignments() {
    let mut solver = AllSatSolver::new();

    // TRUE (no clauses restricts nothing, but we need at least one var)
    // Add a tautology: x1 OR NOT x1
    solver.add_clause(vec![1, -1]);

    let solutions = solver.enumerate();
    // Two solutions: x1=T and x1=F
    assert_eq!(solutions.len(), 2);
}

#[test]
fn test_bounded_enumeration() {
    let mut solver = AllSatSolver::new();

    // (x1 OR x2) - has 3 solutions (TT, TF, FT)
    solver.add_clause(vec![1, 2]);

    let config = AllSatConfig {
        max_solutions: Some(2),
        ..Default::default()
    };
    let solutions = solver.enumerate_with_config(config);
    assert_eq!(solutions.len(), 2);
}

#[test]
fn test_projected_enumeration() {
    let mut solver = AllSatSolver::new();

    // x1 AND (x2 OR x3)
    // Full solutions: x1=T,x2=T,x3=T; x1=T,x2=T,x3=F; x1=T,x2=F,x3=T
    solver.add_clause(vec![1]);
    solver.add_clause(vec![2, 3]);

    // Project onto x1 only
    let config = AllSatConfig {
        projection: Some(vec![1]),
        ..Default::default()
    };
    let solutions = solver.enumerate_with_config(config);
    // Only one projected solution: x1=T
    assert_eq!(solutions.len(), 1);
    assert!(solutions[0].is_true(1));
}

#[test]
fn test_count() {
    let mut solver = AllSatSolver::new();

    // (x1 OR x2) - has 3 solutions
    solver.add_clause(vec![1, 2]);

    assert_eq!(solver.count(), 3);
}

#[test]
fn test_is_sat() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);
    assert!(solver.is_sat());

    let mut solver2 = AllSatSolver::new();
    solver2.add_clause(vec![1]);
    solver2.add_clause(vec![-1]);
    assert!(!solver2.is_sat());
}

#[test]
fn test_unique_solution() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1]);
    solver.add_clause(vec![2]);
    assert!(solver.has_unique_solution());

    let mut solver2 = AllSatSolver::new();
    solver2.add_clause(vec![1, 2]);
    solver2.add_clause(vec![-1, -2]);
    assert!(!solver2.has_unique_solution()); // Has 2 solutions
}

#[test]
fn test_iterator_early_termination() {
    let mut solver = AllSatSolver::new();

    // x1 OR x2 OR x3 - has 7 solutions
    solver.add_clause(vec![1, 2, 3]);

    let mut count = 0;
    for _ in solver.iter() {
        count += 1;
        if count >= 3 {
            break;
        }
    }
    assert_eq!(count, 3);
}

#[test]
fn test_solution_to_literals() {
    let solution = Solution {
        assignment: vec![false, true, false, true], // x1=T, x2=F, x3=T
    };

    let lits = solution.to_literals(&[1, 2, 3]);
    assert_eq!(lits, vec![1, -2, 3]);
}

#[test]
fn test_solution_satisfies() {
    let solution = Solution {
        assignment: vec![false, true, false], // x1=T, x2=F
    };

    assert!(solution.satisfies(1)); // x1 is true
    assert!(!solution.satisfies(-1)); // NOT x1 is false
    assert!(!solution.satisfies(2)); // x2 is false
    assert!(solution.satisfies(-2)); // NOT x2 is true
}

#[test]
fn test_empty_formula() {
    let mut solver = AllSatSolver::new();
    // Empty formula with no variables
    let solutions = solver.enumerate();
    // Empty formula has one solution (the empty assignment)
    assert_eq!(solutions.len(), 1);
}

#[test]
fn test_stats() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, -2]);

    let _ = solver.enumerate();

    let stats = solver.stats();
    assert!(stats.sat_calls > 0);
    assert_eq!(stats.solutions_found, 2);
    assert_eq!(stats.blocking_clauses, 2);
}

#[test]
fn test_pigeonhole_3_2() {
    // 3 pigeons, 2 holes - no solution
    let mut solver = AllSatSolver::new();

    // p_{i,j} = pigeon i in hole j
    // Variables: p11=1, p12=2, p21=3, p22=4, p31=5, p32=6

    // Each pigeon must be in some hole
    solver.add_clause(vec![1, 2]); // p1 in h1 or h2
    solver.add_clause(vec![3, 4]); // p2 in h1 or h2
    solver.add_clause(vec![5, 6]); // p3 in h1 or h2

    // No two pigeons in same hole
    // Hole 1: at most one of p11, p21, p31
    solver.add_clause(vec![-1, -3]); // not (p11 and p21)
    solver.add_clause(vec![-1, -5]); // not (p11 and p31)
    solver.add_clause(vec![-3, -5]); // not (p21 and p31)

    // Hole 2: at most one of p12, p22, p32
    solver.add_clause(vec![-2, -4]); // not (p12 and p22)
    solver.add_clause(vec![-2, -6]); // not (p12 and p32)
    solver.add_clause(vec![-4, -6]); // not (p22 and p32)

    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 0, "Pigeonhole 3->2 should be UNSAT");
}

#[test]
fn test_pigeonhole_2_2() {
    // 2 pigeons, 2 holes - has solutions
    let mut solver = AllSatSolver::new();

    // Variables: p11=1, p12=2, p21=3, p22=4

    // Each pigeon must be in some hole
    solver.add_clause(vec![1, 2]); // p1 in h1 or h2
    solver.add_clause(vec![3, 4]); // p2 in h1 or h2

    // No two pigeons in same hole
    solver.add_clause(vec![-1, -3]); // not (p11 and p21)
    solver.add_clause(vec![-2, -4]); // not (p12 and p22)

    let solutions = solver.enumerate();
    // Solutions: p1->h1,p2->h2 and p1->h2,p2->h1
    // But also variants with "extra" positions set to false
    assert!(solutions.len() >= 2, "Should have at least 2 solutions");

    // With projection to just the "one per pigeon" decision
    let config = AllSatConfig {
        projection: Some(vec![1, 2, 3, 4]),
        ..Default::default()
    };
    let projected = solver.enumerate_with_config(config);
    // Each pigeon in exactly one hole, 2 valid arrangements
    assert!(projected.len() >= 2);
}

// ==========================================================================
// Tests for from_solver (external backend)
// ==========================================================================

#[test]
fn test_from_solver_basic() {
    use ay_sat::{Literal, Solver as SatSolver, Variable};

    // Build a SAT solver with (x0 OR x1) AND (NOT x0 OR NOT x1)
    // 0-indexed: x0, x1 → num_vars=2
    let mut sat = SatSolver::new(2);
    sat.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    sat.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]);

    let mut solver = AllSatSolver::from_solver(sat);
    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 2, "XOR of 2 vars should have 2 solutions");
}

#[test]
fn test_from_solver_projected() {
    use ay_sat::{Literal, Solver as SatSolver, Variable};

    // x0=true AND (x1 OR x2) — 3 full solutions, 1 projected to x0
    // 0-indexed variables: x0, x1, x2 → num_vars=3
    let mut sat = SatSolver::new(3);
    sat.add_clause(vec![Literal::positive(Variable::new(0))]);
    sat.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let mut solver = AllSatSolver::from_solver(sat);
    let config = AllSatConfig {
        projection: Some(vec![0]),
        ..Default::default()
    };
    let solutions = solver.enumerate_with_config(config);
    assert_eq!(
        solutions.len(),
        1,
        "Projected to x0, only one distinct assignment"
    );
    assert!(solutions[0].is_true(0));
}

#[test]
fn test_from_solver_unsat() {
    use ay_sat::{Literal, Solver as SatSolver, Variable};

    // x0 AND NOT x0 — UNSAT
    let mut sat = SatSolver::new(1);
    sat.add_clause(vec![Literal::positive(Variable::new(0))]);
    sat.add_clause(vec![Literal::negative(Variable::new(0))]);

    let mut solver = AllSatSolver::from_solver(sat);
    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 0);
}

// ==========================================================================
// Tests for enumerate_with_callback
// ==========================================================================

#[test]
fn test_enumerate_with_callback_collects_all() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, -2]);

    let mut collected = Vec::new();
    let stats = solver.enumerate_with_callback(AllSatConfig::default(), |sol| {
        collected.push(sol.clone());
        true
    });

    assert_eq!(collected.len(), 2);
    assert_eq!(stats.solutions_found, 2);
    assert!(stats.sat_calls >= 2);
}

#[test]
fn test_enumerate_with_callback_early_stop() {
    let mut solver = AllSatSolver::new();
    // (x1 OR x2) has 3 solutions
    solver.add_clause(vec![1, 2]);

    let mut count = 0;
    let stats = solver.enumerate_with_callback(AllSatConfig::default(), |_| {
        count += 1;
        count < 2 // stop after 2nd solution
    });

    assert_eq!(count, 2);
    assert_eq!(stats.solutions_found, 2);
}

#[test]
fn test_enumerate_with_callback_max_solutions() {
    let mut solver = AllSatSolver::new();
    // (x1 OR x2) has 3 solutions
    solver.add_clause(vec![1, 2]);

    let config = AllSatConfig {
        max_solutions: Some(1),
        ..Default::default()
    };
    let mut count = 0;
    let stats = solver.enumerate_with_callback(config, |_| {
        count += 1;
        true
    });

    assert_eq!(count, 1);
    assert_eq!(stats.solutions_found, 1);
}

#[test]
fn test_enumerate_with_callback_projected() {
    let mut solver = AllSatSolver::new();
    // x1 AND (x2 OR x3) — 3 full, 1 projected to x1
    solver.add_clause(vec![1]);
    solver.add_clause(vec![2, 3]);

    let config = AllSatConfig {
        projection: Some(vec![1]),
        ..Default::default()
    };
    let mut collected = Vec::new();
    solver.enumerate_with_callback(config, |sol| {
        collected.push(sol.clone());
        true
    });
    assert_eq!(collected.len(), 1);
    assert!(collected[0].is_true(1));
}

#[test]
fn test_enumerate_with_callback_from_solver() {
    use ay_sat::{Literal, Solver as SatSolver, Variable};

    // XOR: exactly one of x0, x1 true (0-indexed)
    let mut sat = SatSolver::new(2);
    sat.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    sat.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]);

    let mut solver = AllSatSolver::from_solver(sat);
    let mut collected = Vec::new();
    let stats = solver.enumerate_with_callback(AllSatConfig::default(), |sol| {
        collected.push(sol.clone());
        true
    });

    assert_eq!(collected.len(), 2);
    assert_eq!(stats.solutions_found, 2);
}

// ==========================================================================
// AllSatOutcome / cap-hit tracking tests (#8557)
// ==========================================================================

#[test]
fn test_callback_cap_hit_sets_outcome_capped() {
    let mut solver = AllSatSolver::new();
    // (x1 OR x2) has 3 solutions
    solver.add_clause(vec![1, 2]);

    let config = AllSatConfig {
        max_solutions: Some(2),
        ..Default::default()
    };
    let stats = solver.enumerate_with_callback(config, |_| true);

    assert_eq!(stats.solutions_found, 2);
    assert_eq!(stats.allsat_cap_hits, 1);
    assert_eq!(stats.outcome, AllSatOutcome::Capped);

    // Persistent stats should also reflect the cap hit
    assert_eq!(solver.stats().allsat_cap_hits, 1);
    assert_eq!(solver.stats().outcome, AllSatOutcome::Capped);
}

#[test]
fn test_callback_exhaustive_sets_outcome_exhaustive() {
    let mut solver = AllSatSolver::new();
    // (x1 OR x2) AND (NOT x1 OR NOT x2) has exactly 2 solutions
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, -2]);

    let stats = solver.enumerate_with_callback(AllSatConfig::default(), |_| true);

    assert_eq!(stats.solutions_found, 2);
    assert_eq!(stats.allsat_cap_hits, 0);
    assert_eq!(stats.outcome, AllSatOutcome::Exhaustive);
    assert_eq!(solver.stats().outcome, AllSatOutcome::Exhaustive);
}

#[test]
fn test_iterator_cap_hit_sets_outcome_capped() {
    let mut solver = AllSatSolver::new();
    // (x1 OR x2) has 3 solutions
    solver.add_clause(vec![1, 2]);

    let config = AllSatConfig {
        max_solutions: Some(2),
        ..Default::default()
    };
    let mut iter = solver.iter_with_config(config);

    // Consume the iterator
    let mut count = 0;
    while iter.next().is_some() {
        count += 1;
    }
    assert_eq!(count, 2);

    // The iterator should report Capped
    assert_eq!(iter.outcome(), AllSatOutcome::Capped);
}

#[test]
fn test_iterator_exhaustive_sets_outcome_exhaustive() {
    let mut solver = AllSatSolver::new();
    // x1 AND x2: exactly 1 solution
    solver.add_clause(vec![1]);
    solver.add_clause(vec![2]);

    let mut iter = solver.iter();
    while iter.next().is_some() {}

    assert_eq!(iter.outcome(), AllSatOutcome::Exhaustive);
}

#[test]
fn test_iterator_cap_hit_increments_stats() {
    let mut solver = AllSatSolver::new();
    // (x1 OR x2) has 3 solutions
    solver.add_clause(vec![1, 2]);

    let config = AllSatConfig {
        max_solutions: Some(1),
        ..Default::default()
    };
    let mut iter = solver.iter_with_config(config);
    while iter.next().is_some() {}

    // Stats should record the cap hit
    assert_eq!(solver.stats().allsat_cap_hits, 1);
    assert_eq!(solver.stats().outcome, AllSatOutcome::Capped);
}

#[test]
fn test_enumerate_with_config_cap_reflects_in_stats() {
    let mut solver = AllSatSolver::new();
    // (x1 OR x2 OR x3) has 7 solutions
    solver.add_clause(vec![1, 2, 3]);

    let config = AllSatConfig {
        max_solutions: Some(3),
        ..Default::default()
    };
    let solutions = solver.enumerate_with_config(config);
    assert_eq!(solutions.len(), 3);

    // After using the convenience method (which uses the iterator),
    // the stats should show the cap was hit
    assert_eq!(solver.stats().allsat_cap_hits, 1);
    assert_eq!(solver.stats().outcome, AllSatOutcome::Capped);
}

#[test]
fn test_unsat_formula_outcome_is_exhaustive() {
    let mut solver = AllSatSolver::new();
    // x1 AND NOT x1: UNSAT
    solver.add_clause(vec![1]);
    solver.add_clause(vec![-1]);

    let config = AllSatConfig {
        max_solutions: Some(10),
        ..Default::default()
    };
    let stats = solver.enumerate_with_callback(config, |_| true);

    // No solutions found, but we exhausted the space (not capped)
    assert_eq!(stats.solutions_found, 0);
    assert_eq!(stats.outcome, AllSatOutcome::Exhaustive);
    assert_eq!(stats.allsat_cap_hits, 0);
}

// ==========================================================================
// Original tests
// ==========================================================================

#[test]
fn test_xor_chain() {
    // XOR chain: x1 XOR x2 XOR x3 = true
    // (x1 XOR x2 XOR x3) encoded as CNF
    let mut solver = AllSatSolver::new();

    // x1 XOR x2 XOR x3 = 1 is equivalent to:
    // odd number of variables must be true
    // Clauses: (x1 OR x2 OR x3) AND (!x1 OR !x2 OR x3) AND (!x1 OR x2 OR !x3) AND (x1 OR !x2 OR !x3)
    solver.add_clause(vec![1, 2, 3]);
    solver.add_clause(vec![-1, -2, 3]);
    solver.add_clause(vec![-1, 2, -3]);
    solver.add_clause(vec![1, -2, -3]);

    let solutions = solver.enumerate();
    // Should have 4 solutions: TTF, TFT, FTT, FFF... wait, FFF has 0 true = even, not valid
    // Actually: TTT (3), TFF (1), FTF (1), FFT (1) = 4 solutions with odd parity
    assert_eq!(solutions.len(), 4);

    // Verify each solution has odd parity
    for sol in &solutions {
        let count = (1..=3).filter(|&v| sol.is_true(v)).count();
        assert!(count % 2 == 1, "XOR chain should have odd parity");
    }
}
