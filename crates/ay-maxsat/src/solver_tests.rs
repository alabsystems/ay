// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_simple_unweighted() {
    let mut solver = MaxSatSolver::new();

    // x1 OR x2 (hard)
    solver.add_hard_clause(vec![1, 2]);

    // Prefer x1 = true
    solver.add_soft_clause(vec![1], 1);
    // Prefer x2 = true
    solver.add_soft_clause(vec![2], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => {
            assert_eq!(cost, 0, "Should satisfy all clauses");
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_conflicting_soft_clauses() {
    let mut solver = MaxSatSolver::new();

    // Soft: x1 = true
    solver.add_soft_clause(vec![1], 1);
    // Soft: x1 = false (conflicts!)
    solver.add_soft_clause(vec![-1], 1);
    // Soft: x2 = true
    solver.add_soft_clause(vec![2], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 1, "Should violate exactly one clause");
            // x2 should be true (satisfies third clause)
            assert!(model.get(2).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_weighted() {
    let mut solver = MaxSatSolver::new();

    // Soft: x1 = true (weight 10)
    solver.add_soft_clause(vec![1], 10);
    // Soft: x1 = false (weight 1)
    solver.add_soft_clause(vec![-1], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Should prefer violating the weight-1 clause
            assert_eq!(cost, 1);
            // x1 should be true (higher weight)
            assert!(model.get(1).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_weighted_optimizes_total_cost_not_weight_strata() {
    let mut solver = MaxSatSolver::new();

    // A lexicographic stratum solver chooses x1=true and pays 12.
    // Exact weighted MaxSAT must choose x1=false and pay 10.
    solver.add_soft_clause(vec![1], 10);
    solver.add_soft_clause(vec![-1], 6);
    solver.add_soft_clause(vec![-1], 6);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 10);
            assert!(!model.get(1).copied().unwrap_or(true));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_unsatisfiable_hard() {
    let mut solver = MaxSatSolver::new();

    // Hard: x1
    solver.add_hard_clause(vec![1]);
    // Hard: !x1
    solver.add_hard_clause(vec![-1]);

    let result = solver.solve();
    assert_eq!(result, MaxSatResult::Unsatisfiable);
}

#[test]
fn test_only_hard_clauses() {
    let mut solver = MaxSatSolver::new();

    solver.add_hard_clause(vec![1, 2]);
    solver.add_hard_clause(vec![-1, 2]);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 0);
            // x2 must be true to satisfy both
            assert!(model.get(2).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_only_soft_clauses() {
    let mut solver = MaxSatSolver::new();

    solver.add_soft_clause(vec![1], 1);
    solver.add_soft_clause(vec![2], 1);
    solver.add_soft_clause(vec![3], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Check that we can satisfy all soft clauses
            assert_eq!(cost, 0);
            // All should be true
            assert!(model.get(1).copied().unwrap_or(false));
            assert!(model.get(2).copied().unwrap_or(false));
            assert!(model.get(3).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_partial_maxsat() {
    let mut solver = MaxSatSolver::new();

    // Hard: at most one of x1, x2, x3 (encoded)
    // !x1 OR !x2
    solver.add_hard_clause(vec![-1, -2]);
    // !x1 OR !x3
    solver.add_hard_clause(vec![-1, -3]);
    // !x2 OR !x3
    solver.add_hard_clause(vec![-2, -3]);

    // Soft: want all three
    solver.add_soft_clause(vec![1], 1);
    solver.add_soft_clause(vec![2], 1);
    solver.add_soft_clause(vec![3], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Can only satisfy 1 soft clause
            assert_eq!(cost, 2);
            // Exactly one should be true
            let count: usize = (1..=3)
                .filter(|&i| model.get(i).copied().unwrap_or(false))
                .count();
            assert_eq!(count, 1);
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_empty_instance() {
    let mut solver = MaxSatSolver::new();
    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => {
            assert_eq!(cost, 0);
        }
        _ => panic!("Expected optimal solution for empty instance"),
    }
}

#[test]
fn test_stats() {
    let mut solver = MaxSatSolver::new();

    solver.add_soft_clause(vec![1], 1);
    solver.add_soft_clause(vec![-1], 1);

    solver.solve();

    let stats = solver.stats();
    assert!(stats.sat_calls > 0, "Should have made SAT calls");
}

#[test]
fn test_default_trait() {
    let mut solver = MaxSatSolver::default();
    solver.add_soft_clause(vec![1], 1);
    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => assert_eq!(cost, 0),
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_sequential_counter_encoding() {
    // 8 soft clauses triggers sequential counter (n > 6 && k > 1)
    let mut solver = MaxSatSolver::new();

    // Hard: at most one of x1..x8
    for i in 1_i32..=8 {
        for j in (i + 1)..=8 {
            solver.add_hard_clause(vec![-i, -j]);
        }
    }

    // Soft: want all 8 to be true
    for i in 1_i32..=8 {
        solver.add_soft_clause(vec![i], 1);
    }

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Can only satisfy 1 soft clause (at-most-one hard constraint)
            assert_eq!(cost, 7);
            let count: usize = (1..=8)
                .filter(|&i| model.get(i).copied().unwrap_or(false))
                .count();
            assert_eq!(count, 1);
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_multi_stratum_weighted() {
    // 3 distinct weights to exercise stratified solver
    let mut solver = MaxSatSolver::new();

    // x1 = true (high priority)
    solver.add_soft_clause(vec![1], 100);
    // x1 = false (medium priority)
    solver.add_soft_clause(vec![-1], 10);
    // x2 = true (low priority)
    solver.add_soft_clause(vec![2], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Should violate weight-10 clause (x1 = false)
            assert_eq!(cost, 10);
            // x1 = true (weight 100 > weight 10)
            assert!(model.get(1).copied().unwrap_or(false));
            // x2 = true (no conflict)
            assert!(model.get(2).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_stratified_conditions_lower_strata_on_higher_bounds() {
    // Both weight-100 softs must be satisfied, forcing the weight-10
    // soft (¬x1 ∨ ¬x2) to be violated: stratification must not let the
    // lower stratum override the higher one.
    let mut solver = MaxSatSolver::new();
    solver.add_soft_clause(vec![1], 100);
    solver.add_soft_clause(vec![2], 100);
    solver.add_soft_clause(vec![-1, -2], 10);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 10, "optimal violates only the weight-10 soft");
            assert!(model.get(1).copied().unwrap_or(false));
            assert!(model.get(2).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_weighted_partial_maxsat() {
    // Hard clauses + unit-weight soft clauses (binary search path)
    let mut solver = MaxSatSolver::new();

    // Hard: x1 OR x2
    solver.add_hard_clause(vec![1, 2]);
    // Hard: x3 OR x4
    solver.add_hard_clause(vec![3, 4]);

    // Soft: prefer all false (conflicting with hard)
    solver.add_soft_clause(vec![-1], 1);
    solver.add_soft_clause(vec![-2], 1);
    solver.add_soft_clause(vec![-3], 1);
    solver.add_soft_clause(vec![-4], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Must satisfy hard: x1 OR x2, x3 OR x4
            let x1 = model.get(1).copied().unwrap_or(false);
            let x2 = model.get(2).copied().unwrap_or(false);
            let x3 = model.get(3).copied().unwrap_or(false);
            let x4 = model.get(4).copied().unwrap_or(false);
            assert!(x1 || x2, "Hard clause x1 OR x2 violated");
            assert!(x3 || x4, "Hard clause x3 OR x4 violated");
            // Minimum 2 violations (one from each hard pair)
            assert_eq!(cost, 2);
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_single_variable() {
    let mut solver = MaxSatSolver::new();
    solver.add_soft_clause(vec![1], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 0);
            assert!(model.get(1).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_all_soft_conflicting() {
    // Every pair of soft clauses conflicts
    let mut solver = MaxSatSolver::new();

    // x1, NOT x1, x2, NOT x2
    solver.add_soft_clause(vec![1], 1);
    solver.add_soft_clause(vec![-1], 1);
    solver.add_soft_clause(vec![2], 1);
    solver.add_soft_clause(vec![-2], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => {
            assert_eq!(cost, 2, "Must violate exactly 2 of 4 conflicting clauses");
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_hard_subsumes_soft() {
    // Hard clause forces assignment, soft agrees
    let mut solver = MaxSatSolver::new();

    // Hard: x1 must be true
    solver.add_hard_clause(vec![1]);
    // Soft: prefer x1 = true (already forced)
    solver.add_soft_clause(vec![1], 1);
    // Soft: prefer x1 = false (violated by hard)
    solver.add_soft_clause(vec![-1], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 1);
            assert!(model.get(1).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_large_clause_soft() {
    let mut solver = MaxSatSolver::new();

    // Soft: x1 OR x2 OR x3 OR x4 OR x5 (easy to satisfy)
    solver.add_soft_clause(vec![1, 2, 3, 4, 5], 1);
    // Soft: NOT x1 OR NOT x2 OR ... (all negative lits - also easy to satisfy)
    solver.add_soft_clause(vec![-1, -2, -3, -4, -5], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => {
            assert_eq!(cost, 0, "Both large clauses should be satisfiable");
        }
        _ => panic!("Expected optimal solution"),
    }
}

/// Deterministic LCG for reproducible randomized instances.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        // Numerical Recipes LCG constants
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Brute-force optimum over all 2^n assignments; None if hard-UNSAT.
fn brute_force_optimum(num_vars: u32, hard: &[Vec<i32>], soft: &[(u64, Vec<i32>)]) -> Option<u64> {
    let clause_sat = |clause: &[i32], bits: u64| {
        clause.iter().any(|&lit| {
            let var = lit.unsigned_abs();
            let val = (bits >> (var - 1)) & 1 == 1;
            (lit > 0) == val
        })
    };
    let mut best: Option<u64> = None;
    for bits in 0..(1u64 << num_vars) {
        if hard.iter().any(|c| !clause_sat(c, bits)) {
            continue;
        }
        let cost: u64 = soft
            .iter()
            .filter(|(_, c)| !clause_sat(c, bits))
            .map(|(w, _)| *w)
            .sum();
        best = Some(best.map_or(cost, |b: u64| b.min(cost)));
    }
    best
}

/// Cross-check the OLL engine against brute force on random weighted
/// partial instances. Small sizes, many seeds: exercises cores, weight
/// splitting, totalizer bounds, stratification, and hardening.
#[test]
fn test_random_cross_check_brute_force() {
    for seed in 0..500u64 {
        let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1));
        let num_vars = 3 + rng.below(6) as u32; // 3..8
        let num_hard = rng.below(6) as usize;
        let num_soft = 1 + rng.below(12) as usize;

        let gen_clause = |rng: &mut Lcg| -> Vec<i32> {
            let len = 1 + rng.below(3) as usize;
            (0..len)
                .map(|_| {
                    let v = 1 + rng.below(num_vars as u64) as i32;
                    if rng.below(2) == 0 {
                        v
                    } else {
                        -v
                    }
                })
                .collect()
        };

        let hard: Vec<Vec<i32>> = (0..num_hard).map(|_| gen_clause(&mut rng)).collect();
        let soft: Vec<(u64, Vec<i32>)> = (0..num_soft)
            .map(|_| (1 + rng.below(20), gen_clause(&mut rng)))
            .collect();

        let expected = brute_force_optimum(num_vars, &hard, &soft);

        let mut solver = MaxSatSolver::new();
        for c in &hard {
            solver.add_hard_clause(c.clone());
        }
        for (w, c) in &soft {
            solver.add_soft_clause(c.clone(), *w);
        }

        match (solver.solve(), expected) {
            (MaxSatResult::Optimal { cost, model }, Some(exp)) => {
                assert_eq!(
                    cost, exp,
                    "seed {seed}: OLL cost {cost} != brute force {exp}\nhard: {hard:?}\nsoft: {soft:?}",
                );
                // The reported model must itself achieve the reported cost.
                let model_cost: u64 = soft
                    .iter()
                    .filter(|(_, c)| {
                        !c.iter().any(|&lit| {
                            let idx = lit.unsigned_abs() as usize;
                            model.get(idx).copied().unwrap_or(false) == (lit > 0)
                        })
                    })
                    .map(|(w, _)| *w)
                    .sum();
                assert_eq!(
                    model_cost, exp,
                    "seed {seed}: model does not achieve optimal cost\nhard: {hard:?}\nsoft: {soft:?}",
                );
                // The model must satisfy every hard clause.
                for c in &hard {
                    assert!(
                        c.iter().any(|&lit| {
                            let idx = lit.unsigned_abs() as usize;
                            model.get(idx).copied().unwrap_or(false) == (lit > 0)
                        }),
                        "seed {seed}: model violates hard clause {c:?}",
                    );
                }
            }
            (MaxSatResult::Unsatisfiable, None) => {}
            (got, exp) => panic!(
                "seed {seed}: OLL {got:?} vs brute force {exp:?}\nhard: {hard:?}\nsoft: {soft:?}",
            ),
        }
    }
}

/// Large-optimum unit-weight instance: exercises the LSU descent (OLL alone
/// needs one core per cost unit). Every window of 3 consecutive variables
/// allows at most 2 true, so at most 2/3 of the 600 prefer-true softs can be
/// satisfied: optimum cost = 200.
#[test]
fn test_large_optimum_lsu_descent() {
    let n: i32 = 600;
    let mut solver = MaxSatSolver::new();
    for i in 1..=(n - 2) {
        solver.add_hard_clause(vec![-i, -(i + 1), -(i + 2)]);
    }
    for i in 1..=n {
        solver.add_soft_clause(vec![i], 1);
    }
    match solver.solve() {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 200);
            // Model must satisfy every hard window constraint.
            for i in 1..=(n - 2) as usize {
                let t = |v: usize| model.get(v).copied().unwrap_or(false);
                assert!(!(t(i) && t(i + 1) && t(i + 2)), "window at {i} has 3 true");
            }
        }
        other => panic!("expected optimal, got {other:?}"),
    }
}
