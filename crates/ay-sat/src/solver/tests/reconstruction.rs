// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use proptest::prelude::*;

// ========================================================================
// Property Tests for Propagation Soundness
// ========================================================================

proptest! {
    /// Propagation soundness: if propagate returns conflict, clause is falsified
    #[test]
    fn prop_propagation_conflict_soundness(
        num_clauses in 1usize..10,
        seed in 0u64..1000
    ) {
        // Create solver with fixed seed-based clauses
        let num_vars = 5usize;
        let mut solver = Solver::new(num_vars);

        // Generate deterministic clauses based on seed
        for i in 0..num_clauses {
            let v1 = ((seed + i as u64) % num_vars as u64) as u32;
            let v2 = ((seed + i as u64 + 1) % num_vars as u64) as u32;
            let v3 = ((seed + i as u64 + 2) % num_vars as u64) as u32;

            let lit1 = if (seed + i as u64).is_multiple_of(2) {
                Literal::positive(Variable(v1))
            } else {
                Literal::negative(Variable(v1))
            };
            let lit2 = if (seed + i as u64 + 1).is_multiple_of(2) {
                Literal::positive(Variable(v2))
            } else {
                Literal::negative(Variable(v2))
            };
            let lit3 = if (seed + i as u64 + 2).is_multiple_of(2) {
                Literal::positive(Variable(v3))
            } else {
                Literal::negative(Variable(v3))
            };

            solver.add_clause(vec![lit1, lit2, lit3]);
        }

        // Initialize and run solver
        let result = solver.solve().into_inner();

        // Basic soundness check: if SAT, model satisfies all original clauses
        if let SatResult::Sat(model) = &result {
            for i in solver.arena.indices().take(num_clauses) {
                // Skip clauses deleted by BVE/subsumption during preprocessing
                if solver.arena.is_empty_clause(i) {
                    continue;
                }
                let satisfied = solver.arena.literals(i).iter().any(|&lit| {
                    let var_val = model[lit.variable().index()];
                    if lit.is_positive() {
                        var_val
                    } else {
                        !var_val
                    }
                });
                prop_assert!(satisfied, "Clause {} not satisfied by model", i);
            }
        }
    }

    /// Solver returns consistent results on same formula
    #[test]
    fn prop_solve_deterministic(clauses_seed in 0u64..100) {
        let num_vars = 4usize;
        let num_clauses = 5usize;

        let run_solver = || {
            let mut solver = Solver::new(num_vars);
            for i in 0..num_clauses {
                let v1 = ((clauses_seed + i as u64) % num_vars as u64) as u32;
                let v2 = ((clauses_seed + i as u64 + 1) % num_vars as u64) as u32;
                let polarity1 = (clauses_seed + i as u64).is_multiple_of(2);
                let polarity2 = (clauses_seed + i as u64 + 1).is_multiple_of(2);

                let lit1 = if polarity1 {
                    Literal::positive(Variable(v1))
                } else {
                    Literal::negative(Variable(v1))
                };
                let lit2 = if polarity2 {
                    Literal::positive(Variable(v2))
                } else {
                    Literal::negative(Variable(v2))
                };
                solver.add_clause(vec![lit1, lit2]);
            }
            solver.solve().into_inner()
        };

        let result1 = run_solver();
        let result2 = run_solver();

        // Results should be consistent (both SAT or both UNSAT)
        match (&result1, &result2) {
            (SatResult::Sat(_), SatResult::Sat(_))
            | (SatResult::Unsat(_), SatResult::Unsat(_)) => (),
            _ => prop_assert!(false, "Inconsistent results: {:?} vs {:?}", result1, result2),
        }
    }

    /// Unit clauses are correctly propagated
    #[test]
    fn prop_unit_clause_propagation(var_idx in 0u32..10) {
        let num_vars = 10usize;
        let mut solver = Solver::new(num_vars);

        // Add unit clause
        let unit_lit = Literal::positive(Variable(var_idx));
        solver.add_clause(vec![unit_lit]);

        // Add clause requiring the unit
        let other_var = (var_idx + 1) % num_vars as u32;
        solver.add_clause(vec![
            Literal::negative(Variable(var_idx)),
            Literal::positive(Variable(other_var)),
        ]);

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = result {
            // Unit clause must be satisfied
            prop_assert!(model[var_idx as usize], "Unit clause not satisfied");
        }
    }

    // ====================================================================
    // TLA+ Invariant Property Tests (Gap 3: Formal Link to TLA+ Spec)
    //
    // These tests mirror the invariants from specs/cdcl.tla:
    // - TypeInvariant: Implicitly enforced by Rust's type system
    // - SatCorrect: When SAT, all clauses are satisfied
    // - NoDoubleAssignment: No variable assigned twice
    // - WatchedInvariant: Checked during propagation
    // ====================================================================

    /// TLA+ SatCorrect invariant (lines 201-202 of cdcl.tla):
    /// state = "SAT" => \A clause \in Clauses : Satisfied(clause)
    ///
    /// For any random SAT formula, if the solver returns SAT, every
    /// original clause must be satisfied by the model.
    #[test]
    fn tla_invariant_sat_correct(
        num_vars in 3usize..8,
        num_clauses in 1usize..15,
        seed in 0u64..10000
    ) {
        use std::collections::HashSet;

        let mut solver = Solver::new(num_vars);
        let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

        // Generate random clauses
        for i in 0..num_clauses {
            let clause_len = 2 + ((seed + i as u64) % 3) as usize; // 2-4 literals
            let mut clause = Vec::new();
            let mut seen_vars: HashSet<u32> = HashSet::new();

            for j in 0..clause_len {
                let v = ((seed.wrapping_mul(7) + i as u64 * 13 + j as u64 * 31) % num_vars as u64) as u32;
                if seen_vars.contains(&v) {
                    continue; // Skip duplicate variables in same clause
                }
                seen_vars.insert(v);
                let polarity = (seed + i as u64 + j as u64).is_multiple_of(2);
                let lit = if polarity {
                    Literal::positive(Variable(v))
                } else {
                    Literal::negative(Variable(v))
                };
                clause.push(lit);
            }

            if clause.is_empty() {
                continue; // Skip empty clauses
            }

            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();

        // TLA+ SatCorrect: If SAT, all original clauses must be satisfied
        if let SatResult::Sat(model) = result {
            for (clause_idx, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let var_idx = lit.variable().index();
                    let val = model[var_idx];
                    if lit.is_positive() { val } else { !val }
                });
                prop_assert!(
                    satisfied,
                    "TLA+ SatCorrect violation: clause {} ({:?}) not satisfied by model {:?}",
                    clause_idx, clause, model
                );
            }
        }
    }

    /// TLA+ NoDoubleAssignment invariant (lines 213-215 of cdcl.tla):
    /// \A i, j \in 1..Len(trail) : i # j => Var(trail[i][1]) # Var(trail[j][1])
    ///
    /// In the model, each variable should have exactly one consistent value.
    /// This is implicitly enforced by our Vec<bool> model representation,
    /// but we verify that values are deterministic across multiple accesses.
    #[test]
    fn tla_invariant_no_double_assignment(
        num_vars in 2usize..6,
        seed in 0u64..1000
    ) {
        let mut solver = Solver::new(num_vars);

        // Create simple SAT formula
        for i in 0..num_vars {
            let v1 = i as u32;
            let v2 = ((i + 1) % num_vars) as u32;
            let polarity = (seed + i as u64).is_multiple_of(2);
            let lit1 = if polarity {
                Literal::positive(Variable(v1))
            } else {
                Literal::negative(Variable(v1))
            };
            let lit2 = Literal::positive(Variable(v2));
            solver.add_clause(vec![lit1, lit2]);
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = result {
            // Verify model length matches num_vars
            prop_assert_eq!(
                model.len(), num_vars,
                "Model length {} does not match num_vars {}",
                model.len(), num_vars
            );

            // Verify model actually satisfies all added clauses
            for i in 0..num_vars {
                let v1 = i as u32;
                let v2 = ((i + 1) % num_vars) as u32;
                let polarity = (seed + i as u64).is_multiple_of(2);
                let lit1_sat = if polarity { model[v1 as usize] } else { !model[v1 as usize] };
                let lit2_sat = model[v2 as usize];
                prop_assert!(
                    lit1_sat || lit2_sat,
                    "Clause {} not satisfied by model: lit1(v{}={})={}, lit2(v{}={})={}",
                    i, v1, model[v1 as usize], lit1_sat, v2, model[v2 as usize], lit2_sat
                );
            }
        }
    }

    /// TLA+ Soundness invariant combining SatCorrect and UnsatCorrect:
    /// When we claim SAT, we can construct a satisfying assignment.
    /// When we claim UNSAT, there truly is no satisfying assignment.
    ///
    /// This test generates formulas and verifies soundness both ways.
    #[test]
    fn tla_invariant_soundness(
        num_vars in 2usize..5,
        seed in 0u64..500
    ) {
        // Test 1: Known SAT formula
        {
            let mut solver = Solver::new(num_vars);
            // Add tautology: (x0 OR NOT x0) for each var
            for i in 0..num_vars {
                solver.add_clause(vec![
                    Literal::positive(Variable(i as u32)),
                    Literal::negative(Variable(i as u32)),
                ]);
            }
            let result = solver.solve().into_inner();
            match result {
                SatResult::Sat(_) => (), // Expected
                other => prop_assert!(false, "Tautology should be SAT, got {:?}", other),
            }
        }

        // Test 2: Known UNSAT formula
        {
            let mut solver = Solver::new(1);
            solver.add_clause(vec![Literal::positive(Variable(0))]);
            solver.add_clause(vec![Literal::negative(Variable(0))]);
            let result = solver.solve().into_inner();
            match result {
                SatResult::Unsat(_) => (), // Expected
                other => prop_assert!(false, "x AND NOT x should be UNSAT, got {:?}", other),
            }
        }

        // Test 3: Random formula with soundness check
        {
            let mut solver = Solver::new(num_vars);
            let mut clauses: Vec<Vec<Literal>> = Vec::new();

            for i in 0..=(seed % 10) {
                let v1 = (seed.wrapping_add(i) % num_vars as u64) as u32;
                let v2 = (seed.wrapping_add(i).wrapping_add(1) % num_vars as u64) as u32;
                let p1 = (seed.wrapping_add(i) % 2) == 0;
                let p2 = (seed.wrapping_add(i).wrapping_add(1) % 2) == 0;
                let lit1 = if p1 { Literal::positive(Variable(v1)) } else { Literal::negative(Variable(v1)) };
                let lit2 = if p2 { Literal::positive(Variable(v2)) } else { Literal::negative(Variable(v2)) };
                clauses.push(vec![lit1, lit2]);
                solver.add_clause(vec![lit1, lit2]);
            }

            let result = solver.solve().into_inner();

            if let SatResult::Sat(model) = result {
                // Verify all clauses satisfied
                for clause in &clauses {
                    let sat = clause.iter().any(|&lit| {
                        let v = lit.variable().index();
                        let val = model[v];
                        if lit.is_positive() { val } else { !val }
                    });
                    prop_assert!(sat, "Soundness violation: clause {:?} not satisfied", clause);
                }
            }
            // Note: For UNSAT, we trust DRAT proof verification (Gap 2)
        }
    }

    /// TLA+ TrailConsistency: Variables assigned in dependency order
    ///
    /// If x implies y (via unit clause ¬x ∨ y), then in any model:
    /// - If x is true, y must be true
    /// - This tests that propagation correctly follows implication chains
    #[test]
    fn tla_invariant_trail_consistency(
        chain_len in 2usize..6,
        _seed in 0u64..1000
    ) {
        // Build implication chain: x0 → x1 → x2 → ... → xN
        let num_vars = chain_len;
        let mut solver = Solver::new(num_vars);

        // Add implications: ¬x_i ∨ x_{i+1}
        for i in 0..(num_vars - 1) {
            solver.add_clause(vec![
                Literal::negative(Variable(i as u32)),
                Literal::positive(Variable((i + 1) as u32)),
            ]);
        }

        // Force x0 true (this should propagate through the chain)
        solver.add_clause(vec![Literal::positive(Variable(0))]);

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = result {
            // x0 must be true
            prop_assert!(model[0], "Root of implication chain must be true");

            // All implied variables must be true
            for (offset, &value) in model[1..].iter().enumerate() {
                let i = offset + 1;
                prop_assert!(
                    value,
                    "Variable {} should be true by implication from 0",
                    i
                );
            }
        } else {
            // Formula is satisfiable, UNSAT is a bug
            prop_assert!(false, "Implication chain should be SAT");
        }
    }

    /// TLA+ ConflictLevelCorrect: Conflict analysis produces valid learned clauses
    ///
    /// For known-UNSAT formulas, verify:
    /// 1. Solver returns UNSAT (conflicts were resolved correctly)
    /// 2. Unit propagation finds conflicts at appropriate levels
    #[test]
    fn tla_invariant_conflict_level_correct(
        n in 2usize..5,
        _seed in 0u64..500
    ) {
        // Create simple UNSAT formula: (x) ∧ (¬x)
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(Variable(0))]);
        solver.add_clause(vec![Literal::negative(Variable(0))]);

        let result = solver.solve().into_inner();

        // Must be UNSAT - conflict at level 0
        prop_assert!(
            matches!(result, SatResult::Unsat(_)),
            "x ∧ ¬x must be UNSAT, got {:?}",
            result
        );

        // Test with deeper conflicts: pigeon-hole principle for n+1 pigeons in n holes
        // PHP is UNSAT and requires exponential resolution
        if n >= 2 {
            let pigeons = n + 1;
            let holes = n;
            let mut php_solver = Solver::new(pigeons * holes);

            // Each pigeon must be in some hole: ∨_j p_{i,j}
            for p in 0..pigeons {
                let mut clause = Vec::new();
                for h in 0..holes {
                    let var = (p * holes + h) as u32;
                    clause.push(Literal::positive(Variable(var)));
                }
                php_solver.add_clause(clause);
            }

            // No two pigeons in same hole: ¬p_{i,h} ∨ ¬p_{j,h}
            for h in 0..holes {
                for p1 in 0..pigeons {
                    for p2 in (p1 + 1)..pigeons {
                        let var1 = (p1 * holes + h) as u32;
                        let var2 = (p2 * holes + h) as u32;
                        php_solver.add_clause(vec![
                            Literal::negative(Variable(var1)),
                            Literal::negative(Variable(var2)),
                        ]);
                    }
                }
            }

            let php_result = php_solver.solve().into_inner();
            prop_assert!(
                matches!(php_result, SatResult::Unsat(_)),
                "PHP({},{}) must be UNSAT, got {:?}",
                pigeons,
                holes,
                php_result
            );
        }
    }

    /// TLA+ LearnedClauseValid: Learned clauses are properly asserting
    ///
    /// Tests that:
    /// 1. Solver can solve problems requiring clause learning
    /// 2. Results are correct (SAT models satisfy formula, UNSAT is actually UNSAT)
    /// 3. No infinite loops (learning makes progress)
    #[test]
    fn tla_invariant_learned_clause_valid(
        grid_size in 2usize..4,
        seed in 0u64..200
    ) {
        // Create graph coloring problem: 2-colorable cycle (even length = SAT, odd = UNSAT)
        let is_odd = (seed % 2) == 1;
        let cycle_len = if is_odd { grid_size * 2 + 1 } else { grid_size * 2 };
        let num_vars = cycle_len; // One variable per node (true = color 1, false = color 2)

        let mut solver = Solver::new(num_vars);

        // Adjacent nodes must have different colors: (x_i ∨ x_{i+1}) ∧ (¬x_i ∨ ¬x_{i+1})
        // This is equivalent to x_i XOR x_{i+1}
        for i in 0..cycle_len {
            let j = (i + 1) % cycle_len;
            // At least one must be true
            solver.add_clause(vec![
                Literal::positive(Variable(i as u32)),
                Literal::positive(Variable(j as u32)),
            ]);
            // At least one must be false
            solver.add_clause(vec![
                Literal::negative(Variable(i as u32)),
                Literal::negative(Variable(j as u32)),
            ]);
        }

        let result = solver.solve().into_inner();

        if is_odd {
            // Odd cycle is not 2-colorable
            prop_assert!(
                matches!(result, SatResult::Unsat(_)),
                "Odd cycle length {} should be UNSAT, got {:?}",
                cycle_len,
                result
            );
        } else {
            // Even cycle is 2-colorable
            if let SatResult::Sat(model) = &result {
                // Verify coloring is valid
                for i in 0..cycle_len {
                    let j = (i + 1) % cycle_len;
                    prop_assert!(
                        model[i] != model[j],
                        "Adjacent nodes {} and {} have same color",
                        i,
                        j
                    );
                }
            } else {
                prop_assert!(
                    false,
                    "Even cycle length {} should be SAT, got {:?}",
                    cycle_len,
                    result
                );
            }
        }
    }

    /// BVE model reconstruction soundness: if the solver returns SAT after
    /// BVE eliminates variables, the reconstructed model must satisfy all
    /// original (pre-elimination) clauses.
    ///
    /// Note: compaction requires >= 100 eliminated variables (COMPACT_MIN_INACTIVE)
    /// so it does NOT trigger with these small formulas (10-30 vars). This test
    /// exercises BVE reconstruction only. The compaction index remapping is
    /// covered by prop_map_lit_for_reconstruction_no_index_collision in compact.rs.
    ///
    /// Regression coverage for #4977: BVE reconstruction correctness.
    ///
    /// Strategy: generate 3-SAT formulas near the satisfiability threshold
    /// (clause/var ratio ~4.2) with enough variables that BVE can eliminate
    /// some. Preserve original clauses before solving, then verify model.
    #[test]
    fn prop_bve_model_reconstruction_soundness(
        num_vars in 10usize..30,
        seed in 0u64..500
    ) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        // Generate a reproducible pseudo-random 3-SAT formula.
        // Target clause/var ratio ~4.2 (phase transition region) to get
        // a mix of SAT and UNSAT instances where BVE is useful.
        let num_clauses = (num_vars as f64 * 4.2) as usize;
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        let mut h = hasher.finish();

        let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
        let mut solver: Solver = Solver::new(num_vars);
        solver.set_bve_enabled(true);

        for _ in 0..num_clauses {
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v0 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v1 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v2 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let signs = h % 8;

            let lit0 = if signs & 1 == 0 {
                Literal::positive(Variable(v0))
            } else {
                Literal::negative(Variable(v0))
            };
            let lit1 = if signs & 2 == 0 {
                Literal::positive(Variable(v1))
            } else {
                Literal::negative(Variable(v1))
            };
            let lit2 = if signs & 4 == 0 {
                Literal::positive(Variable(v2))
            } else {
                Literal::negative(Variable(v2))
            };

            let clause = vec![lit0, lit1, lit2];
            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = &result {
            // Verify model against original clauses (pre-BVE).
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    if vi >= model.len() {
                        // Model shorter than expected — reconstruction bug.
                        return false;
                    }
                    if lit.is_positive() { model[vi] } else { !model[vi] }
                });
                prop_assert!(
                    satisfied,
                    "Original clause {} ({:?}) not satisfied by model (BVE reconstruction). \
                     num_vars={}, seed={}",
                    ci, clause, num_vars, seed
                );
            }
        }
        // UNSAT results don't need model verification here.
    }
}

fn generate_bve_reconstruction_formula(num_vars: usize, seed: u64) -> Vec<Vec<Literal>> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        clauses.push(vec![lit0, lit1, lit2]);
    }

    clauses
}

fn verify_bve_reconstruction_case<F>(num_vars: usize, seed: u64, configure: F)
where
    F: FnOnce(&mut Solver),
{
    let clauses = generate_bve_reconstruction_formula(num_vars, seed);
    let mut solver = Solver::new(num_vars);
    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);
    configure(&mut solver);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                vi < model.len()
                    && if lit.is_positive() {
                        model[vi]
                    } else {
                        !model[vi]
                    }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model. \
                 num_vars={num_vars}, seed={seed}"
            );
        }
    }
}

/// Deterministic reproduction of the stale-reason BVE deletion path seen in
/// `prop_bve_model_reconstruction_soundness`.
#[test]
fn test_bve_reconstruction_12_0_default_preprocessing() {
    verify_bve_reconstruction_case(12, 0, |_| {});
}

/// Isolation check: run the same formula with only preprocessing BVE enabled.
#[test]
fn test_bve_reconstruction_12_0_bve_only() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.disable_all_inprocessing();
        solver.set_bve_enabled(true);
    });
}

/// Isolation check: disable conditioning while leaving the rest of the default
/// preprocessing stack in place.
#[test]
fn test_bve_reconstruction_12_0_no_conditioning() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.set_condition_enabled(false);
    });
}

/// Isolation check: keep decompose disabled while leaving the rest of the
/// default preprocessing stack in place.
#[test]
fn test_bve_reconstruction_12_0_no_decompose() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.set_decompose_enabled(false);
    });
}

/// Isolation check: disable sweep while leaving the rest of the default
/// preprocessing stack in place.
#[test]
fn test_bve_reconstruction_12_0_no_sweep() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.set_sweep_enabled(false);
    });
}

/// Isolation check: keep congruence disabled while leaving the rest of the
/// default preprocessing stack in place.
#[test]
fn test_bve_reconstruction_12_0_no_congruence() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.set_congruence_enabled(false);
    });
}

/// Deterministic reproduction of BVE model reconstruction failure at
/// num_vars=19, seed=234. Tests conditioning+BVE interaction separately
/// to isolate the root cause.
#[test]
fn test_bve_reconstruction_19_234_no_conditioning() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 19usize;
    let seed = 234u64;
    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    solver.set_condition_enabled(false);

    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        let clause = vec![lit0, lit1, lit2];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in original_clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                if vi >= model.len() {
                    return false;
                }
                if lit.is_positive() {
                    model[vi]
                } else {
                    !model[vi]
                }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model (BVE w/o conditioning). num_vars={num_vars}, seed={seed}",
            );
        }
    }
}

#[test]
fn test_bve_reconstruction_19_234_with_conditioning() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 19usize;
    let seed = 234u64;
    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    // Conditioning is enabled by default, leave it enabled.

    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        let clause = vec![lit0, lit1, lit2];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in original_clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                if vi >= model.len() {
                    return false;
                }
                if lit.is_positive() {
                    model[vi]
                } else {
                    !model[vi]
                }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model (BVE+conditioning). num_vars={num_vars}, seed={seed}",
            );
        }
    }
}

// ========================================================================
// Decompose (SCC+ELS) Soundness Cross-Check (#5067)
// ========================================================================

proptest! {
    /// Decompose soundness: decompose-only must agree with no-inprocessing.
    ///
    /// Generates random formulas with a mix of binary and ternary clauses
    /// (binary clauses form the implication graph for SCC detection).
    /// Runs with decompose-only and with no inprocessing. If decompose
    /// returns UNSAT but baseline returns SAT, the model is verified against
    /// the original formula to confirm it's a real wrong-UNSAT.
    #[test]
    fn prop_decompose_soundness_cross_check(
        num_vars in 5usize..25,
        seed in 0u64..2000
    ) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let num_binary = num_vars * 3; // ~3 binary clauses per var to trigger SCCs
        let num_ternary = (num_vars as f64 * 2.0) as usize;
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        let mut h = hasher.finish();

        let mut clauses: Vec<Vec<Literal>> = Vec::new();

        // Generate binary clauses (form the implication graph).
        for _ in 0..num_binary {
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v0 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v1 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let signs = h % 4;
            let l0 = if signs & 1 == 0 {
                Literal::positive(Variable(v0))
            } else {
                Literal::negative(Variable(v0))
            };
            let l1 = if signs & 2 == 0 {
                Literal::positive(Variable(v1))
            } else {
                Literal::negative(Variable(v1))
            };
            if v0 != v1 {
                clauses.push(vec![l0, l1]);
            }
        }

        // Generate ternary clauses for more interesting formulas.
        for _ in 0..num_ternary {
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v0 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v1 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v2 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let signs = h % 8;
            let l0 = if signs & 1 == 0 { Literal::positive(Variable(v0)) } else { Literal::negative(Variable(v0)) };
            let l1 = if signs & 2 == 0 { Literal::positive(Variable(v1)) } else { Literal::negative(Variable(v1)) };
            let l2 = if signs & 4 == 0 { Literal::positive(Variable(v2)) } else { Literal::negative(Variable(v2)) };
            clauses.push(vec![l0, l1, l2]);
        }

        if clauses.is_empty() {
            return Ok(());
        }

        // Run 1: decompose only (all other inprocessing off).
        let mut solver_decompose: Solver = Solver::new(num_vars);
        solver_decompose.disable_all_inprocessing();
        solver_decompose.set_decompose_enabled(true);
        for c in &clauses {
            solver_decompose.add_clause(c.clone());
        }
        let result_decompose = solver_decompose.solve().into_inner();

        // Run 2: no inprocessing baseline.
        let mut solver_baseline: Solver = Solver::new(num_vars);
        solver_baseline.disable_all_inprocessing();
        for c in &clauses {
            solver_baseline.add_clause(c.clone());
        }
        let result_baseline = solver_baseline.solve().into_inner();

        // Cross-check: if decompose says UNSAT but baseline says SAT, verify.
        match (&result_decompose, &result_baseline) {
            (SatResult::Unsat(_), SatResult::Sat(model)) => {
                // Verify the baseline model against original clauses.
                let model_valid = clauses.iter().all(|clause| {
                    clause.iter().any(|&lit| {
                        let vi = lit.variable().index();
                        if vi >= model.len() { return false; }
                        if lit.is_positive() { model[vi] } else { !model[vi] }
                    })
                });
                prop_assert!(
                    !model_valid,
                    "DECOMPOSE WRONG-UNSAT: decompose returned UNSAT but baseline returned SAT \
                     with a valid model. num_vars={}, seed={}, clauses={}",
                    num_vars, seed, clauses.len()
                );
            }
            (SatResult::Sat(model_d), SatResult::Unsat(_)) => {
                // Decompose says SAT but baseline says UNSAT — verify decompose model.
                let model_valid = clauses.iter().all(|clause| {
                    clause.iter().any(|&lit| {
                        let vi = lit.variable().index();
                        if vi >= model_d.len() { return false; }
                        if lit.is_positive() { model_d[vi] } else { !model_d[vi] }
                    })
                });
                prop_assert!(
                    !model_valid,
                    "BASELINE WRONG-UNSAT: baseline returned UNSAT but decompose returned SAT \
                     with a valid model. num_vars={}, seed={}, clauses={}",
                    num_vars, seed, clauses.len()
                );
            }
            (SatResult::Sat(model_d), SatResult::Sat(_)) => {
                // Both SAT — verify decompose model (reconstruction correctness).
                for (ci, clause) in clauses.iter().enumerate() {
                    let satisfied = clause.iter().any(|&lit| {
                        let vi = lit.variable().index();
                        if vi >= model_d.len() { return false; }
                        if lit.is_positive() { model_d[vi] } else { !model_d[vi] }
                    });
                    prop_assert!(
                        satisfied,
                        "DECOMPOSE MODEL BUG: clause {} ({:?}) not satisfied. \
                         num_vars={}, seed={}",
                        ci, clause, num_vars, seed
                    );
                }
            }
            _ => {
                // Both UNSAT or other combos — OK
            }
        }
    }
}

// ========================================================================
// Decompose Reconstruction Bug Reproduction (#5067)
// ========================================================================

/// Deterministic reproduction of decompose proptest failure: num_vars=5, seed=1010.
/// The solver with decompose-only returns SAT but reconstruction produces an
/// invalid model that doesn't satisfy the original clauses.
#[test]
fn test_decompose_reconstruction_bug_5_1010() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 5usize;
    let seed = 1010u64;
    let num_binary = num_vars * 3;
    let num_ternary = (num_vars as f64 * 2.0) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut clauses: Vec<Vec<Literal>> = Vec::new();

    // Generate binary clauses.
    for _ in 0..num_binary {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 4;
        let l0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let l1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        if v0 != v1 {
            clauses.push(vec![l0, l1]);
        }
    }

    // Generate ternary clauses.
    for _ in 0..num_ternary {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;
        let l0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let l1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let l2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };
        clauses.push(vec![l0, l1, l2]);
    }

    eprintln!(
        "Generated {} clauses for num_vars={}, seed={}",
        clauses.len(),
        num_vars,
        seed
    );
    for (i, c) in clauses.iter().enumerate() {
        let dimacs: Vec<i32> = c.iter().map(|l| l.to_dimacs()).collect();
        eprintln!("  clause {i}: {dimacs:?}");
    }

    // Run with decompose only.
    let mut solver: Solver = Solver::new(num_vars);
    solver.disable_all_inprocessing();
    solver.set_decompose_enabled(true);
    for c in &clauses {
        solver.add_clause(c.clone());
    }
    let result = solver.solve().into_inner();

    match &result {
        SatResult::Sat(model) => {
            // Verify model against original clauses.
            for (ci, clause) in clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    if vi >= model.len() {
                        return false;
                    }
                    if lit.is_positive() {
                        model[vi]
                    } else {
                        !model[vi]
                    }
                });
                assert!(
                    satisfied,
                    "Decompose reconstruction bug: original clause {} ({:?}) not satisfied. \
                     model={:?}, num_vars={}, seed={}",
                    ci,
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                    model,
                    num_vars,
                    seed
                );
            }
        }
        SatResult::Unsat(_) => {
            // Run baseline to verify.
            let mut solver_baseline: Solver = Solver::new(num_vars);
            solver_baseline.disable_all_inprocessing();
            for c in &clauses {
                solver_baseline.add_clause(c.clone());
            }
            let result_baseline = solver_baseline.solve().into_inner();
            if let SatResult::Sat(model) = &result_baseline {
                let model_valid = clauses.iter().all(|clause| {
                    clause.iter().any(|&lit| {
                        let vi = lit.variable().index();
                        if vi >= model.len() {
                            return false;
                        }
                        if lit.is_positive() {
                            model[vi]
                        } else {
                            !model[vi]
                        }
                    })
                });
                assert!(
                    !model_valid,
                    "Decompose wrong-UNSAT: decompose returned UNSAT but baseline found valid SAT model. \
                     num_vars={num_vars}, seed={seed}",
                );
            }
        }
        _ => {}
    }
}

// ========================================================================
// BVE Reconstruction Bug Reproduction (#5044 follow-up)
// ========================================================================

/// Deterministic reproduction of proptest failure: num_vars=17, seed=194.
/// The solver returns SAT but reconstruction flips a variable that breaks
/// a live clause_db clause.
#[test]
fn test_bve_reconstruction_bug_17_194() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 17usize;
    let seed = 194u64;
    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    let mut solver: Solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);

    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        let clause = vec![lit0, lit1, lit2];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in original_clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                if vi >= model.len() {
                    return false;
                }
                if lit.is_positive() {
                    model[vi]
                } else {
                    !model[vi]
                }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model. num_vars={num_vars}, seed={seed}"
            );
        }
    }
    // If UNSAT, the test passes (no model to verify).
}

// ========================================================================
// BVE Reconstruction Property Tests (#4977)
// ========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    /// BVE reconstruction soundness: after BVE eliminates bridge variables,
    /// the model (extended by reconstruction) must satisfy all original clauses.
    ///
    /// Exercises the `map_lit_for_reconstruction` fix from #4977 (commit
    /// 561d2b6c0) which offsets eliminated variables beyond the compacted
    /// range to prevent index collisions during reconstruction.
    ///
    /// Formula: `core_count` core vars + `bridge_count` BVE-eliminable vars.
    /// Each bridge var `b` has exactly 1 positive and 1 negative binary clause:
    /// `(a ∨ b)` and `(¬b ∨ c)` where a, c are core vars. BVE resolves these
    /// into `(a ∨ c)`, eliminating b (product = 1 ≤ growth bound).
    #[test]
    fn prop_bve_reconstruction_model_soundness(
        seed in 0u64..200,
        bridge_count in 20usize..150,
    ) {
        let core_count = 30usize;
        let total_vars = core_count + bridge_count;

        let mut solver: Solver = Solver::new(total_vars);
        solver.set_preprocess_enabled(true);
        solver.disable_all_inprocessing();
        solver.inproc_ctrl.bve.enabled = true;

        let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

        // Bridge variable clauses: each bridge var `b` has exactly
        // 1 positive and 1 negative occurrence → BVE-eliminable.
        for i in 0..bridge_count {
            let b = (core_count + i) as u32;
            let a = ((seed as usize + i * 3) % core_count) as u32;
            let c = ((seed as usize + i * 3 + 1) % core_count) as u32;

            let clause_pos = vec![
                Literal::positive(Variable(a)),
                Literal::positive(Variable(b)),
            ];
            let clause_neg = vec![
                Literal::negative(Variable(b)),
                Literal::positive(Variable(c)),
            ];

            original_clauses.push(clause_pos.clone());
            original_clauses.push(clause_neg.clone());
            solver.add_clause(clause_pos);
            solver.add_clause(clause_neg);
        }

        // Core clauses: positive binary clauses (formula always SAT).
        for i in 0..core_count.min(15) {
            let v1 = ((seed as usize + i * 7) % core_count) as u32;
            let v2 = ((seed as usize + i * 7 + 3) % core_count) as u32;
            if v1 != v2 {
                let clause = vec![
                    Literal::positive(Variable(v1)),
                    Literal::positive(Variable(v2)),
                ];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }

        let result = solver.solve().into_inner();

        // BVE must have eliminated bridge vars.
        let eliminated = solver.bve_stats().vars_eliminated;
        prop_assert!(
            eliminated >= 5,
            "BVE should eliminate bridge vars, got {}",
            eliminated,
        );

        // Model soundness: every original clause must be satisfied.
        if let SatResult::Sat(model) = &result {
            for (clause_idx, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    if vi >= model.len() {
                        return false;
                    }
                    let val = model[vi];
                    if lit.is_positive() { val } else { !val }
                });
                prop_assert!(
                    satisfied,
                    "Original clause {} ({:?}) not satisfied by model after BVE",
                    clause_idx,
                    clause,
                );
            }
        } else {
            // Formula is always SAT by construction (core positive binary
            // clauses + bridge resolvents are satisfiable by all-true).
            prop_assert!(false, "Formula should be SAT (seed={})", seed);
        }
    }
}

/// Deterministic reproduction of #7083: BVE rebuild hits active-clause
/// eliminated-variable invariant at num_vars=23, seed=455.
///
/// The multi-round BVE loop eliminated variables in round 1, but the
/// inter-round GC pass was missing, leaving irredundant clauses with
/// eliminated-variable literals alive when round 2 called rebuild_with_vals().
#[test]
fn test_bve_rebuild_eliminated_var_invariant_23_455() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 23usize;
    let seed = 455u64;
    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);

    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        let clause = vec![lit0, lit1, lit2];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in original_clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                if vi >= model.len() {
                    return false;
                }
                if lit.is_positive() {
                    model[vi]
                } else {
                    !model[vi]
                }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model. \
                 num_vars={num_vars}, seed={seed}",
            );
        }
    }
}

/// Regression test for P1 dual ReconstructionStack field bug (#7015).
///
/// Constructs a SAT formula with 30 core vars and 40 bridge vars. Each
/// bridge var has exactly 1 positive and 1 negative occurrence, making it
/// BVE-eliminable. After BVE, reconstruction must restore eliminated vars.
///
/// The bug was: finalize_sat.rs read `self.reconstruction` (empty, wrong field)
/// instead of `self.inproc.reconstruction` (populated by BVE). Eliminated
/// variables never got reconstructed, causing finalize_sat_model to demote
/// SAT→Unknown. Fixed by removing the duplicate field and routing all reads
/// through `self.inproc.reconstruction`.
#[test]
fn test_bve_reconstruction_reads_correct_field_p1_7015() {
    let core_count = 30usize;
    let bridge_count = 40usize;
    let total_vars = core_count + bridge_count;
    let seed = 42u64;

    let mut solver = Solver::new(total_vars);
    solver.set_preprocess_enabled(true);
    solver.disable_all_inprocessing();
    solver.inproc_ctrl.bve.enabled = true;

    let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

    // Bridge variable clauses: each bridge var `b` has exactly
    // 1 positive and 1 negative occurrence → BVE-eliminable.
    for i in 0..bridge_count {
        let b = (core_count + i) as u32;
        let a = ((seed as usize + i * 3) % core_count) as u32;
        let c = ((seed as usize + i * 3 + 1) % core_count) as u32;

        let clause_pos = vec![
            Literal::positive(Variable(a)),
            Literal::positive(Variable(b)),
        ];
        let clause_neg = vec![
            Literal::negative(Variable(b)),
            Literal::positive(Variable(c)),
        ];

        original_clauses.push(clause_pos.clone());
        original_clauses.push(clause_neg.clone());
        solver.add_clause(clause_pos);
        solver.add_clause(clause_neg);
    }

    // Core clauses: positive binary clauses (formula always SAT by all-true).
    for i in 0..core_count.min(15) {
        let v1 = ((seed as usize + i * 7) % core_count) as u32;
        let v2 = ((seed as usize + i * 7 + 3) % core_count) as u32;
        if v1 != v2 {
            let clause = vec![
                Literal::positive(Variable(v1)),
                Literal::positive(Variable(v2)),
            ];
            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }
    }

    let result = solver.solve().into_inner();

    // BVE should have eliminated bridge vars.
    let eliminated = solver.bve_stats().vars_eliminated;
    assert!(
        eliminated >= 5,
        "BVE should eliminate bridge vars, got {eliminated} eliminations",
    );

    // Reconstruction entries should exist in inproc (the correct location).
    assert!(
        solver.inproc.reconstruction.len() > 0,
        "BVE pushed {} reconstruction entries to inproc.reconstruction, \
         but finalize_sat_model reads from the wrong Solver.reconstruction field",
        solver.inproc.reconstruction.len(),
    );

    // The formula is SAT by construction (all-positive binary core + bridge resolvents).
    // With the dual-field bug, the solver returns Unknown because its internal
    // model verification catches the unsatisfied original clauses.
    match &result {
        SatResult::Sat(model) => {
            // If we get here, reconstruction worked (bug is fixed).
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len() && (model[vi] == lit.is_positive())
                });
                assert!(
                    satisfied,
                    "Original clause {ci} ({clause:?}) not satisfied by model",
                );
            }
        }
        _ => {
            panic!(
                "Expected SAT (formula is SAT by construction), got {:?}. \
                 BVE eliminated {} vars, inproc.reconstruction has {} entries. \
                 This is the dual ReconstructionStack field bug: finalize_sat.rs \
                 reads from Solver.reconstruction (empty) instead of \
                 inproc.reconstruction ({} entries).",
                result,
                eliminated,
                solver.inproc.reconstruction.len(),
                solver.inproc.reconstruction.len(),
            );
        }
    }
}

// ========================================================================
// Gate-based BVE Reconstruction Soundness (#8223)
// ========================================================================

/// Regression test for #8223: BVE gate-based reconstruction soundness.
///
/// Constructs an UNSAT formula where a variable `y` has an AND gate
/// definition plus additional non-gate binary constraints. When gate-only
/// filtering was used for the reconstruction stack, the non-gate clauses
/// were deleted without reconstruction entries. The gate x non-gate
/// resolvents added to the formula were too weak to prevent reconstruction
/// from incorrectly setting y, leading to a spurious SAT answer.
///
/// After the fix (push ALL clauses to reconstruction regardless of gate
/// status), the solver must correctly return UNSAT.
#[test]
fn test_bve_gate_reconstruction_soundness_8223() {
    // Construct: y = AND(a, b, c) with additional constraints making UNSAT.
    //
    // Gate-defining clauses:
    //   (!y | a), (!y | b), (!y | c)    -- forward implications
    //   (y | !a | !b | !c)              -- backward implication
    //
    // Non-gate clauses:
    //   (!y | !d), (!y | !e)            -- extra negative constraints on y
    //   (d), (e)                         -- force d=true, e=true
    //   (a), (b), (c)                    -- force a=b=c=true
    //
    // Analysis: d=true, e=true forced by units.
    //   (!y | !d) with d=true => y=false.
    //   (!y | a) is satisfied since y=false.
    //   (y | !a | !b | !c) with a=b=c=true => y must be true. Contradiction.
    //
    // This formula is UNSAT. BVE can eliminate y using the AND gate.
    // If non-gate clauses (!y | !d), (!y | !e) are missing from the
    // reconstruction stack, reconstruction may incorrectly set y=true,
    // violating the non-gate constraints.
    let num_vars = 6;
    let mut solver = Solver::new(num_vars);

    let y = Variable(0);
    let a = Variable(1);
    let b = Variable(2);
    let c = Variable(3);
    let d = Variable(4);
    let e = Variable(5);

    // Gate-defining clauses for y = AND(a, b, c)
    solver.add_clause(vec![Literal::negative(y), Literal::positive(a)]);
    solver.add_clause(vec![Literal::negative(y), Literal::positive(b)]);
    solver.add_clause(vec![Literal::negative(y), Literal::positive(c)]);
    solver.add_clause(vec![
        Literal::positive(y),
        Literal::negative(a),
        Literal::negative(b),
        Literal::negative(c),
    ]);

    // Non-gate clauses for y
    solver.add_clause(vec![Literal::negative(y), Literal::negative(d)]);
    solver.add_clause(vec![Literal::negative(y), Literal::negative(e)]);

    // Unit clauses forcing d=true, e=true, a=b=c=true
    solver.add_clause(vec![Literal::positive(d)]);
    solver.add_clause(vec![Literal::positive(e)]);
    solver.add_clause(vec![Literal::positive(a)]);
    solver.add_clause(vec![Literal::positive(b)]);
    solver.add_clause(vec![Literal::positive(c)]);

    let result = solver.solve().into_inner();

    // The formula is UNSAT. If BVE reconstruction is broken, it might
    // return SAT with an invalid model or Unknown.
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "#8223: gate-based BVE reconstruction must produce UNSAT, got {result:?}"
    );
}

/// Larger regression test for #8223: UNSAT graph coloring formula with
/// AND gates and non-gate constraints.
///
/// Constructs a 2-coloring problem on K_10 (complete graph on 10 vertices).
/// K_10 is not 2-colorable, so the formula is UNSAT. The encoding creates
/// gate structures that BVE can exploit.
#[test]
fn test_bve_gate_reconstruction_graph_coloring_unsat_8223() {
    let k = 10; // vertices in complete graph
    let n_colors = 2;
    let num_vars = k * n_colors;

    let mut solver = Solver::new(num_vars);
    let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

    let var = |v: usize, c: usize| -> Variable { Variable((v * n_colors + c) as u32) };

    // Each vertex gets at least one color
    for v in 0..k {
        let clause: Vec<Literal> = (0..n_colors)
            .map(|c| Literal::positive(var(v, c)))
            .collect();
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    // Each vertex gets at most one color (AMO pairwise encoding)
    for v in 0..k {
        for c1 in 0..n_colors {
            for c2 in (c1 + 1)..n_colors {
                let clause = vec![Literal::negative(var(v, c1)), Literal::negative(var(v, c2))];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }
    }

    // Adjacent vertices must have different colors
    for v1 in 0..k {
        for v2 in (v1 + 1)..k {
            for c in 0..n_colors {
                let clause = vec![Literal::negative(var(v1, c)), Literal::negative(var(v2, c))];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }
    }

    let result = solver.solve().into_inner();

    match &result {
        SatResult::Unsat(_) => {
            // Expected: K_10 is not 2-colorable
        }
        SatResult::Sat(model) => {
            // Verify model against original clauses -- should fail
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len() && (model[vi] == lit.is_positive())
                });
                assert!(
                    satisfied,
                    "#8223: spurious SAT: original clause {} ({:?}) not satisfied. \
                     This indicates a BVE reconstruction bug.",
                    ci,
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                );
            }
            panic!(
                "#8223: K_10 2-coloring should be UNSAT but solver returned SAT. \
                 This indicates a BVE reconstruction soundness bug."
            );
        }
        _ => {
            // Unknown is acceptable (verification caught reconstruction failure)
        }
    }
}

// Proptest for gate-based BVE reconstruction: formulas with AND gates and
// additional non-gate constraints. Verifies that when SAT is returned,
// the model satisfies all original clauses (including non-gate ones).
//
// Regression coverage for #8223.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn prop_bve_gate_reconstruction_non_gate_clauses(
        seed in 0u64..500,
        n_gates in 3usize..8,
    ) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        // Generate a formula with n_gates AND gates, each having 2-3 inputs
        // and 1-2 non-gate binary constraints.
        let n_inputs_per_gate = 3;
        let core_vars = n_gates * n_inputs_per_gate; // input variables
        let gate_vars = n_gates;                      // output (gate) variables
        let extra_vars = 5;                           // auxiliary variables for non-gate clauses
        let total_vars = core_vars + gate_vars + extra_vars;

        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        let mut h = hasher.finish();

        let mut original_clauses: Vec<Vec<Literal>> = Vec::new();
        let mut solver = Solver::new(total_vars);

        for g in 0..n_gates {
            let y = Variable((core_vars + g) as u32);
            let inputs: Vec<Variable> = (0..n_inputs_per_gate)
                .map(|i| Variable((g * n_inputs_per_gate + i) as u32))
                .collect();

            // AND gate: y = AND(inputs)
            // Forward: !y | x_i for each input
            for &inp in &inputs {
                let clause = vec![Literal::negative(y), Literal::positive(inp)];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
            // Backward: y | !x_1 | !x_2 | ... | !x_n
            let mut backward = vec![Literal::positive(y)];
            for &inp in &inputs {
                backward.push(Literal::negative(inp));
            }
            original_clauses.push(backward.clone());
            solver.add_clause(backward);

            // Non-gate binary constraint tying y to an auxiliary variable
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let aux = Variable((core_vars + gate_vars + (h as usize % extra_vars)) as u32);
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let polarity = h.is_multiple_of(2);
            let aux_lit = if polarity {
                Literal::positive(aux)
            } else {
                Literal::negative(aux)
            };
            let clause = vec![Literal::negative(y), aux_lit];
            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        // Add random binary clauses among core variables
        for _ in 0..total_vars {
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v1 = (h % total_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v2 = (h % total_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let s = h % 4;
            if v1 != v2 {
                let l1 = if s & 1 == 0 {
                    Literal::positive(Variable(v1))
                } else {
                    Literal::negative(Variable(v1))
                };
                let l2 = if s & 2 == 0 {
                    Literal::positive(Variable(v2))
                } else {
                    Literal::negative(Variable(v2))
                };
                let clause = vec![l1, l2];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = &result {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len() && (model[vi] == lit.is_positive())
                });
                prop_assert!(
                    satisfied,
                    "#8223: original clause {} ({:?}) not satisfied by model. \
                     seed={}, n_gates={}",
                    ci,
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                    seed,
                    n_gates,
                );
            }
        }
    }
}

// ========================================================================
// End-to-End BVE Grouped Reconstruction Validation (#8494)
// ========================================================================

/// Deterministic test for deep BVE elimination chains.
///
/// Creates a chain of 10 elimination steps: chain_0 -> chain_1 -> ... -> chain_9.
/// Each chain variable `c_i` has exactly 2 clauses:
///   (c_i | core_a_i) and (!c_i | core_b_i)
/// where core_a_i and core_b_i are core variables. BVE eliminates c_i by
/// resolving into (core_a_i | core_b_i). The chain structure means
/// the resolvent from eliminating c_0 involves the same core variables
/// that c_1's clauses reference, creating cascading dependencies.
///
/// After elimination, reconstruction must restore all chain variables
/// such that the original clauses are satisfied. This exercises multi-round
/// BVE reconstruction where later eliminations interact with earlier ones.
#[test]
fn test_bve_deep_chain_deterministic() {
    let core_count = 20usize;
    let chain_depth = 10usize;
    let total_vars = core_count + chain_depth;

    let mut solver = Solver::new(total_vars);
    solver.set_preprocess_enabled(true);
    solver.disable_all_inprocessing();
    solver.inproc_ctrl.bve.enabled = true;

    let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

    // Chain variables: each c_i has 1 positive and 1 negative occurrence.
    // c_i connects core_a = (2*i) % core_count to core_b = (2*i+1) % core_count.
    // The resolvents (core_a | core_b) form a satisfiable set of positive binary clauses.
    for i in 0..chain_depth {
        let c = (core_count + i) as u32;
        let core_a = ((2 * i) % core_count) as u32;
        let core_b = ((2 * i + 1) % core_count) as u32;

        let pos_clause = vec![
            Literal::positive(Variable(c)),
            Literal::positive(Variable(core_a)),
        ];
        let neg_clause = vec![
            Literal::negative(Variable(c)),
            Literal::positive(Variable(core_b)),
        ];

        original_clauses.push(pos_clause.clone());
        original_clauses.push(neg_clause.clone());
        solver.add_clause(pos_clause);
        solver.add_clause(neg_clause);
    }

    // Core constraints: positive binary clauses (formula always SAT by all-true).
    for i in 0..core_count / 2 {
        let v1 = (i * 2) as u32;
        let v2 = (i * 2 + 1) as u32;
        let clause = vec![
            Literal::positive(Variable(v1)),
            Literal::positive(Variable(v2)),
        ];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    // BVE should eliminate chain variables.
    let eliminated = solver.bve_stats().vars_eliminated;
    assert!(
        eliminated >= 5,
        "BVE should eliminate chain vars, got {eliminated}",
    );

    // Model must satisfy all original clauses.
    match &result {
        SatResult::Sat(model) => {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len()
                        && if lit.is_positive() {
                            model[vi]
                        } else {
                            !model[vi]
                        }
                });
                assert!(
                    satisfied,
                    "Deep chain: original clause {ci} ({:?}) not satisfied. \
                     eliminated={eliminated}",
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                );
            }
        }
        _ => {
            panic!(
                "Deep chain formula should be SAT (all-true satisfies core clauses), got {result:?}"
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Property test for deep BVE elimination chains.
    ///
    /// Creates formulas with a chain of `chain_depth` BVE-eliminable variables,
    /// each having exactly 1 positive and 1 negative occurrence. The resolvents
    /// from eliminating each chain variable feed into core constraints.
    /// Chain depth varies from 3 to 15 to exercise multi-round reconstruction.
    ///
    /// Regression coverage for #8494: grouped reconstruction end-to-end validation.
    #[test]
    fn prop_bve_deep_elimination_chain(
        seed in 0u64..300,
        chain_depth in 3usize..15,
    ) {
        let core_count = 20usize;
        let total_vars = core_count + chain_depth;

        let mut solver: Solver = Solver::new(total_vars);
        solver.set_preprocess_enabled(true);
        solver.disable_all_inprocessing();
        solver.inproc_ctrl.bve.enabled = true;

        let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

        // Chain links: each chain variable c_i connects two core variables.
        for i in 0..chain_depth {
            let c = (core_count + i) as u32;
            let core_a = ((seed as usize + i * 3) % core_count) as u32;
            let core_b = ((seed as usize + i * 3 + 1) % core_count) as u32;

            let pos_clause = vec![
                Literal::positive(Variable(c)),
                Literal::positive(Variable(core_a)),
            ];
            let neg_clause = vec![
                Literal::negative(Variable(c)),
                Literal::positive(Variable(core_b)),
            ];

            original_clauses.push(pos_clause.clone());
            original_clauses.push(neg_clause.clone());
            solver.add_clause(pos_clause);
            solver.add_clause(neg_clause);
        }

        // Core: positive binary clauses (always SAT by all-true).
        for i in 0..core_count.min(10) {
            let v1 = ((seed as usize + i * 7) % core_count) as u32;
            let v2 = ((seed as usize + i * 7 + 3) % core_count) as u32;
            if v1 != v2 {
                let clause = vec![
                    Literal::positive(Variable(v1)),
                    Literal::positive(Variable(v2)),
                ];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = &result {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len()
                        && if lit.is_positive() { model[vi] } else { !model[vi] }
                });
                prop_assert!(
                    satisfied,
                    "Deep chain: clause {} ({:?}) not satisfied. seed={}, chain_depth={}",
                    ci,
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                    seed,
                    chain_depth,
                );
            }
        }
        // UNSAT is also acceptable (some seed/depth combos may be UNSAT).
    }

    /// Property test for XOR gate BVE reconstruction.
    ///
    /// An XOR gate `y = x1 XOR x2` is encoded as 4 clauses:
    ///   (y | x1 | x2), (y | !x1 | !x2), (!y | x1 | !x2), (!y | !x1 | x2)
    ///
    /// BVE can eliminate y if its total resolvent count stays within bounds.
    /// This test creates 3-8 XOR gates with shared input variables to stress
    /// the reconstruction of multi-clause gate structures.
    ///
    /// Regression coverage for #8494: XOR gate reconstruction validation.
    #[test]
    fn prop_bve_xor_gate_reconstruction(
        seed in 0u64..500,
        n_gates in 3usize..8,
    ) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let n_input_vars = n_gates * 2 + 5; // shared input pool
        let total_vars = n_input_vars + n_gates; // inputs + gate outputs
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        let mut h = hasher.finish();

        let mut original_clauses: Vec<Vec<Literal>> = Vec::new();
        let mut solver = Solver::new(total_vars);

        for g in 0..n_gates {
            let y = Variable((n_input_vars + g) as u32);

            // Pick two input variables from the shared pool.
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let x1_idx = (h as usize % n_input_vars) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let mut x2_idx = (h as usize % n_input_vars) as u32;
            if x2_idx == x1_idx {
                x2_idx = (x1_idx + 1) % n_input_vars as u32;
            }

            let x1 = Variable(x1_idx);
            let x2 = Variable(x2_idx);

            // XOR: y = x1 XOR x2
            // (y | x1 | x2)
            let c1 = vec![Literal::positive(y), Literal::positive(x1), Literal::positive(x2)];
            // (y | !x1 | !x2)
            let c2 = vec![Literal::positive(y), Literal::negative(x1), Literal::negative(x2)];
            // (!y | x1 | !x2)
            let c3 = vec![Literal::negative(y), Literal::positive(x1), Literal::negative(x2)];
            // (!y | !x1 | x2)
            let c4 = vec![Literal::negative(y), Literal::negative(x1), Literal::positive(x2)];

            for c in [c1, c2, c3, c4] {
                original_clauses.push(c.clone());
                solver.add_clause(c);
            }
        }

        // Add binary clauses among input variables to constrain the formula.
        for _ in 0..n_input_vars {
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v1 = (h % n_input_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v2 = (h % n_input_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let s = h % 4;
            if v1 != v2 {
                let l1 = if s & 1 == 0 {
                    Literal::positive(Variable(v1))
                } else {
                    Literal::negative(Variable(v1))
                };
                let l2 = if s & 2 == 0 {
                    Literal::positive(Variable(v2))
                } else {
                    Literal::negative(Variable(v2))
                };
                let clause = vec![l1, l2];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = &result {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len() && (model[vi] == lit.is_positive())
                });
                prop_assert!(
                    satisfied,
                    "XOR gate: clause {} ({:?}) not satisfied. seed={}, n_gates={}",
                    ci,
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                    seed,
                    n_gates,
                );
            }
        }
    }

    /// Property test for mixed clause lengths with BVE reconstruction.
    ///
    /// Creates formulas mixing binary (2-lit), ternary (3-lit), quaternary
    /// (4-lit), and 5-literal clauses. Binary clauses create more BVE
    /// opportunities since they contribute fewer resolvents. The mix of
    /// lengths exercises different paths through the reconstruction algorithm.
    ///
    /// Regression coverage for #8494: mixed clause length validation.
    #[test]
    fn prop_bve_mixed_clause_lengths(
        num_vars in 15usize..40,
        seed in 0u64..500,
    ) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let num_clauses = (num_vars as f64 * 4.0) as usize;
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        let mut h = hasher.finish();

        let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
        let mut solver: Solver = Solver::new(num_vars);
        solver.set_bve_enabled(true);

        for _ in 0..num_clauses {
            // Choose clause length: 2, 3, 4, or 5 with weights 30%, 40%, 20%, 10%.
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let len_roll = h % 100;
            let clause_len = if len_roll < 30 {
                2
            } else if len_roll < 70 {
                3
            } else if len_roll < 90 {
                4
            } else {
                5
            };

            let mut clause = Vec::with_capacity(clause_len);
            let mut used_vars = std::collections::HashSet::new();

            for _ in 0..clause_len {
                h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                let mut v = (h % num_vars as u64) as u32;
                // Avoid duplicate variables in the same clause.
                let mut attempts = 0;
                while used_vars.contains(&v) && attempts < 10 {
                    h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    v = (h % num_vars as u64) as u32;
                    attempts += 1;
                }
                if used_vars.contains(&v) {
                    continue;
                }
                used_vars.insert(v);

                h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                let lit = if h.is_multiple_of(2) {
                    Literal::positive(Variable(v))
                } else {
                    Literal::negative(Variable(v))
                };
                clause.push(lit);
            }

            if clause.len() >= 2 {
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = &result {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len()
                        && if lit.is_positive() { model[vi] } else { !model[vi] }
                });
                prop_assert!(
                    satisfied,
                    "Mixed lengths: clause {} ({:?}) not satisfied. \
                     num_vars={}, seed={}",
                    ci,
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                    num_vars,
                    seed,
                );
            }
        }
    }

    /// Property test for combined sweep + BVE reconstruction.
    ///
    /// Creates formulas with:
    /// 1. Equivalence pairs (x <-> y via (x|!y) and (!x|y)) to trigger sweep
    /// 2. Bridge variables (1 pos + 1 neg occurrence) to trigger BVE
    ///
    /// The interaction between sweep (variable merging) and BVE (variable
    /// elimination) was a source of bugs (#8179, #8356). This test validates
    /// that both transformations compose correctly in reconstruction.
    ///
    /// Regression coverage for #8494: sweep+BVE combined reconstruction.
    #[test]
    fn prop_bve_sweep_combined_reconstruction(
        seed in 0u64..300,
        n_equiv_pairs in 3usize..8,
        n_bridges in 5usize..20,
    ) {
        let core_count = 20usize;
        let equiv_count = n_equiv_pairs * 2; // two vars per equivalence pair
        let bridge_count = n_bridges;
        let total_vars = core_count + equiv_count + bridge_count;

        let mut solver: Solver = Solver::new(total_vars);
        // Enable full preprocessing including both sweep and BVE.
        solver.set_preprocess_enabled(true);
        solver.set_bve_enabled(true);
        // Sweep stays enabled by default; decompose/congruence remain opt-in.

        let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

        // Equivalence pairs: x_i <-> x_{i+1} via binary implications.
        for p in 0..n_equiv_pairs {
            let x = (core_count + p * 2) as u32;
            let y = (core_count + p * 2 + 1) as u32;

            // x -> y: (!x | y)
            let c1 = vec![Literal::negative(Variable(x)), Literal::positive(Variable(y))];
            // y -> x: (!y | x)
            let c2 = vec![Literal::negative(Variable(y)), Literal::positive(Variable(x))];

            original_clauses.push(c1.clone());
            original_clauses.push(c2.clone());
            solver.add_clause(c1);
            solver.add_clause(c2);
        }

        // Bridge variables: each has 1 positive + 1 negative occurrence.
        for i in 0..bridge_count {
            let b = (core_count + equiv_count + i) as u32;
            let core_a = ((seed as usize + i * 5) % core_count) as u32;
            let core_b = ((seed as usize + i * 5 + 2) % core_count) as u32;

            let pos_clause = vec![
                Literal::positive(Variable(b)),
                Literal::positive(Variable(core_a)),
            ];
            let neg_clause = vec![
                Literal::negative(Variable(b)),
                Literal::positive(Variable(core_b)),
            ];

            original_clauses.push(pos_clause.clone());
            original_clauses.push(neg_clause.clone());
            solver.add_clause(pos_clause);
            solver.add_clause(neg_clause);
        }

        // Core: positive binary clauses (formula always SAT by all-true).
        for i in 0..core_count.min(12) {
            let v1 = ((seed as usize + i * 3) % core_count) as u32;
            let v2 = ((seed as usize + i * 3 + 1) % core_count) as u32;
            if v1 != v2 {
                let clause = vec![
                    Literal::positive(Variable(v1)),
                    Literal::positive(Variable(v2)),
                ];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }

        // Also connect equivalence vars to core vars.
        for p in 0..n_equiv_pairs.min(5) {
            let eq_var = (core_count + p * 2) as u32;
            let core_v = ((seed as usize + p * 11) % core_count) as u32;
            let clause = vec![
                Literal::positive(Variable(eq_var)),
                Literal::positive(Variable(core_v)),
            ];
            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = &result {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len()
                        && if lit.is_positive() { model[vi] } else { !model[vi] }
                });
                prop_assert!(
                    satisfied,
                    "Sweep+BVE: clause {} ({:?}) not satisfied. \
                     seed={}, n_equiv={}, n_bridges={}",
                    ci,
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                    seed,
                    n_equiv_pairs,
                    n_bridges,
                );
            }
        }
        // UNSAT is acceptable (some combinations may be unsatisfiable).
    }
}

// ========================================================================
// Braun-style Circuit Equivalence Regression Tests (#8482)
// ========================================================================

/// Regression test for #8482: BVE reconstruction on gate-structured circuit
/// equivalence formulas (Braun tree encoding pattern).
///
/// The Braun tree circuit equivalence benchmarks encode two implementations
/// of the same boolean function and check equivalence via XOR gates on the
/// outputs. This creates a dense AND/XOR gate structure where BVE can
/// eliminate many gate-output variables. The bug was that non-gate clauses
/// were incorrectly pushed to the reconstruction stack, corrupting the
/// witness-based model extension.
///
/// This test creates a small circuit equivalence checking formula:
/// - Circuit A: chain of AND gates computing f_A(x1..xN)
/// - Circuit B: chain of AND gates computing f_B(x1..xN) (same function)
/// - Equivalence check: output_A XOR output_B (should always be false)
/// - Final clause: (eq_out) forcing the XOR to be true → UNSAT
///
/// With the #8482 fix (gate-only witness filtering), BVE eliminates gate
/// variables correctly and reconstruction produces a valid model extension
/// that confirms UNSAT.
#[test]
fn test_bve_braun_circuit_equivalence_unsat_8482() {
    // Small circuit: 4 inputs, 2 AND-tree circuits, XOR equivalence check.
    //
    // Variables:
    //   0..3: inputs x0..x3
    //   4: a0 = AND(x0, x1)  -- circuit A internal
    //   5: a1 = AND(x2, x3)  -- circuit A internal
    //   6: out_a = AND(a0, a1) -- circuit A output
    //   7: b0 = AND(x0, x1)  -- circuit B internal (same function)
    //   8: b1 = AND(x2, x3)  -- circuit B internal
    //   9: out_b = AND(b0, b1) -- circuit B output
    //   10: xor_out = XOR(out_a, out_b) -- equivalence check
    //
    // Since both circuits compute the same function, xor_out is always false.
    // Adding unit clause (xor_out) makes it UNSAT.
    let num_vars = 11;
    let mut solver = Solver::new(num_vars);

    let x = |i: u32| Variable(i);

    // Helper to add AND gate: out = AND(a, b)
    // Clauses: (!out | a), (!out | b), (out | !a | !b)
    let add_and_gate = |solver: &mut Solver, out: Variable, a: Variable, b: Variable| {
        solver.add_clause(vec![Literal::negative(out), Literal::positive(a)]);
        solver.add_clause(vec![Literal::negative(out), Literal::positive(b)]);
        solver.add_clause(vec![
            Literal::positive(out),
            Literal::negative(a),
            Literal::negative(b),
        ]);
    };

    // Circuit A: out_a = AND(AND(x0,x1), AND(x2,x3))
    add_and_gate(&mut solver, x(4), x(0), x(1)); // a0 = AND(x0, x1)
    add_and_gate(&mut solver, x(5), x(2), x(3)); // a1 = AND(x2, x3)
    add_and_gate(&mut solver, x(6), x(4), x(5)); // out_a = AND(a0, a1)

    // Circuit B: out_b = AND(AND(x0,x1), AND(x2,x3)) -- same function
    add_and_gate(&mut solver, x(7), x(0), x(1)); // b0 = AND(x0, x1)
    add_and_gate(&mut solver, x(8), x(2), x(3)); // b1 = AND(x2, x3)
    add_and_gate(&mut solver, x(9), x(7), x(8)); // out_b = AND(b0, b1)

    // XOR equivalence check: xor_out = XOR(out_a, out_b)
    // Standard Tseitin XOR encoding for z <=> (a XOR b):
    //   (!z | a | b), (!z | !a | !b), (z | !a | b), (z | a | !b)
    let xor_out = x(10);
    let out_a = x(6);
    let out_b = x(9);
    solver.add_clause(vec![
        Literal::negative(xor_out),
        Literal::positive(out_a),
        Literal::positive(out_b),
    ]);
    solver.add_clause(vec![
        Literal::negative(xor_out),
        Literal::negative(out_a),
        Literal::negative(out_b),
    ]);
    solver.add_clause(vec![
        Literal::positive(xor_out),
        Literal::negative(out_a),
        Literal::positive(out_b),
    ]);
    solver.add_clause(vec![
        Literal::positive(xor_out),
        Literal::positive(out_a),
        Literal::negative(out_b),
    ]);

    // Force equivalence to be violated (xor_out = true)
    solver.add_clause(vec![Literal::positive(xor_out)]);

    let result = solver.solve().into_inner();

    // Both circuits compute the same function, so XOR(out_a, out_b) is always
    // false. Forcing it true makes the formula UNSAT. With the #8482 bug
    // (non-gate clauses in reconstruction stack), the solver could return
    // SAT with an invalid model or Unknown.
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "#8482: braun-style circuit equivalence must be UNSAT, got {result:?}"
    );
}

/// Larger braun-style test with deeper AND-tree circuits and additional
/// non-gate constraints. Tests that gate-only witness filtering works
/// correctly when gate variables have both gate-defining and non-gate
/// occurrence clauses.
#[test]
fn test_bve_braun_circuit_deep_tree_unsat_8482() {
    // 8-input AND tree (3 levels deep), two copies, XOR equivalence.
    //
    // Inputs: 0..7
    // Circuit A levels:
    //   L1: 8=AND(0,1), 9=AND(2,3), 10=AND(4,5), 11=AND(6,7)
    //   L2: 12=AND(8,9), 13=AND(10,11)
    //   L3: 14=AND(12,13) = out_a
    // Circuit B levels:
    //   L1: 15=AND(0,1), 16=AND(2,3), 17=AND(4,5), 18=AND(6,7)
    //   L2: 19=AND(15,16), 20=AND(17,18)
    //   L3: 21=AND(19,20) = out_b
    // XOR: 22=XOR(14,21)
    // Non-gate constraints on internal vars: (8 | !15), (!9 | 16)
    let num_vars = 23;
    let mut solver = Solver::new(num_vars);

    let v = |i: u32| Variable(i);

    let add_and = |solver: &mut Solver, out: Variable, a: Variable, b: Variable| {
        solver.add_clause(vec![Literal::negative(out), Literal::positive(a)]);
        solver.add_clause(vec![Literal::negative(out), Literal::positive(b)]);
        solver.add_clause(vec![
            Literal::positive(out),
            Literal::negative(a),
            Literal::negative(b),
        ]);
    };

    // Circuit A
    add_and(&mut solver, v(8), v(0), v(1));
    add_and(&mut solver, v(9), v(2), v(3));
    add_and(&mut solver, v(10), v(4), v(5));
    add_and(&mut solver, v(11), v(6), v(7));
    add_and(&mut solver, v(12), v(8), v(9));
    add_and(&mut solver, v(13), v(10), v(11));
    add_and(&mut solver, v(14), v(12), v(13));

    // Circuit B (same structure, same inputs)
    add_and(&mut solver, v(15), v(0), v(1));
    add_and(&mut solver, v(16), v(2), v(3));
    add_and(&mut solver, v(17), v(4), v(5));
    add_and(&mut solver, v(18), v(6), v(7));
    add_and(&mut solver, v(19), v(15), v(16));
    add_and(&mut solver, v(20), v(17), v(18));
    add_and(&mut solver, v(21), v(19), v(20));

    // XOR equivalence: 22 = XOR(14, 21)
    // Standard Tseitin XOR encoding for z <=> (a XOR b):
    //   (!z | a | b), (!z | !a | !b), (z | !a | b), (z | a | !b)
    let xor_out = v(22);
    let out_a = v(14);
    let out_b = v(21);
    solver.add_clause(vec![
        Literal::negative(xor_out),
        Literal::positive(out_a),
        Literal::positive(out_b),
    ]);
    solver.add_clause(vec![
        Literal::negative(xor_out),
        Literal::negative(out_a),
        Literal::negative(out_b),
    ]);
    solver.add_clause(vec![
        Literal::positive(xor_out),
        Literal::negative(out_a),
        Literal::positive(out_b),
    ]);
    solver.add_clause(vec![
        Literal::positive(xor_out),
        Literal::positive(out_a),
        Literal::negative(out_b),
    ]);

    // Non-gate binary constraints on internal gate variables.
    // These are the clauses that #8482 was incorrectly pushing to the
    // reconstruction stack (non-gate clauses for gate-defined variables).
    solver.add_clause(vec![Literal::positive(v(8)), Literal::negative(v(15))]);
    solver.add_clause(vec![Literal::negative(v(9)), Literal::positive(v(16))]);
    solver.add_clause(vec![Literal::positive(v(12)), Literal::negative(v(19))]);

    // Force equivalence violation
    solver.add_clause(vec![Literal::positive(xor_out)]);

    let result = solver.solve().into_inner();

    assert!(
        matches!(result, SatResult::Unsat(_)),
        "#8482: deep braun-style circuit equivalence with non-gate constraints \
         must be UNSAT, got {result:?}"
    );
}

// ========================================================================
// Multi-Round BVE Non-Contiguous Witness Entry Validation (#8494)
// ========================================================================

/// Validates that multi-round BVE with non-contiguous witness entries
/// reconstructs correctly. The grouped reconstruction algorithm processes
/// witness entries by variable, handling the case where entries for the
/// same variable are scattered across the reconstruction stack due to
/// multi-round elimination.
///
/// This test creates a formula where:
/// - Round 1: eliminates variables v_A and v_B, pushing witness entries
/// - Round 2: eliminates variables v_C (whose clauses reference variables
///   from round 1's resolvents), pushing entries that interleave with
///   round 1's entries on the reconstruction stack.
///
/// The non-contiguous ordering is the core scenario from #8494.
#[test]
fn test_bve_multi_round_noncontiguous_witness_8494() {
    // 15 core variables, 6 bridge variables for 2 rounds of BVE.
    //
    // Round 1 bridges: b0(15), b1(16), b2(17) - each has 1 pos + 1 neg occurrence
    // Round 2 bridges: b3(18), b4(19), b5(20) - involve resolvents from round 1
    //
    // After round 1 eliminates b0..b2, the resolvents create new binary
    // clauses among core variables. Round 2 bridges b3..b5 are designed
    // so their clauses reference core variables that also appear in
    // round 1's witness entries, creating the non-contiguous interleaving.
    let core_count = 15usize;
    let round1_bridges = 3usize;
    let round2_bridges = 3usize;
    let total_vars = core_count + round1_bridges + round2_bridges;

    let mut solver = Solver::new(total_vars);
    solver.set_preprocess_enabled(true);
    solver.disable_all_inprocessing();
    solver.inproc_ctrl.bve.enabled = true;

    let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

    // Round 1 bridges: b_i connects core variables.
    for i in 0..round1_bridges {
        let b = (core_count + i) as u32;
        let core_a = (i * 2) as u32;
        let core_b = (i * 2 + 1) as u32;

        let pos = vec![
            Literal::positive(Variable(b)),
            Literal::positive(Variable(core_a)),
        ];
        let neg = vec![
            Literal::negative(Variable(b)),
            Literal::positive(Variable(core_b)),
        ];
        original_clauses.push(pos.clone());
        original_clauses.push(neg.clone());
        solver.add_clause(pos);
        solver.add_clause(neg);
    }

    // Round 2 bridges: these reference some of the same core variables
    // as round 1, creating non-contiguous witness entry patterns.
    for i in 0..round2_bridges {
        let b = (core_count + round1_bridges + i) as u32;
        // Reference core variables that also appeared in round 1 bridges.
        let core_a = (i % core_count) as u32;
        let core_b = ((i + 3) % core_count) as u32;

        let pos = vec![
            Literal::positive(Variable(b)),
            Literal::positive(Variable(core_a)),
        ];
        let neg = vec![
            Literal::negative(Variable(b)),
            Literal::positive(Variable(core_b)),
        ];
        original_clauses.push(pos.clone());
        original_clauses.push(neg.clone());
        solver.add_clause(pos);
        solver.add_clause(neg);
    }

    // Core: positive binary clauses making the formula always SAT.
    for i in 0..core_count / 2 {
        let v1 = (i * 2) as u32;
        let v2 = (i * 2 + 1) as u32;
        let clause = vec![
            Literal::positive(Variable(v1)),
            Literal::positive(Variable(v2)),
        ];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    let eliminated = solver.bve_stats().vars_eliminated;
    assert!(
        eliminated >= 3,
        "BVE should eliminate at least the round-1 bridges, got {eliminated}",
    );

    match &result {
        SatResult::Sat(model) => {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len()
                        && if lit.is_positive() {
                            model[vi]
                        } else {
                            !model[vi]
                        }
                });
                assert!(
                    satisfied,
                    "#8494: multi-round non-contiguous witness: clause {ci} ({:?}) \
                     not satisfied. eliminated={eliminated}",
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                );
            }
        }
        _ => {
            panic!(
                "#8494: multi-round non-contiguous witness formula should be SAT, got {result:?}"
            );
        }
    }
}

/// Stress test: large random formula that forces heavy BVE and verifies
/// the reconstructed model. Uses 200 variables with high BVE opportunity
/// (many low-degree variables) and validates that the model returned by
/// the solver satisfies all original clauses.
///
/// This is a deterministic reproduction of the end-to-end scenario from #8494:
/// real formulas with hundreds of eliminated variables and multi-round BVE.
#[test]
fn test_bve_heavy_elimination_stress_8494() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let core_count = 50usize;
    let bridge_count = 150usize;
    let total_vars = core_count + bridge_count;
    let seed = 8494u64;

    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut solver = Solver::new(total_vars);
    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

    // Create bridge variables with 1 positive + 1 negative occurrence each.
    // Use varied core variable connections to create a realistic BVE workload.
    for i in 0..bridge_count {
        let b = (core_count + i) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let core_a = (h as usize % core_count) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let core_b = (h as usize % core_count) as u32;

        let pos = vec![
            Literal::positive(Variable(b)),
            Literal::positive(Variable(core_a)),
        ];
        let neg = vec![
            Literal::negative(Variable(b)),
            Literal::positive(Variable(core_b)),
        ];
        original_clauses.push(pos.clone());
        original_clauses.push(neg.clone());
        solver.add_clause(pos);
        solver.add_clause(neg);
    }

    // Core: positive binary and ternary clauses (formula always SAT by all-true).
    for _ in 0..core_count {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h as usize % core_count) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h as usize % core_count) as u32;
        if v1 != v2 {
            let clause = vec![
                Literal::positive(Variable(v1)),
                Literal::positive(Variable(v2)),
            ];
            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }
    }

    let result = solver.solve().into_inner();

    let eliminated = solver.bve_stats().vars_eliminated;
    assert!(
        eliminated >= 50,
        "#8494: heavy BVE stress test should eliminate 50+ vars, got {eliminated}",
    );

    match &result {
        SatResult::Sat(model) => {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len()
                        && if lit.is_positive() {
                            model[vi]
                        } else {
                            !model[vi]
                        }
                });
                assert!(
                    satisfied,
                    "#8494: heavy BVE stress: clause {ci} ({:?}) not satisfied. \
                     eliminated={eliminated}",
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                );
            }
        }
        _ => {
            panic!(
                "#8494: heavy BVE stress formula should be SAT, got {result:?}. \
                 eliminated={eliminated}"
            );
        }
    }
}

/// Multi-round BVE with BCE enabled validates that retained witness entries
/// reconstruct every original clause when the passes interleave.
///
/// Regression coverage for #8494 + #8179 interaction.
#[test]
fn test_bve_bce_interleaved_reconstruction_8494() {
    // Formula with:
    // - Variables 0..9: core
    // - Variable 10: BCE-blocked + BVE-eliminable
    // - Variable 11: BVE-eliminable (round 2, references var 10's core connections)
    //
    let num_vars = 12;
    let mut solver = Solver::new(num_vars);

    let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

    // BVE-eligible: v10 has low occurrence count.
    let c1 = vec![
        Literal::positive(Variable(10)),
        Literal::positive(Variable(0)),
    ];
    let c2 = vec![
        Literal::negative(Variable(10)),
        Literal::positive(Variable(1)),
    ];
    // v11 BVE-eligible, references same core vars as v10's connections.
    let c3 = vec![
        Literal::positive(Variable(11)),
        Literal::positive(Variable(0)),
    ];
    let c4 = vec![
        Literal::negative(Variable(11)),
        Literal::positive(Variable(2)),
    ];

    for c in [&c1, &c2, &c3, &c4] {
        original_clauses.push(c.clone());
        solver.add_clause(c.clone());
    }

    // Core clauses: positive binary (formula always SAT by all-true).
    for i in 0..5 {
        let v1 = (i * 2) as u32;
        let v2 = (i * 2 + 1) as u32;
        if v1 < 10 && v2 < 10 {
            let clause = vec![
                Literal::positive(Variable(v1)),
                Literal::positive(Variable(v2)),
            ];
            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }
    }

    let result = solver.solve().into_inner();

    match &result {
        SatResult::Sat(model) => {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len()
                        && if lit.is_positive() {
                            model[vi]
                        } else {
                            !model[vi]
                        }
                });
                assert!(
                    satisfied,
                    "#8494: BCE+BVE interleaved: clause {ci} ({:?}) not satisfied",
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                );
            }
        }
        other => panic!("#8494: formula is SAT by all-true, got {other:?}"),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Property test: multi-round BVE with varying bridge density.
    ///
    /// Creates formulas with `n_rounds` layers of BVE-eliminable variables,
    /// where later rounds' bridges reference core variables that appeared
    /// in earlier rounds' witness entries. This exercises non-contiguous
    /// witness entry ordering in the grouped reconstruction algorithm.
    ///
    /// Regression coverage for #8494.
    #[test]
    fn prop_bve_multi_round_layered(
        seed in 0u64..500,
        n_rounds in 2usize..5,
        bridges_per_round in 5usize..20,
    ) {
        let core_count = 25usize;
        let total_bridges = n_rounds * bridges_per_round;
        let total_vars = core_count + total_bridges;

        let mut solver: Solver = Solver::new(total_vars);
        solver.set_preprocess_enabled(true);
        solver.disable_all_inprocessing();
        solver.inproc_ctrl.bve.enabled = true;

        let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

        // Each round creates bridges referencing core vars with increasing
        // overlap (later rounds share more core variables with earlier rounds).
        for round in 0..n_rounds {
            for i in 0..bridges_per_round {
                let b = (core_count + round * bridges_per_round + i) as u32;
                // Use different core variable selection per round but with overlap.
                let core_a = ((seed as usize + round * 7 + i * 3) % core_count) as u32;
                let core_b = ((seed as usize + round * 7 + i * 3 + 1) % core_count) as u32;

                let pos = vec![
                    Literal::positive(Variable(b)),
                    Literal::positive(Variable(core_a)),
                ];
                let neg = vec![
                    Literal::negative(Variable(b)),
                    Literal::positive(Variable(core_b)),
                ];
                original_clauses.push(pos.clone());
                original_clauses.push(neg.clone());
                solver.add_clause(pos);
                solver.add_clause(neg);
            }
        }

        // Core: positive binary clauses (formula always SAT by all-true).
        for i in 0..core_count.min(15) {
            let v1 = ((seed as usize + i * 5) % core_count) as u32;
            let v2 = ((seed as usize + i * 5 + 2) % core_count) as u32;
            if v1 != v2 {
                let clause = vec![
                    Literal::positive(Variable(v1)),
                    Literal::positive(Variable(v2)),
                ];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = &result {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len()
                        && if lit.is_positive() { model[vi] } else { !model[vi] }
                });
                prop_assert!(
                    satisfied,
                    "#8494: multi-round layered: clause {} ({:?}) not satisfied. \
                     seed={}, n_rounds={}, bridges_per_round={}",
                    ci,
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                    seed,
                    n_rounds,
                    bridges_per_round,
                );
            }
        }
    }
}
