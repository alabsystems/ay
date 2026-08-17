// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `solver::tests::search` to preserve test FQNs.

// ========================================================================
// Basic solver tests (extracted from tests.rs, Part of #5142)
// ========================================================================

#[test]
fn test_simple_sat() {
    let mut solver = Solver::new(2);
    // (x0 OR x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model[0] || model[1]);
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_simple_unsat() {
    let mut solver = Solver::new(1);
    // x0 AND NOT x0
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(0))]);
    let result = solver.solve().into_inner();
    assert!(result.is_unsat());
}

#[test]
fn test_unit_propagation() {
    let mut solver = Solver::new(3);
    // x0 (unit)
    // NOT x0 OR x1
    // NOT x1 OR x2
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model[0]); // x0 must be true
            assert!(model[1]); // x1 must be true (propagated)
            assert!(model[2]); // x2 must be true (propagated)
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_conflict_learning() {
    let mut solver = Solver::new(3);
    // UNSAT formula that requires conflict-driven clause learning:
    // (x0 | x1) & (x0 | !x1) & (!x0 | x2) & (!x0 | !x2)
    // Proof: x0=T => x2 & !x2 (clauses 3,4); x0=F => x1 & !x1 (clauses 1,2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(2)),
    ]);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Expected UNSAT for provably unsatisfiable formula, got {result:?}",
    );
}

#[test]
fn test_preprocessing_correctness() {
    // Test that preprocessing doesn't break solver correctness
    let mut solver = Solver::new(5);
    solver.set_preprocess_enabled(true);

    // Create a SAT formula: (a OR b) AND (NOT a OR c)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)), "Expected SAT");

    // Create an UNSAT formula with preprocessing
    let mut solver2 = Solver::new(3);
    solver2.set_preprocess_enabled(true);

    // (a) AND (NOT a)
    solver2.add_clause(vec![Literal::positive(Variable(0))]);
    solver2.add_clause(vec![Literal::negative(Variable(0))]);

    let result2 = solver2.solve().into_inner();
    assert!(result2.is_unsat());
}

#[test]
fn test_preprocessing_with_random_formulas() {
    // Test that preprocessing is correct on random formulas (#113)
    // This exercises the bounds checking in propagate() during probing
    use std::collections::HashSet;

    for seed in [0u64, 42, 1707, 12345, 99999] {
        for num_vars in [3, 5, 7, 10] {
            for num_clauses in [5, 10, 15, 20] {
                let mut solver = Solver::new(num_vars);
                solver.set_preprocess_enabled(true);
                let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

                // Generate random clauses
                for i in 0..num_clauses {
                    let clause_len = 2 + ((seed + i as u64) % 3) as usize;
                    let mut clause = Vec::new();
                    let mut seen_vars: HashSet<u32> = HashSet::new();

                    for j in 0..clause_len {
                        let v = ((seed.wrapping_mul(7) + i as u64 * 13 + j as u64 * 31)
                            % num_vars as u64) as u32;
                        if seen_vars.contains(&v) {
                            continue;
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
                        continue;
                    }

                    original_clauses.push(clause.clone());
                    solver.add_clause(clause);
                }

                let result = solver.solve().into_inner();

                // If SAT, verify all original clauses are satisfied
                if let SatResult::Sat(model) = result {
                    for (idx, clause) in original_clauses.iter().enumerate() {
                        let satisfied = clause.iter().any(|&lit| {
                            let var_idx = lit.variable().index();
                            let val = model[var_idx];
                            if lit.is_positive() {
                                val
                            } else {
                                !val
                            }
                        });
                        assert!(
                            satisfied,
                            "Clause {idx} ({clause:?}) not satisfied by model {model:?} \
                             (seed={seed}, num_vars={num_vars}, num_clauses={num_clauses})"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn test_preprocessing_integration_style() {
    // Reproduce the failing integration test
    // generate_test_clauses(10, 40, 456) equivalent
    let num_vars = 10u32;
    let num_clauses = 40usize;
    let mut state = 456u64;
    let lcg_next = |s: &mut u64| {
        *s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
        *s
    };

    let mut clauses = Vec::new();
    for _ in 0..num_clauses {
        let mut clause_lits = Vec::new();
        for _ in 0..3 {
            let var = (lcg_next(&mut state) % u64::from(num_vars)) as u32;
            let sign = lcg_next(&mut state) % 2 == 0;
            let variable = Variable(var);
            let literal = if sign {
                Literal::positive(variable)
            } else {
                Literal::negative(variable)
            };
            clause_lits.push(literal);
        }
        clauses.push(clause_lits);
    }

    let mut solver = Solver::new(num_vars as usize);
    // Preprocessing enabled by default (probing + subsumption)

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (i, clause) in clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|lit| {
                let var_val = model[lit.variable().0 as usize];
                if lit.is_positive() {
                    var_val
                } else {
                    !var_val
                }
            });
            assert!(
                satisfied,
                "Clause {i} not satisfied: {clause:?}, model: {model:?}"
            );
        }
    }
}

#[test]
fn test_lazy_reimplication_trail_compaction() {
    // Test that trail is properly compacted during backtrack
    let mut solver = Solver::new(5);

    // Manually set up a scenario with literals at different levels
    solver.decision_level = 3;
    solver.trail_lim = vec![0, 2, 4]; // Level 1 starts at 0, level 2 at 2, level 3 at 4

    // Trail: [lit0@1, lit1@1, lit2@2, lit3@2, lit4@3]
    let lits = [
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ];

    for (i, &lit) in lits.iter().enumerate() {
        let var = lit.variable();
        solver.vals[lit.index()] = 1;
        solver.vals[lit.negated().index()] = -1;
        solver.var_data[var.index()].trail_pos = i as u32;
        // Set levels: 0,1 at level 1; 2,3 at level 2; 4 at level 3
        solver.var_data[var.index()].level = if i < 2 {
            1
        } else if i < 4 {
            2
        } else {
            3
        };
    }
    solver.trail = lits.to_vec();

    // Backtrack to level 1 - should keep only vars 0 and 1
    solver.backtrack(1);

    assert_eq!(solver.decision_level, 1);
    assert_eq!(solver.trail.len(), 2);
    assert!(solver.var_is_assigned(0));
    assert!(solver.var_is_assigned(1));
    assert!(!solver.var_is_assigned(2));
    assert!(!solver.var_is_assigned(3));
    assert!(!solver.var_is_assigned(4));
}

#[test]
fn test_random_var_freq_solver_soundness_sat() {
    // Simple SAT instance: (x0 v x1) ^ (x0 v ~x1) — SAT at x0=true
    let mut solver = Solver::new(2);
    let x0 = Variable(0);
    let x1 = Variable(1);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x0), Literal::negative(x1)]);
    // Max random frequency: every decision is random
    solver.set_random_var_freq(1.0);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "SAT formula with random_var_freq=1.0: {result:?}"
    );
}

#[test]
fn test_random_var_freq_solver_soundness_unsat() {
    // Simple UNSAT instance: (x) ^ (~x)
    let mut solver = Solver::new(1);
    let x = Variable(0);
    solver.add_clause(vec![Literal::positive(x)]);
    solver.add_clause(vec![Literal::negative(x)]);
    solver.set_random_var_freq(1.0);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "UNSAT formula with random_var_freq=1.0: {result:?}"
    );
}

#[test]
fn test_random_var_freq_default_is_zero() {
    let solver = Solver::new(1);
    assert!(
        (solver.random_var_freq() - 0.0).abs() < f64::EPSILON,
        "default should be 0.0"
    );
}
