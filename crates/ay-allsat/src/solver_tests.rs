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
    assert_eq!(solutions[0].is_true(1), Some(true));
    assert_eq!(solutions[0].is_true(2), Some(true));
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
    let has_10 = solutions
        .iter()
        .any(|s| s.is_true(1) == Some(true) && s.is_true(2) == Some(false));
    let has_01 = solutions
        .iter()
        .any(|s| s.is_true(1) == Some(false) && s.is_true(2) == Some(true));
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
fn declared_internal_variables_are_enumerated_even_when_absent_from_clauses() {
    let mut free = AllSatSolver::new();
    free.try_ensure_num_vars(2).unwrap();
    let free_solutions = free.try_enumerate().unwrap();
    assert_eq!(free.num_vars(), 2);
    assert_eq!(free_solutions.len(), 4);
    assert!(free_solutions
        .iter()
        .all(|solution| solution.get(1).is_some() && solution.get(2).is_some()));

    let mut partially_constrained = AllSatSolver::new();
    partially_constrained.try_ensure_num_vars(2).unwrap();
    partially_constrained.try_add_clause(vec![1]).unwrap();
    let solutions = partially_constrained.try_enumerate().unwrap();
    assert_eq!(solutions.len(), 2);
    assert!(solutions
        .iter()
        .all(|solution| solution.get(1) == Some(true)));
    assert!(solutions
        .iter()
        .any(|solution| solution.get(2) == Some(false)));
    assert!(solutions
        .iter()
        .any(|solution| solution.get(2) == Some(true)));
}

#[test]
fn declared_internal_variable_count_has_typed_backend_and_resource_errors() {
    let mut oversized = AllSatSolver::new();
    assert_eq!(
        oversized
            .try_ensure_num_vars(MAX_INTERNAL_VARIABLE_INDEX as usize + 1)
            .unwrap_err(),
        AllSatInputError::InternalVariableCountExceedsLimit {
            variable_count: MAX_INTERNAL_VARIABLE_INDEX as usize + 1,
            max_variable: MAX_INTERNAL_VARIABLE_INDEX,
        }
    );

    let external = SatSolver::new(1);
    let mut external = AllSatSolver::from_solver(external);
    assert_eq!(
        external.try_ensure_num_vars(1).unwrap_err(),
        AllSatInputError::VariableRegistrationUnsupportedBackend
    );
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
    assert_eq!(solutions[0].is_true(1), Some(true));
}

#[test]
fn internal_projection_rejects_zero_and_variables_above_formula_range() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);

    for (projection, expected) in [
        (
            vec![0],
            AllSatInputError::InternalProjectionVariableOutOfRange {
                variable: 0,
                max_variable: 2,
            },
        ),
        (
            vec![3],
            AllSatInputError::InternalProjectionVariableOutOfRange {
                variable: 3,
                max_variable: 2,
            },
        ),
    ] {
        let report = solver.enumerate_report_with_config(AllSatConfig {
            projection: Some(projection),
            ..Default::default()
        });
        assert!(report.solutions.is_empty());
        assert_eq!(report.stats.outcome, AllSatOutcome::InvalidInput);
        assert_eq!(report.stats.input_error, Some(expected));
        assert_eq!(report.stats.sat_calls, 0);
    }
}

#[test]
fn duplicate_projection_variables_are_rejected() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1]);
    let report = solver.enumerate_report_with_config(AllSatConfig {
        projection: Some(vec![1, 1]),
        ..Default::default()
    });

    assert!(report.solutions.is_empty());
    assert_eq!(report.stats.outcome, AllSatOutcome::InvalidInput);
    assert_eq!(
        report.stats.input_error,
        Some(AllSatInputError::DuplicateProjectionVariable(1))
    );
}

#[test]
fn empty_projection_has_one_projected_model() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, -1]);
    let report = solver.enumerate_report_with_config(AllSatConfig {
        projection: Some(Vec::new()),
        ..Default::default()
    });

    assert_eq!(report.solutions.len(), 1);
    assert_eq!(report.stats.outcome, AllSatOutcome::Exhaustive);
}

#[test]
fn report_and_fallible_collection_expose_a_cap() {
    let config = AllSatConfig {
        max_solutions: Some(1),
        ..Default::default()
    };
    let mut report_solver = AllSatSolver::new();
    report_solver.add_clause(vec![1, -1]);
    let report = report_solver.enumerate_report_with_config(config.clone());
    assert_eq!(report.solutions.len(), 1);
    assert_eq!(report.stats.outcome, AllSatOutcome::Capped);

    let mut exact_solver = AllSatSolver::new();
    exact_solver.add_clause(vec![1, -1]);
    let error = exact_solver.try_enumerate_with_config(config).unwrap_err();
    assert_eq!(error.outcome, AllSatOutcome::Capped);
    assert_eq!(error.solutions_found, 1);
}

#[test]
fn signed_clause_boundaries_are_typed_and_legacy_calls_fail_closed() {
    let mut solver = AllSatSolver::new();
    assert_eq!(
        solver.try_add_clause(vec![0]).unwrap_err(),
        AllSatInputError::InvalidClauseLiteral(0)
    );
    assert_eq!(
        solver.try_add_clause(vec![i32::MIN]).unwrap_err(),
        AllSatInputError::InvalidClauseLiteral(i32::MIN)
    );

    // `try_add_clause` is non-mutating on error, so a later valid formula is
    // still usable.
    solver.try_add_clause(vec![1]).unwrap();
    assert_eq!(solver.try_enumerate().unwrap().len(), 1);

    let mut compatibility_solver = AllSatSolver::new();
    compatibility_solver.add_clause(vec![0]);
    let report = compatibility_solver.enumerate_report();
    assert!(report.solutions.is_empty());
    assert_eq!(report.stats.outcome, AllSatOutcome::InvalidInput);
    assert_eq!(
        report.stats.input_error,
        Some(AllSatInputError::InvalidClauseLiteral(0))
    );
}

#[test]
fn sparse_high_internal_identifier_is_rejected_before_dense_allocation() {
    let mut solver = AllSatSolver::new();
    assert_eq!(
        solver.try_add_clause(vec![i32::MAX]).unwrap_err(),
        AllSatInputError::InternalVariableIndexExceedsLimit {
            variable: i32::MAX as u32,
            max_variable: MAX_INTERNAL_VARIABLE_INDEX,
        }
    );

    solver.add_clause(vec![i32::MAX]);
    let report = solver.enumerate_report();
    assert!(report.solutions.is_empty());
    assert_eq!(report.stats.outcome, AllSatOutcome::InvalidInput);
    assert_eq!(report.stats.sat_calls, 0);
}

#[test]
fn cap_probe_distinguishes_exact_boundary_from_an_additional_model() {
    let config = AllSatConfig {
        max_solutions: Some(1),
        ..Default::default()
    };

    let mut exact = AllSatSolver::new();
    exact.add_clause(vec![1]);
    let exact_report = exact.enumerate_report_with_config(config.clone());
    assert_eq!(exact_report.solutions.len(), 1);
    assert_eq!(exact_report.stats.outcome, AllSatOutcome::Exhaustive);
    assert_eq!(exact_report.stats.allsat_cap_hits, 0);
    assert_eq!(exact_report.stats.sat_calls, 2);

    let mut over = AllSatSolver::new();
    over.add_clause(vec![1, -1]);
    let over_report = over.enumerate_report_with_config(config);
    assert_eq!(over_report.solutions.len(), 1);
    assert_eq!(over_report.stats.outcome, AllSatOutcome::Capped);
    assert_eq!(over_report.stats.allsat_cap_hits, 1);
    assert_eq!(over_report.stats.sat_calls, 2);
}

#[test]
fn test_count() {
    let mut solver = AllSatSolver::new();

    // (x1 OR x2) - has 3 solutions
    solver.add_clause(vec![1, 2]);

    assert_eq!(solver.count().unwrap(), 3);
}

#[test]
fn test_is_sat() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);
    assert!(solver.is_sat().unwrap());

    let mut solver2 = AllSatSolver::new();
    solver2.add_clause(vec![1]);
    solver2.add_clause(vec![-1]);
    assert!(!solver2.is_sat().unwrap());
}

#[test]
fn test_unique_solution() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1]);
    solver.add_clause(vec![2]);
    assert!(solver.has_unique_solution().unwrap());

    let mut solver2 = AllSatSolver::new();
    solver2.add_clause(vec![1, 2]);
    solver2.add_clause(vec![-1, -2]);
    assert!(!solver2.has_unique_solution().unwrap()); // Has 2 solutions
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
    let solution = Solution::new(
        vec![false, true, false, true], // x1=T, x2=F, x3=T
        SolutionIndexing::OneBased,
    );

    let lits = solution.to_literals(&[1, 2, 3]).unwrap();
    assert_eq!(lits, vec![1, -2, 3]);
}

#[test]
fn solution_to_literals_rejects_unrepresentable_variables() {
    let solution = Solution::new(vec![false, true], SolutionIndexing::OneBased);

    assert_eq!(
        solution.to_literals(&[0]).unwrap_err(),
        SolutionLiteralError::VariableOutOfRange(0)
    );
    assert_eq!(
        solution.to_literals(&[i32::MAX as u32 + 1]).unwrap_err(),
        SolutionLiteralError::VariableOutOfRange(i32::MAX as u32 + 1)
    );
    assert_eq!(
        solution.to_literals(&[2]).unwrap_err(),
        SolutionLiteralError::VariableMissing(2)
    );
}

#[test]
fn test_solution_satisfies() {
    let solution = Solution::new(
        vec![false, true, false], // x1=T, x2=F
        SolutionIndexing::OneBased,
    );

    assert!(solution.satisfies(1).unwrap()); // x1 is true
    assert!(!solution.satisfies(-1).unwrap()); // NOT x1 is false
    assert!(!solution.satisfies(2).unwrap()); // x2 is false
    assert!(solution.satisfies(-2).unwrap()); // NOT x2 is true
    assert_eq!(solution.is_true(99), None);
    assert_eq!(
        solution.satisfies(-99).unwrap_err(),
        SolutionLiteralError::VariableMissing(99)
    );
    assert_eq!(
        solution.satisfies(i32::MIN).unwrap_err(),
        SolutionLiteralError::VariableOutOfRange(i32::MIN.unsigned_abs())
    );
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
fn external_enumeration_is_scoped_repeatable_and_zero_based() {
    use ay_sat::{Literal, Solver as SatSolver, Variable};

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
    let first = solver.try_enumerate().unwrap();
    assert_eq!(first.len(), 2);
    for solution in &first {
        assert_eq!(solution.indexing(), SolutionIndexing::ZeroBased);
        assert_eq!(solution.assignment.len(), 2);
        assert!(solution.get(0).is_some());
        assert_eq!(
            solution.to_literals(&[1]).unwrap_err(),
            SolutionLiteralError::IndexingMismatch(SolutionIndexing::ZeroBased)
        );
        assert_eq!(
            solution.satisfies(1).unwrap_err(),
            SolutionLiteralError::IndexingMismatch(SolutionIndexing::ZeroBased)
        );
    }

    // Scoped blockers are removed after exhaustion, so all queries see the
    // original external formula.
    assert_eq!(solver.try_enumerate().unwrap().len(), 2);
    assert!(solver.is_sat().unwrap());

    {
        let mut iter = solver.iter();
        assert!(iter.next().is_some());
        assert_eq!(iter.outcome(), AllSatOutcome::InProgress);
        // Drop before exhaustion; Drop must retract the active blocker scope.
    }
    assert_eq!(solver.stats().outcome, AllSatOutcome::IteratorDropped);
    assert_eq!(solver.try_enumerate().unwrap().len(), 2);
}

#[test]
fn external_callback_panic_retracts_blocking_scope() {
    use ay_sat::{Literal, Solver as SatSolver, Variable};
    use std::panic::{catch_unwind, AssertUnwindSafe};

    let mut sat = SatSolver::new(1);
    sat.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(0)),
    ]);
    let mut solver = AllSatSolver::from_solver(sat);

    let panic = catch_unwind(AssertUnwindSafe(|| {
        solver.enumerate_with_callback(AllSatConfig::default(), |_| {
            panic!("intentional callback panic")
        });
    }));
    assert!(panic.is_err());
    assert_eq!(solver.stats().outcome, AllSatOutcome::IteratorDropped);
    assert_eq!(solver.try_enumerate().unwrap().len(), 2);
}

#[test]
fn external_solver_can_be_recovered_after_early_iterator_drop() {
    use ay_sat::{Literal, SatResult, Solver as SatSolver, Variable};

    let mut sat = SatSolver::new(1);
    sat.add_clause(vec![Literal::positive(Variable::new(0))]);
    let mut allsat = AllSatSolver::from_solver(sat);
    {
        let mut iter = allsat.iter();
        assert!(iter.next().is_some());
    }

    let mut recovered = allsat
        .try_into_solver()
        .unwrap_or_else(|_allsat| panic!("external backend must be recoverable"));
    assert!(matches!(recovered.solve().into_inner(), SatResult::Sat(_)));
}

#[test]
fn external_scope_pop_failure_is_reported_as_invalid_input() {
    use ay_sat::Solver as SatSolver;

    let mut solver = AllSatSolver::from_solver(SatSolver::new(1));
    {
        let mut iter = solver.iter();
        let SolverBackend::External(sat_solver) = &mut iter.solver.backend else {
            unreachable!("test constructed the external backend")
        };
        assert!(sat_solver.pop(), "iterator must have pushed a scope");
        iter.finish(AllSatOutcome::Exhaustive);
        assert_eq!(iter.outcome(), AllSatOutcome::InvalidInput);
        assert_eq!(
            iter.run_stats.input_error,
            Some(AllSatInputError::BackendScopePopFailed)
        );
    }
    assert_eq!(solver.stats().outcome, AllSatOutcome::InvalidInput);
    assert_eq!(
        solver.stats().input_error,
        Some(AllSatInputError::BackendScopePopFailed)
    );
    let report = solver.enumerate_report();
    assert_eq!(report.stats.outcome, AllSatOutcome::InvalidInput);
    assert_eq!(report.stats.sat_calls, 0);
    assert!(
        solver.try_into_solver().is_err(),
        "a solver whose enumeration scope could not be retracted must not be exposed"
    );
}

#[test]
fn external_projection_rejects_variables_at_or_above_user_count() {
    use ay_sat::Solver as SatSolver;

    let mut solver = AllSatSolver::from_solver(SatSolver::new(2));
    let report = solver.enumerate_report_with_config(AllSatConfig {
        projection: Some(vec![2]),
        ..Default::default()
    });

    assert!(report.solutions.is_empty());
    assert_eq!(report.stats.outcome, AllSatOutcome::InvalidInput);
    assert_eq!(
        report.stats.input_error,
        Some(AllSatInputError::ExternalProjectionVariableOutOfRange {
            variable: 2,
            variable_count: 2,
        })
    );
    assert_eq!(report.stats.sat_calls, 0);
}

#[test]
fn signed_clause_addition_is_rejected_for_external_backends() {
    use ay_sat::Solver as SatSolver;

    let mut solver = AllSatSolver::from_solver(SatSolver::new(1));
    assert_eq!(
        solver.try_add_clause(vec![1]).unwrap_err(),
        AllSatInputError::ClauseAdditionUnsupportedBackend
    );

    solver.add_clause(vec![1]);
    let report = solver.enumerate_report();
    assert!(report.solutions.is_empty());
    assert_eq!(report.stats.outcome, AllSatOutcome::InvalidInput);
    assert_eq!(
        report.stats.input_error,
        Some(AllSatInputError::ClauseAdditionUnsupportedBackend)
    );
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
    assert_eq!(solutions[0].is_true(0), Some(true));
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

fn conflict_budget_exhausted_solver() -> AllSatSolver {
    // Pigeonhole 5 -> 4 is small but requires search. A zero conflict budget
    // therefore deterministically stops at the first search conflict.
    const PIGEONS: usize = 5;
    const HOLES: usize = 4;
    let mut sat = SatSolver::new(PIGEONS * HOLES);
    for pigeon in 0..PIGEONS {
        sat.add_clause(
            (0..HOLES)
                .map(|hole| Literal::positive(Variable::new((pigeon * HOLES + hole) as u32)))
                .collect(),
        );
    }
    for hole in 0..HOLES {
        for first in 0..PIGEONS {
            for second in first + 1..PIGEONS {
                sat.add_clause(vec![
                    Literal::negative(Variable::new((first * HOLES + hole) as u32)),
                    Literal::negative(Variable::new((second * HOLES + hole) as u32)),
                ]);
            }
        }
    }
    sat.set_preprocess_enabled(false);
    sat.set_conflict_budget(Some(0));
    AllSatSolver::from_solver(sat)
}

#[test]
fn callback_reports_backend_unknown() {
    let mut solver = conflict_budget_exhausted_solver();
    let stats = solver.enumerate_with_callback(AllSatConfig::default(), |_| true);

    assert_eq!(stats.outcome, AllSatOutcome::SolverUnknown);
    assert_eq!(stats.solutions_found, 0);
    assert_eq!(stats.sat_calls, 1);
    assert_eq!(solver.stats().outcome, AllSatOutcome::SolverUnknown);
}

#[test]
fn iterator_is_terminal_after_backend_unknown() {
    let mut solver = conflict_budget_exhausted_solver();
    {
        let mut iter = solver.iter();
        assert!(iter.next().is_none());
        assert_eq!(iter.outcome(), AllSatOutcome::SolverUnknown);
        assert!(iter.next().is_none());
    }

    assert_eq!(solver.stats().sat_calls, 1);
    assert_eq!(solver.stats().outcome, AllSatOutcome::SolverUnknown);
}

#[test]
fn enumeration_predicates_fail_closed_on_backend_unknown() {
    let mut count_solver = conflict_budget_exhausted_solver();
    let count_error = count_solver.count().unwrap_err();
    assert_eq!(count_error.outcome, AllSatOutcome::SolverUnknown);
    assert_eq!(count_error.solutions_found, 0);

    let mut sat_solver = conflict_budget_exhausted_solver();
    assert_eq!(
        sat_solver.is_sat().unwrap_err().outcome,
        AllSatOutcome::SolverUnknown
    );

    let mut unique_solver = conflict_budget_exhausted_solver();
    assert_eq!(
        unique_solver.has_unique_solution().unwrap_err().outcome,
        AllSatOutcome::SolverUnknown
    );
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
    assert_eq!(stats.outcome, AllSatOutcome::CallbackStopped);
    assert_eq!(solver.stats().outcome, AllSatOutcome::CallbackStopped);
}

#[test]
fn test_exhausted_iterator_does_not_resolve() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1]);

    {
        let mut iter = solver.iter();
        assert!(iter.next().is_some());
        assert!(iter.next().is_none());
        assert!(iter.next().is_none());
        assert!(iter.next().is_none());
    }

    // One SAT call finds the model and one proves exhaustion. Repeated calls
    // after `None` must be side-effect free.
    assert_eq!(solver.stats().sat_calls, 2);
    assert_eq!(solver.stats().outcome, AllSatOutcome::Exhaustive);
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
    assert_eq!(collected[0].is_true(1), Some(true));
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
    drop(iter);

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
        let count = (1..=3).filter(|&v| sol.is_true(v) == Some(true)).count();
        assert!(count % 2 == 1, "XOR chain should have odd parity");
    }
}
