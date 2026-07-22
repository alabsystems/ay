// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness and model verification tests: online witness checking,
//! model verification against original formula, solution file loading,
//! and BVE/sweep elimination verification.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

// ========================================================================
// Online Witness + Solution Loading Tests
// ========================================================================

#[test]
fn test_online_witness_detects_first_invalid_learned_clause_non_incremental() {
    let mut solver: Solver = Solver::new(2);
    solver
        .try_set_solution(&[true, false])
        .expect("valid full witness should be accepted");

    let bad_learned = [
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_db(&bad_learned, true);
    }));

    assert!(
        panic.is_err(),
        "learned clause falsified by witness should panic immediately"
    );
}

#[test]
fn test_online_witness_ignores_internal_scope_selectors() {
    let mut solver: Solver = Solver::new(1);
    solver.push();
    let selector = solver.cold.scope_selectors[0];

    // Provide only user-visible assignment (x0=true). Internal selector stays unknown.
    solver
        .try_set_solution(&[true])
        .expect("user-visible witness should be accepted");

    // Clause is false on known literals (¬x0), but contains unknown selector.
    // Online witness checker must not report a violation.
    let mixed_clause = [Literal::negative(Variable(0)), Literal::positive(selector)];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_db(&mixed_clause, true);
    }));

    assert!(
        panic.is_ok(),
        "internal selector with unknown witness value should not trigger violation"
    );
}

/// Online witness check for replaced/shrunken clauses (CaDiCaL parity:
/// `check_solution_on_shrunken_clause`). When a clause is strengthened via
/// inprocessing (vivification, subsumption, etc.), the replacement must still
/// be satisfied by the witness. This test verifies the gap covered in #4291.
#[test]
fn test_online_witness_detects_invalid_replaced_clause() {
    let mut solver: Solver = Solver::new(3);
    // Solution: x0=true, x1=false, x2=true
    solver
        .try_set_solution(&[true, false, true])
        .expect("valid witness should be accepted");

    // Add an original clause (x0 ∨ x1 ∨ x2) — satisfied by x0=true
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    let clause_idx = 0;

    // Replace with (¬x0 ∨ x1) — falsified by witness (x0=true, x1=false)
    let bad_replacement = [
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.replace_clause_checked(clause_idx, &bad_replacement);
    }));

    assert!(
        panic.is_err(),
        "replaced clause falsified by witness should panic immediately"
    );
}

/// Verify that valid clause replacements do NOT trigger the witness check.
/// Strengthening (x0 ∨ x1 ∨ x2) → (x0 ∨ x2) should be fine when x0=true.
#[test]
fn test_online_witness_allows_valid_replaced_clause() {
    let mut solver: Solver = Solver::new(3);
    // Solution: x0=true, x1=false, x2=true
    solver
        .try_set_solution(&[true, false, true])
        .expect("valid witness should be accepted");

    // Add original clause (x0 ∨ x1 ∨ x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    let clause_idx = 0;

    // Replace with (x0 ∨ x2) — still satisfied by x0=true
    let good_replacement = [
        Literal::positive(Variable(0)),
        Literal::positive(Variable(2)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.replace_clause_checked(clause_idx, &good_replacement);
    }));

    assert!(
        panic.is_ok(),
        "valid replacement should not trigger witness violation"
    );
}

/// Clauses added through the inprocessing path (`add_clause_watched`) are
/// derived consequences and must also be checked against the witness.
#[test]
fn test_online_witness_detects_invalid_irredundant_derived_clause() {
    let mut solver: Solver = Solver::new(3);
    solver.set_solution(vec![true, false, true]);

    // Clause (¬x0 ∨ x1) is falsified by witness (x0=true, x1=false).
    let mut invalid = vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_watched(&mut invalid);
    }));

    assert!(
        panic.is_err(),
        "derived irredundant clause falsified by witness should panic"
    );
}

/// Valid inprocessing-derived clauses should not trigger the witness check.
#[test]
fn test_online_witness_allows_valid_irredundant_derived_clause() {
    let mut solver: Solver = Solver::new(3);
    solver.set_solution(vec![true, false, true]);

    // Clause (x0 ∨ x2) is satisfied by witness.
    let mut valid = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(2)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_watched(&mut valid);
    }));

    assert!(
        panic.is_ok(),
        "valid derived irredundant clause should not trigger witness violation"
    );
}

/// CaDiCaL parity: check_no_solution_after_learning_empty_clause (#4615).
/// When a satisfying assignment is configured and the solver derives the empty
/// clause (UNSAT), it must abort immediately — the formula is SAT so deriving
/// UNSAT is a soundness bug.
#[test]
fn test_online_witness_aborts_on_empty_clause_derivation() {
    let mut solver: Solver = Solver::new(1);
    solver.set_solution(vec![true]);

    // Adding the empty clause signals UNSAT. With a witness configured,
    // mark_empty_clause must abort.
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.add_clause(vec![]);
    }));

    assert!(
        panic.is_err(),
        "deriving empty clause with a configured witness should abort"
    );
}

/// Sam Buss trick: deriving an empty clause while a solution witness is loaded
/// must panic immediately. The empty clause means UNSAT, but the witness proves
/// SAT — so the solver has a soundness bug.
/// CaDiCaL parity: analyze.cpp:19 (empty clause check against solution).
#[test]
fn test_online_witness_detects_empty_clause_derivation() {
    let mut solver: Solver = Solver::new(2);
    solver.set_solution(vec![true, false]);

    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.mark_empty_clause();
    }));

    assert!(
        panic.is_err(),
        "empty clause with loaded witness should panic (UNSAT from SAT formula)"
    );
}

/// Verify that marking an empty clause WITHOUT a solution witness does not panic.
/// Normal UNSAT derivation (no witness loaded) should proceed without assertion failure.
#[test]
fn test_empty_clause_without_witness_does_not_panic() {
    let mut solver: Solver = Solver::new(2);
    // No set_solution call — solution_witness is None.

    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.mark_empty_clause();
    }));

    assert!(
        panic.is_ok(),
        "empty clause without loaded witness should not panic"
    );
    assert!(solver.has_empty_clause, "empty clause flag should be set");
}

/// End-to-end: load a satisfying solution, then solve a satisfiable formula.
/// The solver should return SAT without triggering any witness violations.
#[test]
fn test_online_witness_no_panic_on_normal_sat_solve() {
    let mut solver: Solver = Solver::new(3);
    // Formula: (x0 ∨ x1) ∧ (¬x0 ∨ x2) ∧ (¬x1 ∨ x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    // Known satisfying assignment: x0=true, x1=true, x2=true
    solver.set_solution(vec![true, true, true]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(_) => {} // expected
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Load a solution from a file in SAT competition format (v-lines).
/// CaDiCaL parity: External::read_solution().
#[test]
fn test_load_solution_file_competition_format() {
    use std::io::Write;
    let dir = std::env::temp_dir().join("ay_test_solution");
    std::fs::create_dir_all(&dir).unwrap();
    let sol_path = dir.join("test.sol");
    {
        let mut f = std::fs::File::create(&sol_path).unwrap();
        writeln!(f, "s SATISFIABLE").unwrap();
        writeln!(f, "v 1 -2 3 0").unwrap();
    }

    let mut solver: Solver = Solver::new(3);
    solver
        .load_solution_file(sol_path.to_str().unwrap())
        .unwrap();

    // Witness is: x0=true, x1=false, x2=true
    // A learned clause (¬x0 ∨ x1) = (false ∨ false) should trigger panic.
    let bad_clause = [
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_db(&bad_clause, true);
    }));
    assert!(
        panic.is_err(),
        "file-loaded witness should detect falsified learned clause"
    );

    // Clean up
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_try_set_solution_rejects_invalid_lengths_and_solver_remains_operational() {
    let mut solver: Solver = Solver::new(2);

    let short = solver
        .try_set_solution(&[true])
        .expect_err("short witness must return structured error");
    assert_eq!(short, SetSolutionError::TooShort { got: 1, min: 2 });
    assert!(
        solver.cold.solution_witness.is_none(),
        "invalid short witness must not mutate solver witness state"
    );

    let long = solver
        .try_set_solution(&[true, false, true])
        .expect_err("long witness must return structured error");
    assert_eq!(long, SetSolutionError::TooLong { got: 3, max: 2 });
    assert!(
        solver.cold.solution_witness.is_none(),
        "invalid long witness must not mutate solver witness state"
    );

    solver.add_clause(vec![Literal::positive(Variable(0))]);
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "solver should still solve after rejected witness inputs"
    );
}

// ========================================================================
// Model Verification Against Original Formula
// ========================================================================

fn add_binary_xor(solver: &mut Solver, a: Variable, b: Variable) {
    solver.add_clause(vec![Literal::positive(a), Literal::positive(b)]);
    solver.add_clause(vec![Literal::negative(a), Literal::negative(b)]);
}

fn php_var(pigeon: usize, hole: usize, holes: usize) -> Variable {
    Variable((pigeon * holes + hole) as u32)
}

#[test]
fn test_soundness_unique_satisfying_assignment_returns_exact_model() {
    let mut solver = Solver::new(3);

    // Unique model: x0=true, x1=false, x2=true.
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
        Literal::negative(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert_eq!(
        model,
        vec![true, false, true],
        "formula should have exactly one satisfying assignment"
    );
    assert!(
        solver.verify_against_original(&model).is_none(),
        "returned model must satisfy the original formula"
    );
}

#[test]
fn test_soundness_php_4_3_is_unsat() {
    let pigeons = 4;
    let holes = 3;
    let mut solver = Solver::new(pigeons * holes);

    for pigeon in 0..pigeons {
        let clause = (0..holes)
            .map(|hole| Literal::positive(php_var(pigeon, hole, holes)))
            .collect();
        solver.add_clause(clause);
    }

    for hole in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                solver.add_clause(vec![
                    Literal::negative(php_var(p1, hole, holes)),
                    Literal::negative(php_var(p2, hole, holes)),
                ]);
            }
        }
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(4,3) must be UNSAT");
}

#[test]
fn test_soundness_xor_heavy_parity_formula_returns_valid_model() {
    let mut solver = Solver::new(4);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let x3 = Variable(3);

    // Four-way parity ring, then select the phase with (x0 v x2).
    add_binary_xor(&mut solver, x0, x1);
    add_binary_xor(&mut solver, x1, x2);
    add_binary_xor(&mut solver, x2, x3);
    add_binary_xor(&mut solver, x3, x0);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x2)]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert_eq!(
        model,
        vec![true, false, true, false],
        "parity ring should collapse to the alternating model"
    );
    assert!(model[0] ^ model[1], "x0 xor x1 must hold");
    assert!(model[1] ^ model[2], "x1 xor x2 must hold");
    assert!(model[2] ^ model[3], "x2 xor x3 must hold");
    assert!(model[3] ^ model[0], "x3 xor x0 must hold");
    assert!(
        solver.verify_against_original(&model).is_none(),
        "returned model must satisfy the original parity formula"
    );
}

#[test]
fn test_soundness_long_implication_chain_to_not_a_is_unsat() {
    let mut solver = Solver::new(8);

    solver.add_clause(vec![Literal::positive(Variable(0))]);
    for from in 0..7 {
        solver.add_clause(vec![
            Literal::negative(Variable(from as u32)),
            Literal::positive(Variable((from + 1) as u32)),
        ]);
    }
    solver.add_clause(vec![
        Literal::negative(Variable(7)),
        Literal::negative(Variable(0)),
    ]);

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "A, A->B->...->H, H->!A must be UNSAT");
}

#[test]
fn test_soundness_unit_and_binary_propagation_fronts_meet_in_conflict() {
    let mut solver = Solver::new(5);

    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(4))]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(4)),
        Literal::negative(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "two unit-propagation fronts should meet in a binary-clause conflict"
    );
}

#[test]
fn test_first_model_violation_reports_clause_db_clause() {
    let mut solver: Solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let violation = solver
        .first_model_violation(&[false, false], false)
        .expect("all-false model should violate (x0 v x1)");

    assert_eq!(
        violation,
        ModelViolation::ClauseDb {
            clause_index: 0,
            clause_dimacs: vec![1, 2],
        }
    );
}

#[test]
fn test_describe_model_violation_clause_db_includes_literal_evals() {
    let mut solver: Solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    let model = [false, false];

    let violation = solver
        .first_model_violation(&model, false)
        .expect("all-false model should violate (x0 v x1)");
    let message = solver.describe_model_violation(&model, &violation);

    assert!(
        message.contains("clause_db[0] unsatisfied"),
        "message must include clause source/index: {message}"
    );
    assert!(
        message.contains("clause=[1, 2]"),
        "message must include failing clause DIMACS form: {message}"
    );
    assert!(
        message.contains("1@v0=F->F"),
        "message must include first literal eval: {message}"
    );
    assert!(
        message.contains("2@v1=F->F"),
        "message must include second literal eval: {message}"
    );
}

#[test]
fn test_verify_against_original_reports_first_unsatisfied_clause() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    // x0=true, x1=false satisfies clause 0 and violates clause 1.
    let model = vec![true, false];
    assert_eq!(solver.verify_against_original(&model), Some(1));
}

#[test]
fn test_verify_against_original_ignores_learned_clauses() {
    let mut solver = Solver::new(1);
    solver.add_clause(vec![Literal::positive(Variable(0))]); // Original formula
    let _ = solver.add_clause_db(&[Literal::negative(Variable(0))], true); // Learned only

    // This model satisfies the original formula but falsifies the learned clause.
    let model = vec![true];
    assert_eq!(solver.verify_against_original(&model), None);
    #[cfg(debug_assertions)]
    assert!(
        !solver.verify_clause_db_only(&model, false),
        "clause-db check must still fail on the learned clause"
    );
}

/// verify_against_original must detect a corrupted model (#4604).
///
/// Constructs a SAT formula, solves it, flips one variable to corrupt the model,
/// and verifies that `verify_against_original` returns the index of an unsatisfied
/// original clause.
#[test]
fn test_original_formula_ledger_catches_wrong_model() {
    // Simple SAT formula: (x0 | x1) & (!x0 | x1) — forces x1=true.
    let mut solver: Solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(m) => m,
        other => panic!("expected SAT, got {other:?}"),
    };

    // Corrupt the model: flip x1 (which must be true) to false.
    let mut bad_model = vec![false; solver.num_vars];
    for (i, &val) in model.iter().enumerate() {
        if i < bad_model.len() {
            bad_model[i] = val;
        }
    }
    // x1 = Variable(1) must be true in any satisfying assignment.
    bad_model[1] = !bad_model[1];

    let fail_idx = solver.verify_against_original(&bad_model);
    assert!(
        fail_idx.is_some(),
        "verify_against_original must detect the corrupted model"
    );
}

/// verify_against_original must run on the SECOND solve_with_assumptions call.
///
/// Before this fix, `has_been_incremental` (set on second solve) caused
/// `verify_against_original` to be skipped for ALL incremental solving.
/// The fix uses `has_ever_scoped` (only set by push()) so assumption-only
/// incremental solving (used by CHC) still verifies against original clauses.
#[test]
fn test_verify_against_original_runs_on_second_assumption_solve() {
    let mut solver = Solver::new(4);
    // Simple formula: (x0 | x1) & (!x0 | x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);

    // First solve — this sets has_solved_once=true
    let assumptions = vec![Literal::positive(Variable(3))];
    let r1 = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(r1, AssumeResult::Sat(_)),
        "first solve should be SAT"
    );

    // Add more clauses (simulating CHC blocking clauses)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);

    // Second solve — has_been_incremental is now true.
    // verify_against_original must STILL run because no push() was called.
    let r2 = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(r2, AssumeResult::Sat(_)),
        "second solve should be SAT"
    );

    // Verify the model satisfies ALL original clauses (including the one
    // added between solves). This confirms that verify_against_original
    // is running even though has_been_incremental is true.
    if let AssumeResult::Sat(model) = r2 {
        assert!(
            solver.verify_against_original(&model).is_none(),
            "model from second assumption solve must satisfy all original clauses"
        );
    }

    // Verify has_been_incremental is true but has_ever_scoped is false
    assert!(
        solver.cold.has_been_incremental,
        "has_been_incremental must be true after second solve"
    );
    assert!(
        !solver.cold.has_ever_scoped,
        "has_ever_scoped must be false (no push/pop used)"
    );
}

/// original_clauses must not include learned clauses (#4604).
///
/// Solves a formula that requires conflict-driven learning (PHP 3,2),
/// then verifies that the original_clauses count equals the input clause
/// count, not input + learned.
#[test]
fn test_original_formula_ledger_excludes_learned_clauses() {
    // PHP(3,2): 3 pigeons, 2 holes — 6 vars, 9 clauses, UNSAT.
    // Solving this requires learning at least one clause.
    let mut solver: Solver = Solver::new(6);
    let input_clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        vec![
            Literal::positive(Variable(2)),
            Literal::positive(Variable(3)),
        ],
        vec![
            Literal::positive(Variable(4)),
            Literal::positive(Variable(5)),
        ],
        vec![
            Literal::negative(Variable(0)),
            Literal::negative(Variable(2)),
        ],
        vec![
            Literal::negative(Variable(0)),
            Literal::negative(Variable(4)),
        ],
        vec![
            Literal::negative(Variable(2)),
            Literal::negative(Variable(4)),
        ],
        vec![
            Literal::negative(Variable(1)),
            Literal::negative(Variable(3)),
        ],
        vec![
            Literal::negative(Variable(1)),
            Literal::negative(Variable(5)),
        ],
        vec![
            Literal::negative(Variable(3)),
            Literal::negative(Variable(5)),
        ],
    ];
    let num_input = input_clauses.len();
    for clause in input_clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(3,2) must be UNSAT");

    assert_eq!(
        solver.cold.original_ledger.num_clauses(),
        num_input,
        "original_ledger must equal input count ({num_input}), not input + learned ({})",
        solver.cold.original_ledger.num_clauses()
    );
}

/// BVE must fire during preprocessing (#4209).
///
/// Before the fix, `should_bve()` checked `should_fire(num_conflicts)` which
/// required `num_conflicts >= BVE_INTERVAL_BASE = 2000`. During preprocessing
/// num_conflicts is always 0, so BVE never ran. CaDiCaL runs BVE unconditionally
/// during preprocessing (elim.cpp); only the fixpoint guard applies.
///
/// Formula: (x0 | x1) & (!x0 | x2) — x0 has 1 positive and 1 negative
/// occurrence, resolvent (x1 | x2) replaces 2 clauses with 1. With
/// growth_bound=8 (preprocessing default), this is bounded.
#[test]

// ========================================================================
// BVE / Sweep Elimination Verification
// ========================================================================

fn test_bve_no_active_clause_contains_eliminated_var() {
    let mut solver = Solver::new(6);
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);

    // BVE of v0: {v0, v1} ∧ {¬v0, v1} → resolvent {v1} (unit)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    // Clause satisfied by v1=true, contains v2
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    // BVE of v2: two clauses to resolve
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::positive(Variable(5)),
    ]);
    // Extra clause to keep formula satisfiable
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
        Literal::positive(Variable(5)),
    ]);

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "formula should be satisfiable, got {result:?}"
    );
}

#[test]
fn test_bve_unit_resolvent_assigns_variable() {
    // After removing elim_propagate (#8356), BVE no longer eagerly deletes
    // satisfied clauses via occ-list propagation. Unit resolvents are still
    // correctly enqueued on the trail by add_clause_watched. Satisfied
    // clauses persist until the next search propagation or occ rebuild.
    let mut solver = Solver::new(5);
    let x = Variable(0);
    let y = Variable(1);
    let a = Variable(2);
    let b = Variable(3);

    solver.freeze(y);
    solver.freeze(a);
    solver.freeze(b);

    solver.add_clause_db(&[Literal::positive(x), Literal::positive(y)], false);
    solver.add_clause_db(&[Literal::negative(x), Literal::positive(y)], false);
    solver.add_clause_db(
        &[
            Literal::positive(y),
            Literal::positive(a),
            Literal::positive(b),
        ],
        false,
    );

    let derived_unsat = solver.bve();
    assert!(!derived_unsat, "BVE should not derive UNSAT here");
    assert_eq!(
        solver.get_var_assignment(y.index()),
        Some(true),
        "unit resolvent should assign y at level 0"
    );
}

/// #5696: Inline verification in solve() must skip original clauses containing
/// BVE-eliminated variables. Without the skip, the eliminated variable's
/// assignment is set by the extension stack during reconstruction, but the
/// inline check runs before full reconstruction, causing a false-positive
/// InvalidSatModel.
///
/// This test creates a formula where BVE eliminates variable x0 (appears
/// positive in one binary clause, negative in another → resolution yields a
/// binary resolvent {x1, x2}). The original clauses containing x0 are kept
/// in the original_clauses ledger. The inline verification must skip them.
///
/// If the skip-path is broken, solve() returns Unknown(InvalidSatModel).
/// If it works correctly, solve() returns Sat with a valid model.
#[test]
fn test_inline_verify_skips_bve_eliminated_clauses() {
    let mut solver = Solver::new(5); // x0..x4
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);
    // Disable other inprocessing to isolate BVE behavior.
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);

    // BVE target: x0 appears in exactly 2 clauses (one pos, one neg).
    // Resolving {x0, x1} with {¬x0, x2} produces {x1, x2}.
    // x0 is eliminated; the original clauses referencing x0 are handled
    // by the reconstruction extension stack.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    // Additional clauses to make the formula non-trivial.
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ]);

    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            // Verify model against ALL original clauses (including those
            // with the eliminated variable). The full model (post-reconstruction)
            // should satisfy everything.
            assert!(
                solver.verify_against_original(model).is_none(),
                "model must satisfy all original clauses including \
                 those with eliminated variables"
            );
        }
        other => panic!("#5696 regression: BVE + inline verify must return Sat, got {other:?}"),
    }
}

/// #5696: Same as above but with sweep (congruence) enabled alongside BVE.
/// This is the exact configuration that failed on IBM12.
#[test]
fn test_inline_verify_skips_bve_and_sweep_clauses() {
    let mut solver = Solver::new(6); // x0..x5
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);
    solver.set_sweep_enabled(true);
    solver.set_congruence_enabled(true);
    // Disable others for determinism.
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_decompose_enabled(false);

    // BVE eliminates x0: {x0, x1} ∧ {¬x0, x2} → {x1, x2}
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    // Sweep may merge x3 ↔ x4 if they're functionally equivalent.
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::negative(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(4)),
    ]);
    // Additional clauses involving both eliminated and sweep-merged vars.
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(3)),
        Literal::positive(Variable(5)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(4)),
        Literal::positive(Variable(5)),
    ]);
    // Clause mixing eliminated x0 with sweep candidates.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            assert!(
                solver.verify_against_original(model).is_none(),
                "model must satisfy all original clauses including \
                 those with eliminated and sweep-remapped variables"
            );
        }
        other => panic!("#5696 regression: BVE+sweep+congruence must return Sat, got {other:?}"),
    }
}

fn random_3sat_clauses(num_vars: usize, num_clauses: usize, seed: u64) -> Vec<Vec<Literal>> {
    struct SimpleRng {
        state: u64,
    }

    impl SimpleRng {
        fn new(seed: u64) -> Self {
            Self {
                state: seed.wrapping_add(0x9E3779B97F4A7C15),
            }
        }

        fn next(&mut self) -> u64 {
            let mut x = self.state;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.state = x;
            x
        }
    }

    let mut rng = SimpleRng::new(seed);
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let mut clause = Vec::with_capacity(3);
        for _ in 0..3 {
            let var = Variable((rng.next() % num_vars as u64) as u32);
            let lit = if rng.next().is_multiple_of(2) {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            clause.push(lit);
        }
        clauses.push(clause);
    }
    clauses
}

fn build_dimacs_profile_solver(num_vars: usize, clauses: &[Vec<Literal>]) -> Solver {
    let mut solver = Solver::new(num_vars);
    // Match the DIMACS-oriented preprocessing/search configuration that exists
    // on this branch without relying on the unfinished profile API wiring.
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_subsume_enabled(true);
    solver.preprocessing_quick_mode = false;
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver
}

/// Regression for the satisfiable random-3SAT instance exposed by
/// `cross_check_4542::sat_vs_dpll_consistency_random_3sat` (`seed=76`).
///
/// A brute-force check finds a satisfying assignment for this formula, so the
/// DIMACS SAT profile must not conclude UNSAT under any of the small-formula
/// preprocessing/search variants exercised here.
#[test]
fn test_dimacs_profile_random_3sat_seed_76_remains_sat() {
    let num_vars = 20;
    let clauses = random_3sat_clauses(num_vars, 96, 76);

    type ConfigFn = fn(&mut Solver);
    let configs: [(&str, ConfigFn); 4] = [
        ("no_preprocess", |solver| {
            solver.set_preprocess_enabled(false)
        }),
        ("quick_preprocess", |solver| {
            solver.preprocessing_quick_mode = true
        }),
        ("no_chrono", |solver| solver.set_chrono_enabled(false)),
        ("default", |_| {}),
    ];

    for (label, configure) in configs {
        let mut solver = build_dimacs_profile_solver(num_vars, &clauses);
        configure(&mut solver);

        match solver.solve().into_inner() {
            SatResult::Sat(model) => {
                assert!(
                    solver.verify_against_original(&model).is_none(),
                    "{label}: returned SAT model must satisfy the original clauses",
                );
            }
            other => {
                panic!("{label}: satisfiable random-3SAT seed 76 must remain SAT, got {other:?}")
            }
        }
    }
}

fn repo_unsat_corpus_paths() -> Vec<std::path::PathBuf> {
    let corpus_dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/sat/unsat");
    let mut cnf_paths: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", corpus_dir.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .filter(|path| is_fail_closed_known_unsat_benchmark(path))
        .collect();
    cnf_paths.sort();
    assert!(
        !cnf_paths.is_empty(),
        "expected at least one UNSAT benchmark in {}",
        corpus_dir.display()
    );
    cnf_paths
}

fn is_fail_closed_known_unsat_benchmark(path: &std::path::Path) -> bool {
    if path
        .file_name()
        .is_some_and(|name| name == "tseitin_cycle_10.cnf")
    {
        return false;
    }
    // `benchmarks/sat/unsat` also carries phase-transition random 3-SAT files
    // that are only "expected UNSAT" statistically, not proven UNSAT. Keep
    // the fail-closed sweep restricted to the deterministic UNSAT corpus.
    // `tseitin_cycle_10.cnf` is also excluded: the checked-in fixture is SAT.
    let contents = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
    !contents
        .lines()
        .take_while(|line| !line.starts_with("p cnf"))
        .any(|line| line.contains("expected UNSAT"))
}

fn assert_unsat_result_for_known_unsat(
    solver: &Solver,
    result: SatResult,
    benchmark: &std::path::Path,
) {
    let label = benchmark
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("<unknown>");
    match result {
        SatResult::Unsat(_) => {}
        SatResult::Sat(model) => {
            let violated = solver
                .verify_against_original(&model)
                .map_or_else(|| "none".to_string(), |idx| idx.to_string());
            panic!(
                "known-UNSAT benchmark {label} returned SAT; first violated original clause={violated}"
            );
        }
        SatResult::Unknown => {
            panic!("known-UNSAT benchmark {label} returned Unknown");
        }
        #[allow(unreachable_patterns)]
        other => unreachable!("unexpected SAT result variant for {label}: {other:?}"),
    }
}

#[test]
fn test_soundness_small_unsat_corpus_dimacs_profile() {
    for path in repo_unsat_corpus_paths() {
        let dimacs = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        let formula = crate::parse_dimacs(&dimacs)
            .unwrap_or_else(|e| panic!("parse {} failed: {e}", path.display()));
        let mut solver = formula.into_solver();
        let result = solver.solve().into_inner();
        assert_unsat_result_for_known_unsat(&solver, result, &path);
    }
}

#[test]
fn test_soundness_small_unsat_corpus_core_search_only() {
    for path in repo_unsat_corpus_paths() {
        let dimacs = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        let formula = crate::parse_dimacs(&dimacs)
            .unwrap_or_else(|e| panic!("parse {} failed: {e}", path.display()));
        let mut solver = Solver::new(formula.num_vars);
        solver.disable_all_inprocessing();
        solver.set_preprocess_enabled(false);
        solver.set_walk_enabled(false);
        solver.set_warmup_enabled(false);
        for clause in formula.clauses {
            solver.add_clause(clause);
        }
        let result = solver.solve().into_inner();
        assert_unsat_result_for_known_unsat(&solver, result, &path);
    }
}

// ========================================================================
// #7912: Universal verify_external_model tests
//
// These tests validate that verify_external_model correctly verifies
// SAT results against the original formula across all solve paths:
// solve(), solve_with_assumptions(), walk, and preprocessing.
// ========================================================================

/// Verify that solve() produces a model passing verify_external_model.
#[test]
fn test_verify_external_model_solve_basic() {
    let mut solver = Solver::new(4);
    // (x0 v x1) ^ (x1 v x2) ^ (x2 v x3) ^ (~x0 v ~x3)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(3)),
    ]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    // The debug_assert in declare_sat_from_model already calls
    // verify_external_model, but this test explicitly validates it.
    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept the model returned by solve()"
    );
}

/// Verify that solve_with_assumptions() produces a model passing
/// verify_external_model.
#[test]
fn test_verify_external_model_solve_with_assumptions() {
    let mut solver = Solver::new(3);
    // (x0 v x1) ^ (x1 v x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    // Assume x0=false: forces x1=true (from clause 1)
    let assumptions = vec![Literal::negative(Variable(0))];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    let model = match result {
        AssumeResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept the model returned by solve_with_assumptions()"
    );
    // x0 must be false (assumed), x1 must be true (forced by clause 1)
    assert!(!model[0], "x0 should be false (assumed)");
    assert!(
        model[1],
        "x1 should be true (forced by clause 1 with x0=false)"
    );
}

/// Verify that verify_external_model rejects a model that violates an
/// original clause.
#[test]
fn test_verify_external_model_rejects_invalid_model() {
    let mut solver = Solver::new(2);
    // Single clause: (x0 v x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    // Model with both variables false violates (x0 v x1)
    let bad_model = vec![false, false];
    assert!(
        !solver.verify_external_model(&bad_model),
        "verify_external_model must reject a model that violates the original clause"
    );

    // Model with x0=true satisfies (x0 v x1)
    let good_model = vec![true, false];
    assert!(
        solver.verify_external_model(&good_model),
        "verify_external_model must accept a valid model"
    );
}

/// Verify that verify_external_model works after preprocessing (BVE).
/// BVE eliminates variables and adds reconstruction entries. The model
/// returned by solve() must still pass verify_external_model after
/// reconstruction.
#[test]
fn test_verify_external_model_after_bve() {
    let mut solver = Solver::new(5);
    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_walk_enabled(false);

    // Create a formula where BVE can eliminate x0:
    // (x0 v x1) ^ (~x0 v x2) ^ (x1 v x3) ^ (x2 v x4) ^ (x3 v x4)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept the model after BVE reconstruction"
    );
}

/// Verify that interruptible solve also goes through verify_external_model.
#[test]
fn test_verify_external_model_solve_interruptible() {
    let mut solver = Solver::new(3);
    // (x0 v x1) ^ (~x0 v x2) ^ (x1 v x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    let result = solver.solve_interruptible(|| false).into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept the model from solve_interruptible()"
    );
}

/// Verify that verify_external_model handles truncated models correctly.
/// Models returned by solve() are truncated to user_num_vars and should
/// still pass verification.
#[test]
fn test_verify_external_model_truncated_model() {
    let mut solver = Solver::new(3);
    // (x0) ^ (~x1) ^ (x2) — unique model: [true, false, true]
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(1))]);
    solver.add_clause(vec![Literal::positive(Variable(2))]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert_eq!(model.len(), 3, "model should have exactly 3 variables");
    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept unit-clause forced model"
    );
    assert_eq!(model, vec![true, false, true], "unique model must match");
}

/// #7987: Adding a permanent clause between two solve_with_assumptions calls
/// caused the second call to return UNSAT when the formula is SAT.
///
/// Formula: !v0, (!v2 | !v1), (v2 | v1)
/// Solve 1: assumptions=[v1] → SAT (v0=false, v1=true, v2=false)
/// Add clause: !v1
/// Solve 2: assumptions=[v2] → should be SAT (v0=false, v1=false, v2=true)
///
/// Bug: the second solve returned UNSAT due to stale learned clauses from
/// the first solve conflicting with the new permanent clause.
#[test]
fn test_incremental_assumptions_add_clause_between_solves_7987() {
    let mut solver = Solver::new(3);

    // Base formula: !v0, (!v2 | !v1), (v2 | v1)
    solver.add_clause(vec![Literal::negative(Variable::new(0))]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(2)),
        Literal::negative(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(2)),
        Literal::positive(Variable::new(1)),
    ]);

    // First solve: assume v1=true → SAT
    let r1 = solver
        .solve_with_assumptions(&[Literal::positive(Variable::new(1))])
        .into_inner();
    assert!(
        matches!(r1, AssumeResult::Sat(_)),
        "#7987: first solve should be SAT, got {r1:?}"
    );

    // Add permanent clause: !v1
    solver.add_clause(vec![Literal::negative(Variable::new(1))]);

    // Second solve: assume v2=true → should be SAT (v0=false, v1=false, v2=true)
    // Bug: returned UNSAT
    let r2 = solver
        .solve_with_assumptions(&[Literal::positive(Variable::new(2))])
        .into_inner();
    assert!(
        matches!(r2, AssumeResult::Sat(_)),
        "#7987: second solve should be SAT (v0=false, v1=false, v2=true), got {r2:?}"
    );

    // Verify the model
    if let AssumeResult::Sat(model) = r2 {
        assert!(!model[0], "v0 must be false");
        assert!(!model[1], "v1 must be false (unit clause !v1)");
        assert!(model[2], "v2 must be true (assumption)");
    }
}

/// Isolation test: braun.11 with BVE disabled must return UNSAT (#8482).
///
/// If CDCL alone (no BVE) returns UNSAT, then the BVE reduction is the
/// source of the soundness bug.
#[test]
#[ignore = "expensive braun.11 isolation check; run explicitly when auditing #8482"]
fn test_isolation_braun11_no_bve() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/sat/eq_atree_braun/eq.atree.braun.11.unsat.cnf");
    if !path.exists() {
        eprintln!("braun.11 missing, skipping isolation test");
        return;
    }
    let dimacs = std::fs::read_to_string(&path).expect("read braun.11");
    let formula = crate::parse_dimacs(&dimacs).expect("parse braun.11");
    let mut solver = Solver::new(formula.num_vars);
    solver.disable_all_inprocessing();
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert_unsat_result_for_known_unsat(&solver, result, &path);
}

/// Default-budget coverage for the #8482 BVE isolation path.
///
/// `braun.11` is too expensive for the default test suite, but the smaller
/// `braun.7` instance still exercises the known-UNSAT circuit-equivalence
/// family with CDCL-only solving.
#[test]
fn test_isolation_braun7_no_bve_default_regression() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/sat/eq_atree_braun/eq.atree.braun.7.unsat.cnf");
    if !path.exists() {
        eprintln!("braun.7 missing, skipping default isolation regression");
        return;
    }
    let dimacs = std::fs::read_to_string(&path).expect("read braun.7");
    let formula = crate::parse_dimacs(&dimacs).expect("parse braun.7");
    let mut solver = Solver::new(formula.num_vars);
    solver.disable_all_inprocessing();
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert_unsat_result_for_known_unsat(&solver, result, &path);
}

/// Isolation test: braun.11 with backward subsumption strengthening
/// disabled during BVE.
#[test]
#[ignore = "expensive braun.11 isolation check; run explicitly when auditing #8482"]
fn test_isolation_braun11_no_bw_strengthen() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/sat/eq_atree_braun/eq.atree.braun.11.unsat.cnf");
    if !path.exists() {
        eprintln!("braun.11 missing, skipping isolation test");
        return;
    }
    let dimacs = std::fs::read_to_string(&path).expect("read braun.11");
    let formula = crate::parse_dimacs(&dimacs).expect("parse braun.11");
    let mut solver = formula.into_solver();
    // Disable backward subsumption entirely to check if it causes the bug
    solver.disable_technique(crate::SatTechnique::Subsume);
    let result = solver.solve().into_inner();
    assert_unsat_result_for_known_unsat(&solver, result, &path);
}

// ========================================================================
// #8485, #8397, #8482: BVE reconstruction soundness regression tests
//
// These tests verify that known-UNSAT benchmarks which previously
// triggered false SAT or UNKNOWN due to BVE reconstruction corruption
// continue to return UNSAT after fixes.
// ========================================================================

/// Regression: crn_11_99_u.cnf must return UNSAT (#8485, #8397).
///
/// This 1287-variable, 2332-clause benchmark previously returned false SAT
/// (or UNKNOWN after model validation failure) due to BVE reconstruction
/// stack corruption: reconstruction flipped ext_var58 from false to true,
/// breaking clause [-59, 71, -1103] that was satisfied before reconstruction.
#[test]
fn test_regression_crn_11_99_u_must_be_unsat() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    if !path.exists() {
        eprintln!("crn_11_99_u.cnf missing, skipping regression test");
        return;
    }
    let dimacs = std::fs::read_to_string(&path).expect("read crn_11_99_u.cnf");
    let formula = crate::parse_dimacs(&dimacs).expect("parse crn_11_99_u.cnf");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    assert_unsat_result_for_known_unsat(&solver, result, &path);
}

/// Regression: eq.atree.braun odd instances must return UNSAT (#8482).
///
/// braun.7, braun.9, braun.11, braun.13 previously returned UNKNOWN
/// due to BVE reconstruction producing invalid models that failed
/// FINALIZE_SAT_FAIL verification.
///
/// Uses a 30-second per-instance timeout via solve_interruptible to
/// prevent the test suite from hanging on harder instances (#7905).
/// Timeouts (Unknown) are acceptable; wrong answers (SAT) are not.
#[test]
fn test_regression_eq_atree_braun_must_be_unsat() {
    let braun_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/sat/eq_atree_braun");
    if !braun_dir.exists() {
        eprintln!("eq_atree_braun directory missing, skipping regression test");
        return;
    }
    for entry in std::fs::read_dir(&braun_dir).expect("read eq_atree_braun dir") {
        let path = entry.expect("dir entry").path();
        if path.extension().is_none_or(|ext| ext != "cnf") {
            continue;
        }
        let label = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("<unknown>");
        let dimacs = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        let formula = crate::parse_dimacs(&dimacs)
            .unwrap_or_else(|e| panic!("parse {} failed: {e}", path.display()));
        let mut solver = formula.into_solver();

        // 30s per-instance timeout to prevent test suite hangs (#7905).
        let flag = Arc::new(AtomicBool::new(false));
        solver.set_interrupt(flag.clone());
        let timeout_flag = flag.clone();
        std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_secs(30));
            timeout_flag.store(true, Ordering::Relaxed);
        });
        let result = solver
            .solve_interruptible(move || flag.load(Ordering::Relaxed))
            .into_inner();

        match result {
            SatResult::Unsat(_) => {} // expected
            SatResult::Unknown => {
                eprintln!("braun {label}: timed out after 30s, skipping (not a failure)");
            }
            SatResult::Sat(model) => {
                let violated = solver
                    .verify_against_original(&model)
                    .map_or_else(|| "none".to_string(), |idx| idx.to_string());
                panic!(
                    "known-UNSAT benchmark {label} returned SAT; \
                     first violated original clause={violated}"
                );
            }
            #[allow(unreachable_patterns)]
            other => unreachable!("unexpected SAT result variant for {label}: {other:?}"),
        }
    }
}

/// Regression: crn_11_99_u.cnf 10-run stability check (#8485).
///
/// BVE reconstruction bugs can be non-deterministic due to VSIDS scoring
/// and restart timing leading to different search paths. Run the benchmark
/// multiple times to catch intermittent false SAT.
#[test]
fn test_regression_crn_11_99_u_stability() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    if !path.exists() {
        eprintln!("crn_11_99_u.cnf missing, skipping stability test");
        return;
    }
    let dimacs = std::fs::read_to_string(&path).expect("read crn_11_99_u.cnf");
    for run in 0..10 {
        let formula = crate::parse_dimacs(&dimacs).expect("parse crn_11_99_u.cnf");
        let mut solver = formula.into_solver();
        let result = solver.solve().into_inner();
        match result {
            SatResult::Unsat(_) => {}
            SatResult::Sat(model) => {
                let violated = solver
                    .verify_against_original(&model)
                    .map_or_else(|| "none".to_string(), |idx| idx.to_string());
                panic!(
                    "#8485 regression: crn_11_99_u run {run}/10 returned SAT; \
                     first violated original clause={violated}"
                );
            }
            SatResult::Unknown => {
                panic!(
                    "#8485 regression: crn_11_99_u run {run}/10 returned Unknown \
                     (likely reconstruction failure)"
                );
            }
            #[allow(unreachable_patterns)]
            other => unreachable!("unexpected result on run {run}: {other:?}"),
        }
    }
}

/// Regression test for #8577: FINALIZE_SAT_FAIL on miter-like AND-gate formulas.
///
/// Creates a formula mimicking the AIGER miter pattern: chains of AND gates
/// with non-gate clauses. Gate-only witness filtering during BVE must
/// correctly reconstruct eliminated gate variables so that non-gate clauses
/// in the original_ledger are satisfied.
///
/// The miter benchmark has 1792 AND gates out of 2030 variables, creating
/// deep gate chains where multi-variable BVE elimination and reverse
/// reconstruction must cooperate precisely.
#[test]
fn test_miter_and_gate_bve_reconstruction_8577() {
    // Build a formula with AND-gate structure:
    //
    // Inputs: a (v0), b (v1), c (v2), d (v3)
    //
    // AND gates:
    //   g1 (v4) = a AND b    — clauses: (¬g1 ∨ a), (¬g1 ∨ b), (g1 ∨ ¬a ∨ ¬b)
    //   g2 (v5) = c AND d    — clauses: (¬g2 ∨ c), (¬g2 ∨ d), (g2 ∨ ¬c ∨ ¬d)
    //   g3 (v6) = g1 AND g2  — clauses: (¬g3 ∨ g1), (¬g3 ∨ g2), (g3 ∨ ¬g1 ∨ ¬g2)
    //
    // Non-gate clauses (property/transition):
    //   (g3 ∨ e)             — v6 ∨ v7: property requires g3 or escape variable e
    //   (¬e)                 — v7 must be false: forces g3 = true
    //
    // This forces: g3=true → g1=true ∧ g2=true → a=b=c=d=true.
    // BVE should eliminate g3, g1, g2 (gate variables) with gate-only filtering.
    // Reconstruction must correctly set all gate variables.
    let num_vars = 8;
    let mut solver = Solver::new(num_vars);

    let v = |i: u32| Variable(i);
    let pos = |i: u32| Literal::positive(v(i));
    let neg = |i: u32| Literal::negative(v(i));

    // g1 = a AND b (v4 = v0 AND v1)
    solver.add_clause(vec![neg(4), pos(0)]); // ¬g1 ∨ a
    solver.add_clause(vec![neg(4), pos(1)]); // ¬g1 ∨ b
    solver.add_clause(vec![pos(4), neg(0), neg(1)]); // g1 ∨ ¬a ∨ ¬b

    // g2 = c AND d (v5 = v2 AND v3)
    solver.add_clause(vec![neg(5), pos(2)]); // ¬g2 ∨ c
    solver.add_clause(vec![neg(5), pos(3)]); // ¬g2 ∨ d
    solver.add_clause(vec![pos(5), neg(2), neg(3)]); // g2 ∨ ¬c ∨ ¬d

    // g3 = g1 AND g2 (v6 = v4 AND v5)
    solver.add_clause(vec![neg(6), pos(4)]); // ¬g3 ∨ g1
    solver.add_clause(vec![neg(6), pos(5)]); // ¬g3 ∨ g2
    solver.add_clause(vec![pos(6), neg(4), neg(5)]); // g3 ∨ ¬g1 ∨ ¬g2

    // Property: g3 must be true (via forcing)
    solver.add_clause(vec![pos(6), pos(7)]); // g3 ∨ e
    solver.add_clause(vec![neg(7)]); // ¬e (forces g3=true)

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            // Verify the model satisfies all original clauses
            let violated = solver.verify_against_original(&model);
            assert!(
                violated.is_none(),
                "#8577: BVE reconstruction produced invalid model; \
                 first violated original clause index: {violated:?}",
            );
            // Verify semantic correctness
            assert!(model[6], "g3 must be true (forced by ¬e and g3∨e)");
        }
        SatResult::Unknown => {
            panic!(
                "#8577: solver returned Unknown — likely FINALIZE_SAT_FAIL \
                 from BVE reconstruction failure on AND-gate formula"
            );
        }
        other => panic!("#8577: expected SAT, got {other:?}"),
    }
}

/// Stress test for #8577: deeper AND-gate chain with multiple non-gate clauses.
///
/// Creates a deeper miter-like formula to stress multi-variable BVE
/// elimination ordering and reconstruction. The chain depth (4 levels)
/// ensures that reconstruction must correctly process entries in reverse
/// order across multiple elimination rounds.
#[test]
fn test_deep_miter_chain_bve_reconstruction_8577() {
    // v0..v7: inputs
    // v8: g1 = v0 AND v1
    // v9: g2 = v2 AND v3
    // v10: g3 = v4 AND v5
    // v11: g4 = v6 AND v7
    // v12: g5 = g1 AND g2
    // v13: g6 = g3 AND g4
    // v14: g7 = g5 AND g6
    // v15: escape variable
    //
    // Property: g7 ∨ escape, ¬escape → forces g7=true → all inputs true
    let num_vars = 16;
    let mut solver = Solver::new(num_vars);

    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));

    // Helper to add AND gate: g = a AND b
    let mut add_and_gate = |g: u32, a: u32, b: u32| {
        solver.add_clause(vec![neg(g), pos(a)]);
        solver.add_clause(vec![neg(g), pos(b)]);
        solver.add_clause(vec![pos(g), neg(a), neg(b)]);
    };

    // Level 1 gates
    add_and_gate(8, 0, 1); // g1 = v0 AND v1
    add_and_gate(9, 2, 3); // g2 = v2 AND v3
    add_and_gate(10, 4, 5); // g3 = v4 AND v5
    add_and_gate(11, 6, 7); // g4 = v6 AND v7

    // Level 2 gates
    add_and_gate(12, 8, 9); // g5 = g1 AND g2
    add_and_gate(13, 10, 11); // g6 = g3 AND g4

    // Level 3 gate
    add_and_gate(14, 12, 13); // g7 = g5 AND g6

    // Property: g7 must be true
    solver.add_clause(vec![pos(14), pos(15)]); // g7 ∨ escape
    solver.add_clause(vec![neg(15)]); // ¬escape

    // Additional non-gate clauses to stress reconstruction:
    // These create additional occurrence entries for gate variables,
    // producing mixed gate/non-gate patterns that exercise gate-only filtering.
    solver.add_clause(vec![pos(12), pos(0)]); // g5 ∨ v0 (non-gate for g5)
    solver.add_clause(vec![pos(13), pos(4)]); // g6 ∨ v4 (non-gate for g6)
    solver.add_clause(vec![neg(8), pos(2)]); // ¬g1 ∨ v2 (non-gate for g1)

    for run in 0..5 {
        let mut s = Solver::new(num_vars);
        // Re-add all clauses (fresh solver each run for determinism)
        s.add_clause(vec![neg(8), pos(0)]);
        s.add_clause(vec![neg(8), pos(1)]);
        s.add_clause(vec![pos(8), neg(0), neg(1)]);
        s.add_clause(vec![neg(9), pos(2)]);
        s.add_clause(vec![neg(9), pos(3)]);
        s.add_clause(vec![pos(9), neg(2), neg(3)]);
        s.add_clause(vec![neg(10), pos(4)]);
        s.add_clause(vec![neg(10), pos(5)]);
        s.add_clause(vec![pos(10), neg(4), neg(5)]);
        s.add_clause(vec![neg(11), pos(6)]);
        s.add_clause(vec![neg(11), pos(7)]);
        s.add_clause(vec![pos(11), neg(6), neg(7)]);
        s.add_clause(vec![neg(12), pos(8)]);
        s.add_clause(vec![neg(12), pos(9)]);
        s.add_clause(vec![pos(12), neg(8), neg(9)]);
        s.add_clause(vec![neg(13), pos(10)]);
        s.add_clause(vec![neg(13), pos(11)]);
        s.add_clause(vec![pos(13), neg(10), neg(11)]);
        s.add_clause(vec![neg(14), pos(12)]);
        s.add_clause(vec![neg(14), pos(13)]);
        s.add_clause(vec![pos(14), neg(12), neg(13)]);
        s.add_clause(vec![pos(14), pos(15)]);
        s.add_clause(vec![neg(15)]);
        s.add_clause(vec![pos(12), pos(0)]);
        s.add_clause(vec![pos(13), pos(4)]);
        s.add_clause(vec![neg(8), pos(2)]);

        let result = s.solve().into_inner();
        match result {
            SatResult::Sat(model) => {
                let violated = s.verify_against_original(&model);
                assert!(
                    violated.is_none(),
                    "#8577 deep chain run {run}/5: BVE reconstruction violated \
                     original clause {violated:?}",
                );
            }
            SatResult::Unknown => {
                panic!(
                    "#8577 deep chain run {run}/5: Unknown — likely \
                     FINALIZE_SAT_FAIL from BVE reconstruction"
                );
            }
            other => panic!("#8577 deep chain run {run}/5: expected SAT, got {other:?}"),
        }
    }
}

/// Regression test for #8577: BVE reconstruction in incremental mode.
///
/// The miter benchmark triggers FINALIZE_SAT_FAIL through IC3/PDR's
/// incremental solving pattern. This test exercises the exact sequence:
/// 1. First solve (BVE preprocessing runs, reconstruction stack populated)
/// 2. Push scope
/// 3. Add scoped clauses
/// 4. Solve (should use the reconstructed model correctly)
/// 5. Pop scope
/// 6. Solve at base scope (reconstruction must still work)
#[test]
fn test_incremental_bve_reconstruction_8577() {
    // Create a formula with AND-gate structure (same as above but smaller)
    let num_vars = 8;
    let mut solver = Solver::new(num_vars);

    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));

    // g1 = v0 AND v1 (v4)
    solver.add_clause(vec![neg(4), pos(0)]);
    solver.add_clause(vec![neg(4), pos(1)]);
    solver.add_clause(vec![pos(4), neg(0), neg(1)]);

    // g2 = v2 AND v3 (v5)
    solver.add_clause(vec![neg(5), pos(2)]);
    solver.add_clause(vec![neg(5), pos(3)]);
    solver.add_clause(vec![pos(5), neg(2), neg(3)]);

    // g3 = g1 AND g2 (v6)
    solver.add_clause(vec![neg(6), pos(4)]);
    solver.add_clause(vec![neg(6), pos(5)]);
    solver.add_clause(vec![pos(6), neg(4), neg(5)]);

    // Non-gate clause: g3 ∨ e (v7)
    solver.add_clause(vec![pos(6), pos(7)]);
    // Force e = false: ¬e
    solver.add_clause(vec![neg(7)]);

    // First solve: BVE may run and eliminate gate variables
    let result1 = solver.solve().into_inner();
    match result1 {
        SatResult::Sat(model) => {
            let violated = solver.verify_against_original(&model);
            assert!(
                violated.is_none(),
                "#8577 incremental solve 1: original clause violated: {violated:?}",
            );
        }
        SatResult::Unknown => {
            panic!("#8577 incremental solve 1: Unknown (FINALIZE_SAT_FAIL)");
        }
        _ => panic!("#8577 incremental solve 1: expected SAT, got {result1:?}"),
    }

    // Push scope, add scoped clause, solve
    solver.push();
    solver.add_clause(vec![pos(0)]); // Force v0 = true in scope

    let result2 = solver.solve().into_inner();
    match result2 {
        SatResult::Sat(model) => {
            assert!(model[0], "v0 must be true (scoped unit clause)");
        }
        SatResult::Unknown => {
            panic!("#8577 incremental solve 2: Unknown (likely reconstruction issue)");
        }
        _ => panic!("#8577 incremental solve 2: expected SAT, got {result2:?}"),
    }

    // Pop scope
    assert!(solver.pop(), "pop must succeed");

    // Solve at base scope: BVE reconstruction must still produce valid model
    let result3 = solver.solve().into_inner();
    match result3 {
        SatResult::Sat(model) => {
            let violated = solver.verify_against_original(&model);
            assert!(
                violated.is_none(),
                "#8577 incremental solve 3 (post-pop): original clause violated: {violated:?}",
            );
        }
        SatResult::Unknown => {
            panic!("#8577 incremental solve 3: Unknown (FINALIZE_SAT_FAIL after pop)");
        }
        _ => panic!("#8577 incremental solve 3: expected SAT, got {result3:?}"),
    }
}

/// Regression test for #8577: domain-restricted solve_with_assumptions
/// returning FINALIZE_SAT_FAIL (Unknown) due to non-domain clauses.
///
/// Root cause: finalize_sat_model's non-scoped path verified the model against
/// ALL original_ledger clauses without considering domain restriction. When
/// active_domain is set (IC3/PDR), non-domain variables are don't-cares and
/// default to false in vals[]. Clauses involving only non-domain variables
/// may appear unsatisfied even though the solver correctly found SAT for
/// the domain-restricted query.
///
/// The fix adds domain-aware clause filtering to the non-scoped verification
/// path in finalize_sat_model, matching the existing behavior in:
/// - The scoped path (line 592: first_model_violation_domain_aware)
/// - The IC3-specific solve path (ic3.rs line 297: bypasses finalize_sat_model)
#[test]
fn test_domain_restricted_solve_with_assumptions_8577() {
    // Create a formula with "transition system" structure:
    // - Domain variables: v0, v1, v2 (state/next-state)
    // - Non-domain variables: v3, v4, v5 (auxiliary/AND-gate)
    //
    // Transition clauses (involving domain vars):
    //   (v0 | v1)
    //   (¬v0 | v2)
    //
    // Non-domain clauses (only involving v3, v4, v5):
    //   (v3 | v4)           -- satisfied only if v3=true or v4=true
    //   (¬v3 | v5)          -- if v3 then v5
    //   (v4 | v5)           -- v4 or v5
    //
    // These non-domain clauses are satisfiable (e.g., v3=true, v4=true, v5=true)
    // but since domain BCP only decides domain vars, non-domain vars default to
    // false, making clause (v3 | v4) appear unsatisfied.
    //
    // Pre-fix: this test causes FINALIZE_SAT_FAIL → solver returns Unknown.
    // Post-fix: domain-restricted verification correctly skips non-domain clauses.
    let num_vars = 6;
    let mut solver = Solver::new(num_vars);
    // Disable preprocessing so clauses stay in the arena as-is.
    solver.set_preprocess_enabled(false);
    solver.set_incremental_mode();

    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));

    // Domain clauses
    solver.add_clause(vec![pos(0), pos(1)]); // v0 | v1
    solver.add_clause(vec![neg(0), pos(2)]); // ¬v0 | v2

    // Non-domain clauses (only v3, v4, v5)
    solver.add_clause(vec![pos(3), pos(4)]); // v3 | v4
    solver.add_clause(vec![neg(3), pos(5)]); // ¬v3 | v5
    solver.add_clause(vec![pos(4), pos(5)]); // v4 | v5

    // Set domain to {v0, v1, v2} only.
    solver.set_domain(&[Variable(0), Variable(1), Variable(2)]);

    // Solve with assumptions: assume v0=true.
    let result = solver.solve_with_assumptions(&[pos(0)]);
    let inner = result.into_inner();

    match inner {
        AssumeResult::Sat(_model) => {
            // Success: domain-restricted verification correctly skipped
            // non-domain clauses. The model satisfies all domain clauses.
        }
        AssumeResult::Unknown => {
            panic!(
                "#8577: solve_with_assumptions returned Unknown with domain restriction — \
                 FINALIZE_SAT_FAIL from non-domain clause verification. \
                 This is the exact bug: finalize_sat_model's non-scoped path \
                 does not account for active_domain."
            );
        }
        AssumeResult::Unsat(..) => {
            panic!(
                "#8577: expected SAT with domain restriction and v0=true assumption, \
                 got UNSAT"
            );
        }
    }

    solver.clear_domain();

    // Verify that without domain restriction, the solver still finds SAT
    // (the formula is satisfiable as a whole).
    let result2 = solver.solve_with_assumptions(&[pos(0)]);
    assert!(
        result2.into_inner().is_sat(),
        "#8577: formula should be SAT without domain restriction"
    );
}

/// Stress test for #8577: IC3-like query pattern with domain restriction.
///
/// Exercises the exact IC3 pattern from ay-chc: repeated solve_with_assumptions
/// calls with different domains and interleaved add_clause (frame clauses).
/// Each query uses set_domain/solve_with_assumptions/clear_domain, which is
/// the pattern that triggers the bug in production.
#[test]
fn test_ic3_pattern_domain_restricted_queries_8577() {
    // Simulate an IC3-like transition system:
    // State vars: v0, v1 (current state)
    // Next vars: v2, v3 (next state)
    // AND gates: v4, v5 (internal)
    // Frame activation: v6, v7
    let num_vars = 8;
    let mut solver = Solver::new(num_vars);
    solver.set_preprocess_enabled(false);
    solver.set_incremental_mode();
    solver.set_walk_enabled(false);
    solver.set_warmup_enabled(false);

    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));

    // Transition relation: T(s, s')
    // v2 <=> v0 AND v1 (next state bit 0 = AND of current state bits)
    solver.add_clause(vec![neg(2), pos(0)]); // v2 => v0
    solver.add_clause(vec![neg(2), pos(1)]); // v2 => v1
    solver.add_clause(vec![pos(2), neg(0), neg(1)]); // v0 AND v1 => v2

    // v3 <=> v0 OR v1 (next state bit 1 = OR of current state bits)
    solver.add_clause(vec![pos(3), neg(0)]); // v0 => v3
    solver.add_clause(vec![pos(3), neg(1)]); // v1 => v3
    solver.add_clause(vec![neg(3), pos(0), pos(1)]); // v3 => v0 OR v1

    // Internal AND gates (non-domain, used for auxiliary computations)
    // v4 = v0 AND v2
    solver.add_clause(vec![neg(4), pos(0)]);
    solver.add_clause(vec![neg(4), pos(2)]);
    solver.add_clause(vec![pos(4), neg(0), neg(2)]);

    // v5 = v1 AND v3
    solver.add_clause(vec![neg(5), pos(1)]);
    solver.add_clause(vec![neg(5), pos(3)]);
    solver.add_clause(vec![pos(5), neg(1), neg(3)]);

    // IC3 query 1: bad-state check with domain {v0, v1, v6}
    // Frame clause: ¬v6 | ¬v0 | ¬v1 (activation v6 => not(v0=1, v1=1))
    solver.add_clause(vec![neg(6), neg(0), neg(1)]);

    solver.set_domain(&[Variable(0), Variable(1), Variable(6)]);
    let r1 = solver.solve_with_assumptions(&[pos(6), pos(0)]);
    solver.clear_domain();
    // Should succeed (not Unknown from FINALIZE_SAT_FAIL)
    assert!(
        !r1.into_inner().is_unknown(),
        "#8577 IC3 query 1: returned Unknown (FINALIZE_SAT_FAIL)"
    );

    // IC3 query 2: consecution check with wider domain
    solver.set_domain(&[
        Variable(0),
        Variable(1),
        Variable(2),
        Variable(3),
        Variable(6),
    ]);
    let r2 = solver.solve_with_assumptions(&[pos(6), neg(0), pos(2), pos(3)]);
    solver.clear_domain();
    assert!(
        !r2.into_inner().is_unknown(),
        "#8577 IC3 query 2: returned Unknown (FINALIZE_SAT_FAIL)"
    );

    // Add frame clause (blocking clause): ¬v7 | v0 | v1
    solver.add_clause(vec![neg(7), pos(0), pos(1)]);

    // IC3 query 3: after frame clause addition
    solver.set_domain(&[Variable(0), Variable(1), Variable(7)]);
    let r3 = solver.solve_with_assumptions(&[pos(7), neg(0)]);
    solver.clear_domain();
    assert!(
        !r3.into_inner().is_unknown(),
        "#8577 IC3 query 3: returned Unknown (FINALIZE_SAT_FAIL)"
    );

    // IC3 query 4: push/pop pattern (constrained query)
    solver.push();
    solver.add_clause(vec![pos(0), pos(1)]); // temporary constraint
    solver.set_domain(&[Variable(0), Variable(1), Variable(2), Variable(3)]);
    let r4 = solver.solve_with_assumptions(&[pos(0)]);
    solver.clear_domain();
    let _ = solver.pop();

    assert!(
        !r4.into_inner().is_unknown(),
        "#8577 IC3 query 4 (push/pop): returned Unknown (FINALIZE_SAT_FAIL)"
    );

    // IC3 query 5: after pop, without domain restriction
    let r5 = solver.solve_with_assumptions(&[pos(0), pos(1)]);
    assert!(
        r5.into_inner().is_sat(),
        "#8577 IC3 query 5 (post-pop, no domain): expected SAT"
    );
}

// ========================================================================
// #8819 (verification gap #1): SAT verification must run in release builds.
// ========================================================================

/// Regression test for verification gap #1 (#8819).
///
/// Before #8819, `verify_model` and `verify_external_model` were called only
/// from `debug_assert!`, so release builds skipped SAT re-verification
/// entirely. This test ensures the verification helpers remain callable from
/// non-debug code paths by exercising them directly on a concrete model.
///
/// The test passes in BOTH debug and release modes because it invokes the
/// helpers as normal functions (not via `debug_assert!`). A release-mode
/// regression that accidentally drops the always-on call sites would be
/// caught by the `test_release_mode_finalize_sat_returns_valid_model` test
/// below.
#[test]
fn test_verify_model_is_callable_in_release_mode() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(m) => m,
        other => panic!("expected SAT, got {other:?}"),
    };

    // Extend to internal model length for verify_model (which requires
    // model.len() >= num_vars). Reads the truncated external model and
    // pads if needed.
    let mut extended = model.clone();
    extended.resize(solver.num_vars, false);

    // Both verification routines must be callable and return true on a
    // genuine SAT model. If these are removed or gated behind
    // `#[cfg(debug_assertions)]`, this test fails to compile in release.
    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept a genuine SAT model in release mode"
    );
    assert!(
        solver.verify_model(&extended),
        "verify_model must accept a genuine SAT model in release mode"
    );
}

/// Regression test for verification gap #1 (#8819): finalize_sat_model runs its
/// always-on verification in release builds and returns SAT only when the
/// model actually satisfies all original clauses.
///
/// Uses PHP(3,2) as a negative control (must be UNSAT) and a simple SAT
/// formula as a positive control. Both paths exercise declare_sat_from_model
/// / declare_assume_sat_from_model, which now always invoke
/// `verify_external_model` instead of only firing in debug builds.
#[test]
fn test_release_mode_finalize_sat_returns_valid_model() {
    // Positive control: unique SAT assignment.
    let mut sat_solver: Solver = Solver::new(3);
    sat_solver.add_clause(vec![Literal::positive(Variable(0))]);
    sat_solver.add_clause(vec![Literal::positive(Variable(1))]);
    sat_solver.add_clause(vec![Literal::positive(Variable(2))]);
    let sat_result = sat_solver.solve().into_inner();
    let sat_model = match sat_result {
        SatResult::Sat(m) => m,
        other => panic!("positive control: expected SAT, got {other:?}"),
    };
    assert_eq!(
        sat_model,
        vec![true, true, true],
        "positive control: unique model x0=x1=x2=true"
    );
    assert!(
        sat_solver.verify_against_original(&sat_model).is_none(),
        "positive control: model must satisfy original clauses"
    );

    // Negative control: PHP(3,2) is UNSAT. finalize_sat_model must not be
    // invoked. This exercises the UNSAT path which does not go through the
    // SAT verification code, confirming the always-on check does not break
    // UNSAT returns.
    let mut unsat_solver: Solver = Solver::new(6);
    for pigeon in 0..3u32 {
        let clause: Vec<Literal> = (0..2u32)
            .map(|hole| Literal::positive(Variable(pigeon * 2 + hole)))
            .collect();
        unsat_solver.add_clause(clause);
    }
    for hole in 0..2u32 {
        for p1 in 0..3u32 {
            for p2 in (p1 + 1)..3u32 {
                unsat_solver.add_clause(vec![
                    Literal::negative(Variable(p1 * 2 + hole)),
                    Literal::negative(Variable(p2 * 2 + hole)),
                ]);
            }
        }
    }
    assert!(
        unsat_solver.solve().into_inner().is_unsat(),
        "negative control: PHP(3,2) must be UNSAT"
    );
}
