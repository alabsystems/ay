// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{AssumeResult, Literal, SatResult, Solver, Variable};
use ntest::timeout;

/// Verify that a model satisfies all clauses in the formula.
fn verify_model(clauses: &[Vec<Literal>], model: &[bool]) {
    for (i, clause) in clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|&lit| {
            let val = model[lit.variable().index()];
            if lit.is_positive() {
                val
            } else {
                !val
            }
        });
        assert!(satisfied, "Model violates clause {i}: {clause:?}");
    }
}

/// Regression for incremental UNSAT latch: popping a scoped contradiction must
/// clear root-level UNSAT state.
#[test]
#[timeout(10_000)]
fn test_unsat_latch_cleared_after_pop() {
    let mut solver = Solver::new(2);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);

    // Base formula is SAT.
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "Base formula should be SAT"
    );

    solver.push();
    // Scoped contradiction via conflicting units.
    solver.add_clause(vec![Literal::positive(x0)]);
    solver.add_clause(vec![Literal::negative(x0)]);
    assert!(
        solver.solve().into_inner().is_unsat(),
        "Scoped contradiction should be UNSAT"
    );

    assert!(solver.pop(), "Pop should succeed");
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "After pop, solver must return SAT for base formula"
    );
}

/// Regression for multi-solve without push/pop: calling solve() twice must
/// produce sound results. The first solve may trigger inprocessing (BVE,
/// conditioning, etc.) which eliminates clauses. reset_search_state() restores
/// them. The second solve should produce a correct model. (#5031)
#[test]
#[timeout(30_000)]
fn test_multi_solve_without_push_pop() {
    let mut solver = Solver::new(4);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);
    let x3 = Variable::new(3);

    // Formula: (x0 | x1) & (x2 | x3) & (!x0 | x2) & (!x1 | x3)
    let clauses = vec![
        vec![Literal::positive(x0), Literal::positive(x1)],
        vec![Literal::positive(x2), Literal::positive(x3)],
        vec![Literal::negative(x0), Literal::positive(x2)],
        vec![Literal::negative(x1), Literal::positive(x3)],
    ];
    for c in &clauses {
        solver.add_clause(c.clone());
    }

    // First solve — may trigger conditioning/BVE/decompose
    let r1 = solver.solve().into_inner();
    match &r1 {
        SatResult::Sat(model) => verify_model(&clauses, model),
        _ => panic!("First solve should be SAT, got {r1:?}"),
    }

    // Second solve without push/pop — should still produce correct result
    let r2 = solver.solve().into_inner();
    match &r2 {
        SatResult::Sat(model) => verify_model(&clauses, model),
        _ => panic!("Second solve should be SAT, got {r2:?}"),
    }
}

/// Multi-solve with decompose + gate + congruence: these inprocessing passes
/// modify the clause database more aggressively. The second solve must still
/// produce sound results after reset_search_state restores the formula. (#5031)
#[test]
#[timeout(30_000)]
fn test_multi_solve_with_decompose_gate_congruence() {
    let mut solver = Solver::new(4);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);
    let x3 = Variable::new(3);

    // Enable decompose, gate, congruence — these are the passes that
    // caused panics on second solve in #5031.
    solver.set_decompose_enabled(true);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);

    // AND-gate formula: x2 = (x0 & x1), with implications
    // (x0 | !x2) & (x1 | !x2) & (!x0 | !x1 | x2) & (x2 | x3)
    let clauses = vec![
        vec![Literal::positive(x0), Literal::negative(x2)],
        vec![Literal::positive(x1), Literal::negative(x2)],
        vec![
            Literal::negative(x0),
            Literal::negative(x1),
            Literal::positive(x2),
        ],
        vec![Literal::positive(x2), Literal::positive(x3)],
    ];
    for c in &clauses {
        solver.add_clause(c.clone());
    }

    let r1 = solver.solve().into_inner();
    match &r1 {
        SatResult::Sat(model) => verify_model(&clauses, model),
        _ => panic!("First solve should be SAT, got {r1:?}"),
    }

    // Second solve: has_solved_once disables destructive inprocessing,
    // reset_search_state restores eliminated clauses.
    let r2 = solver.solve().into_inner();
    match &r2 {
        SatResult::Sat(model) => verify_model(&clauses, model),
        _ => panic!("Second solve should be SAT, got {r2:?}"),
    }
}

/// Regression for conditioning-before-push: base clauses eliminated by
/// conditioning in the first solve must be restored when push() enters
/// incremental mode. Without restoration, the scoped solve sees only
/// scoped clauses and produces a model that violates the base formula.
/// Reference: the development design notes
#[test]
#[timeout(30_000)]
fn test_incremental_conditioning_restoration() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    // Add clauses that conditioning may eliminate.
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(x2)]);

    // First solve triggers conditioning (may eliminate base clauses).
    let r1 = solver.solve().into_inner();
    assert!(r1.is_sat(), "Base formula should be SAT");

    // Push: should restore eliminated clauses and enter incremental mode.
    solver.push();

    // Add scoped constraints that conflict with base formula.
    solver.add_clause(vec![Literal::negative(x0)]);
    solver.add_clause(vec![Literal::negative(x1)]);
    solver.add_clause(vec![Literal::negative(x2)]);

    // Should be UNSAT: base clauses (x0|x1), (x1|x2) + scoped (!x0, !x1, !x2).
    let r2 = solver.solve().into_inner();
    assert!(r2.is_unsat(), "Base clauses must be active under scope");

    // Pop and verify SAT.
    assert!(solver.pop(), "Pop should succeed");
    let r3 = solver.solve().into_inner();
    assert!(r3.is_sat(), "After pop, base formula is SAT");
}

/// Regression: SAT solver preprocessing (BVE/subsumption) can eliminate clauses
/// that are required for assumption-based solving, causing false UNSAT.
///
/// The fix for IncrementalPdrContext (#8822) is to disable preprocessing before
/// the first assumption-based solve. This test verifies that assumption solving
/// is correct when preprocessing is disabled.
#[test]
#[timeout(10_000)]
fn test_incremental_assume_sat_no_preprocess() {
    let mut solver = Solver::new(5);
    solver.set_preprocess_enabled(false);

    // Two binary clauses (mimicking PDR activation literals):
    solver.add_clause_global(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(0)),
    ]);
    solver.add_clause_global(vec![
        Literal::positive(Variable::new(3)),
        Literal::positive(Variable::new(2)),
    ]);

    // Assumptions that force unit propagation through the binary clauses.
    let assumptions = vec![
        Literal::positive(Variable::new(4)),
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new(2)),
    ];

    let result = solver.solve_with_assumptions_interruptible(&assumptions, || false);
    assert!(
        !result.result().is_unsat(),
        "Trivially SAT formula must not return UNSAT; got: {:?}",
        result.result(),
    );
}

/// Regression for #7987: incremental solve_with_assumptions returns wrong UNSAT.
///
/// After a SAT result with assumption v1=true, adding a permanent clause !v1,
/// then solving with assumption v2=true should be SAT (v1=false, v2=true
/// satisfies all clauses). The bug: preprocessing added derived irredundant
/// clauses that preserve equisatisfiability but not logical equivalence.
/// These clauses persisted across incremental solves because reset_search_state
/// only rebuilt the arena when original clauses were *deleted* (active < ledger),
/// not when derived irredundant clauses were *added* (active > ledger). The
/// derived clauses excluded models that were valid for the original formula,
/// causing spurious UNSAT when new clauses made those excluded models the only
/// satisfying assignments.
#[test]
#[timeout(10_000)]
fn test_incremental_assumption_add_clause_between_solves() {
    let mut s = Solver::new(3);
    let v0 = Variable::new(0);
    let v1 = Variable::new(1);
    let v2 = Variable::new(2);

    s.add_clause(vec![Literal::negative(v0)]); // v0=false
                                               // v2 <=> !v1
    s.add_clause(vec![Literal::negative(v2), Literal::negative(v1)]);
    s.add_clause(vec![Literal::positive(v2), Literal::positive(v1)]);

    // First solve: v1=true? -> SAT
    let r1 = s.solve_with_assumptions(&[Literal::positive(v1)]);
    assert!(
        r1.result().is_sat(),
        "First solve with v1=true should be SAT, got {:?}",
        r1.result()
    );

    // Add permanent clause: !v1
    s.add_clause(vec![Literal::negative(v1)]);

    // Before second solve: check if has_empty_clause is stale
    assert!(
        !s.has_empty_clause(),
        "has_empty_clause must be false before second solve"
    );

    // Second solve: v2=true? -> should be SAT (v0=false, v1=false, v2=true)
    let r2 = s.solve_with_assumptions(&[Literal::positive(v2)]);
    assert!(
        r2.result().is_sat(),
        "Second solve with v2=true should be SAT after adding !v1, got {:?}",
        r2.result()
    );

    // Verify the model is correct
    if let AssumeResult::Sat(model) = r2.into_inner() {
        assert!(!model[0], "v0 should be false");
        assert!(!model[1], "v1 should be false");
        assert!(model[2], "v2 should be true");
    }
}
