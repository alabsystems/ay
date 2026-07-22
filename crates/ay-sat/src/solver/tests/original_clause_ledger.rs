// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the immutable original clause ledger.

use super::*;

#[test]
fn test_decompose_keeps_original_clause_ledger_immutable() {
    let mut solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    // x0 <-> x1 via binary implications. Decompose should rewrite the working
    // clause DB around this equivalence, but `original_clauses` must stay in
    // the user-visible variable space.
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::negative(x1), Literal::positive(x0)]);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x2)]);
    solver.initialize_watches();

    let original_before = solver.cold.original_ledger.to_vec_of_vecs();
    let reconstruction_before = solver.inproc.reconstruction.len();

    solver.decompose();

    assert_eq!(
        solver.cold.original_ledger.to_vec_of_vecs(),
        original_before,
        "decompose must not rewrite original_ledger"
    );
    assert!(
        solver.inproc.reconstruction.len() > reconstruction_before,
        "decompose should still record equivalence reconstruction entries"
    );
}

/// Regression test for #8472: OriginalLedger must shrink after pop().
///
/// Clauses added inside a push/pop scope should be removed from the ledger
/// when pop() is called. Without this fix, the ledger grows monotonically
/// and wastes memory proportional to all clauses ever added across scopes.
#[test]
fn test_original_ledger_shrinks_after_pop() {
    let mut solver = Solver::new(4);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let x3 = Variable(3);

    // Add base clauses (outside any scope).
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x2)]);

    let base_count = solver.cold.original_ledger.num_clauses();
    assert_eq!(base_count, 2, "two base clauses in ledger");

    // Push scope and add scoped clauses.
    solver.push();
    solver.add_clause(vec![Literal::positive(x2), Literal::positive(x3)]);
    solver.add_clause(vec![Literal::negative(x1), Literal::negative(x3)]);

    let scoped_count = solver.cold.original_ledger.num_clauses();
    assert!(
        scoped_count > base_count,
        "ledger should grow inside scope: {scoped_count} > {base_count}"
    );

    // Pop scope — ledger must shrink back to base count.
    assert!(solver.pop(), "pop should succeed");

    let after_pop_count = solver.cold.original_ledger.num_clauses();
    assert_eq!(
        after_pop_count, base_count,
        "ledger must shrink to base count after pop: got {after_pop_count}, expected {base_count}"
    );

    // Verify base clauses are still intact.
    let base_clauses = solver.cold.original_ledger.to_vec_of_vecs();
    assert_eq!(base_clauses.len(), 2);
    assert!(base_clauses[0].contains(&Literal::positive(x0)));
    assert!(base_clauses[1].contains(&Literal::negative(x0)));
}

/// Test nested push/pop scopes truncate the ledger correctly (#8472).
#[test]
fn test_original_ledger_nested_scopes_truncate() {
    let mut solver = Solver::new(5);
    let vars: Vec<Variable> = (0..5).map(Variable).collect();

    // Base clause.
    solver.add_clause(vec![Literal::positive(vars[0])]);
    let base_count = solver.cold.original_ledger.num_clauses();

    // Outer scope.
    solver.push();
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[2])]);
    let outer_scope_count = solver.cold.original_ledger.num_clauses();
    assert!(outer_scope_count > base_count);

    // Inner scope.
    solver.push();
    solver.add_clause(vec![Literal::positive(vars[3]), Literal::positive(vars[4])]);
    let inner_scope_count = solver.cold.original_ledger.num_clauses();
    assert!(inner_scope_count > outer_scope_count);

    // Pop inner — should revert to outer scope count.
    assert!(solver.pop());
    assert_eq!(
        solver.cold.original_ledger.num_clauses(),
        outer_scope_count,
        "pop inner scope must revert to outer scope ledger size"
    );

    // Pop outer — should revert to base count.
    assert!(solver.pop());
    assert_eq!(
        solver.cold.original_ledger.num_clauses(),
        base_count,
        "pop outer scope must revert to base ledger size"
    );
}

/// Test that repeated push/pop cycles don't leak ledger memory (#8472).
#[test]
fn test_original_ledger_repeated_push_pop_no_leak() {
    let mut solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);

    // Base clause.
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    let base_count = solver.cold.original_ledger.num_clauses();

    // Simulate IC3-style workload: many push/pop cycles adding scoped clauses.
    for _ in 0..100 {
        solver.push();
        solver.add_clause(vec![Literal::negative(x0), Literal::negative(x1)]);
        assert!(solver.pop());
    }

    // Ledger must be back to base count after all pops.
    assert_eq!(
        solver.cold.original_ledger.num_clauses(),
        base_count,
        "ledger must not grow after 100 push/pop cycles"
    );

    // incremental_original_boundary must be consistent.
    assert_eq!(
        solver.cold.incremental_original_boundary, base_count,
        "incremental_original_boundary must match ledger size"
    );
}

#[test]
fn test_ic3_scoped_ledger_rebuild_stays_bounded_after_pop() {
    let mut solver = Solver::new(8);
    solver.set_ic3_mode();

    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let x3 = Variable(3);
    let x4 = Variable(4);
    let x5 = Variable(5);
    let x6 = Variable(6);
    let x7 = Variable(7);

    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::positive(x3),
        Literal::positive(x4),
    ]);

    let mut base_ledger = solver.cold.original_ledger.to_vec_of_vecs();
    for clause in &mut base_ledger {
        clause.sort_by_key(|lit| lit.0);
    }
    let base_count = base_ledger.len();
    assert_eq!(base_count, 2);
    assert!(solver.solve_incremental_ic3(&[]).is_sat());

    for round in 0..12 {
        solver.push();
        let selector = *solver
            .cold
            .scope_selectors
            .last()
            .expect("push must allocate a scope selector");

        solver.add_clause(vec![Literal::positive(x5), Literal::negative(x6)]);
        solver.add_clause(vec![Literal::negative(x5), Literal::positive(x7)]);

        assert!(
            solver.cold.original_ledger.num_clauses() > base_count,
            "round {round}: scoped clauses must be present while scope is active"
        );
        assert!(
            solver
                .cold
                .original_ledger
                .iter_clauses()
                .any(|clause| clause.contains(&Literal::positive(selector))),
            "round {round}: scoped ledger entry must contain its selector"
        );
        assert!(
            solver.solve_incremental_ic3(&[]).is_sat(),
            "round {round}: scoped IC3 query should remain SAT"
        );

        assert!(solver.pop(), "round {round}: pop should succeed");
        assert_eq!(
            solver.cold.original_ledger.num_clauses(),
            base_count,
            "round {round}: pop must return the ledger to the base boundary"
        );
        assert_eq!(
            solver.cold.incremental_original_boundary, base_count,
            "round {round}: pop must keep the incremental boundary in sync"
        );

        // Exercise the rebuild path that exposed #8472: after pop(), the live
        // arena still has the selector unit until reset_search_state rebuilds
        // from the trimmed ledger.
        solver.cold.l0_gc_modified_clause_db = true;
        assert!(
            solver.solve_incremental_ic3(&[]).is_sat(),
            "round {round}: post-pop IC3 rebuild should remain SAT"
        );

        let active_originals: Vec<Vec<Literal>> = solver
            .arena
            .active_indices()
            .filter(|&idx| !solver.arena.is_learned(idx))
            .map(|idx| {
                let mut clause = solver.arena.literals(idx).to_vec();
                clause.sort_by_key(|lit| lit.0);
                clause
            })
            .collect();
        assert_eq!(
            active_originals, base_ledger,
            "round {round}: rebuild must not resurrect popped scoped clauses"
        );
        assert!(
            active_originals
                .iter()
                .all(|clause| clause.iter().all(|lit| {
                    !solver
                        .cold
                        .was_scope_selector
                        .get(lit.variable().index())
                        .copied()
                        .unwrap_or(false)
                })),
            "round {round}: rebuilt originals must not mention any popped scope selector"
        );
    }
}
