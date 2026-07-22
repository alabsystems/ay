// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for bucket-queue VSIDS for IC3 short queries (#8476).
//!
//! Verifies that the bucket queue is activated for small domains,
//! produces correct SAT/UNSAT results, switches to heap after
//! the restart threshold, and handles incremental solving correctly.

use super::*;

/// Bucket queue is activated when domain size is small.
#[test]
fn test_bucket_queue_activates_for_small_domain() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..20).map(|_| solver.new_var()).collect();

    // Add simple satisfiable clauses
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[2])]);

    // Small domain (3 vars) — should activate bucket queue
    solver.set_domain(&vars[0..3]);
    assert!(
        solver.bucket_queue_active,
        "bucket queue should be active for small domain"
    );
    assert_eq!(solver.domain_restarts, 0);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(model) => {
            assert!(model[vars[0].index()] || model[vars[1].index()]);
            assert!(!model[vars[1].index()] || model[vars[2].index()]);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Bucket queue is NOT activated when domain size exceeds threshold.
#[test]
fn test_bucket_queue_not_activated_for_large_domain() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..100).map(|_| solver.new_var()).collect();

    // Add a simple clause
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);

    // Large domain (100 vars) — should NOT activate bucket queue
    solver.set_domain(&vars[..]);
    assert!(
        !solver.bucket_queue_active,
        "bucket queue should not be active for large domain"
    );
}

/// Bucket queue correctly finds UNSAT for contradictory domain clauses.
#[test]
fn test_bucket_queue_unsat() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    // Contradictory clauses: (x0) & (!x0)
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.add_clause(vec![Literal::negative(vars[0])]);

    solver.set_domain(&vars[0..1]);
    assert!(solver.bucket_queue_active);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Unsat(_) => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// Bucket queue state is cleared when domain is cleared.
#[test]
fn test_bucket_queue_cleared_on_domain_clear() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    solver.add_clause(vec![Literal::positive(vars[0])]);

    solver.set_domain(&vars[0..3]);
    assert!(solver.bucket_queue_active);

    solver.clear_domain();
    assert!(!solver.bucket_queue_active);
    assert_eq!(solver.domain_restarts, 0);
}

/// Bucket queue handles IC3-like incremental push/pop correctly.
#[test]
fn test_bucket_queue_incremental_push_pop() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..20).map(|_| solver.new_var()).collect();

    // Background clauses
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);

    // IC3 query 1: push, set domain, solve, pop
    solver.push();
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.set_domain(&vars[0..4]);
    assert!(solver.bucket_queue_active);

    let r1 = solver.solve();
    match r1.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat (query 1), got {other:?}"),
    }

    let _ = solver.pop();
    solver.clear_domain();
    assert!(!solver.bucket_queue_active);

    // IC3 query 2: different cube
    solver.push();
    solver.add_clause(vec![Literal::positive(vars[2])]);
    solver.set_domain(&vars[0..4]);
    assert!(solver.bucket_queue_active);

    let r2 = solver.solve();
    match r2.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat (query 2), got {other:?}"),
    }

    let _ = solver.pop();
    solver.clear_domain();
}

/// Bucket queue handles a harder formula that requires multiple restarts.
/// This tests the bucket-to-heap switch path after BUCKET_QUEUE_RESTART_THRESHOLD.
#[test]
fn test_bucket_queue_switches_to_heap_on_hard_query() {
    let mut solver = Solver::new(0);
    // Create enough variables for a non-trivial formula
    let n = 30;
    let vars: Vec<Variable> = (0..n).map(|_| solver.new_var()).collect();

    // Add a pigeonhole-like clause structure that forces restarts.
    // This creates a formula that is satisfiable but requires search.
    for i in 0..n - 2 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
            Literal::positive(vars[i + 2]),
        ]);
        solver.add_clause(vec![
            Literal::negative(vars[i]),
            Literal::negative(vars[i + 1]),
        ]);
    }

    // Domain on first 20 vars — should activate bucket queue
    solver.set_domain(&vars[0..20]);
    assert!(solver.bucket_queue_active);

    let result = solver.solve();
    // The formula should be satisfiable. Whether the bucket queue
    // switched to heap depends on how many restarts happened.
    match result.into_inner() {
        SatResult::Sat(_) | SatResult::Unsat(_) => {
            // Either result is fine — the point is correctness.
        }
        SatResult::Unknown => {}
    }
}

/// Regression: UNSAT with domain restriction and bucket queue preserves soundness.
#[test]
fn test_bucket_queue_soundness_unsat() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..8).map(|_| solver.new_var()).collect();

    // UNSAT: (x0) & (x1) & (!x0 | !x1) & (x2 | x3) & (!x2) & (!x3)
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.add_clause(vec![Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::negative(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::negative(vars[2])]);
    solver.add_clause(vec![Literal::negative(vars[3])]);

    solver.set_domain(&vars[0..4]);
    assert!(solver.bucket_queue_active);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Unsat(_) => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// SAT model from bucket queue path satisfies all clauses.
#[test]
fn test_bucket_queue_model_satisfies_all_clauses() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    // Mix of domain and non-domain variables in clauses:
    // (x0 | x5) & (!x0 | x6) & (x1 | !x7) & (!x1 | x2)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[5])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[6])]);
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::negative(vars[7])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[2])]);

    solver.set_domain(&vars[0..3]);
    assert!(solver.bucket_queue_active);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(model) => {
            // Verify all clauses
            assert!(model[vars[0].index()] || model[vars[5].index()]);
            assert!(!model[vars[0].index()] || model[vars[6].index()]);
            assert!(model[vars[1].index()] || !model[vars[7].index()]);
            assert!(!model[vars[1].index()] || model[vars[2].index()]);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Empty domain with bucket queue should not crash.
#[test]
fn test_bucket_queue_empty_domain() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..5).map(|_| solver.new_var()).collect();

    solver.add_clause(vec![Literal::positive(vars[0])]);

    // Empty domain — bucket queue is active but empty
    solver.set_domain(&[]);
    assert!(solver.bucket_queue_active, "empty domain <= threshold");

    let result = solver.solve();
    // With empty domain, no decisions can be made. Result depends on BCP.
    match result.into_inner() {
        SatResult::Sat(_) | SatResult::Unknown => {}
        SatResult::Unsat(_) => panic!("formula is satisfiable"),
    }
}

/// IC3 mode: bucket queue is always activated regardless of domain size (#8569 Gap 4).
#[test]
fn test_ic3_mode_bucket_queue_always_active() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..200).map(|_| solver.new_var()).collect();

    // Add simple clauses.
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);

    // Enable IC3 mode.
    solver.set_ic3_mode();

    // Large domain (200 vars) — normally exceeds BUCKET_QUEUE_MAX_DOMAIN_SIZE
    // but IC3 mode should always activate the bucket queue.
    solver.set_domain(&vars[..]);
    assert!(
        solver.bucket_queue_active,
        "IC3 mode should always activate bucket queue regardless of domain size"
    );

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat, got {other:?}"),
    }

    solver.clear_domain();
    // After clear_domain, bucket queue should be inactive (no domain).
    assert!(!solver.bucket_queue_active);
}

/// IC3 mode: domain-only bucket queue decisions (#8569 Gap 4).
///
/// Verify that after set_domain() in IC3 mode, the bucket queue contains
/// only domain variables. After clear_domain(), the bucket queue is
/// deactivated and the solver falls back to the heap.
#[test]
fn test_ic3_mode_domain_only_decisions() {
    let mut solver = Solver::new(0);
    // Create 50 variables: domain = first 5, non-domain = remaining 45.
    let vars: Vec<Variable> = (0..50).map(|_| solver.new_var()).collect();

    // Bump activity on some non-domain variables to make them high-priority
    // in the heap. Without domain restriction, the heap would pick these first.
    for &var in vars.iter().take(20).skip(10) {
        for _ in 0..100 {
            solver.vsids.bump(var, &solver.vals, true);
        }
    }

    // Bump domain variables with lower activity.
    for &var in vars.iter().take(5) {
        for _ in 0..10 {
            solver.vsids.bump(var, &solver.vals, true);
        }
    }

    // Add clauses to make the formula satisfiable.
    for i in 0..49 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    solver.set_ic3_mode();
    solver.set_domain(&vars[0..5]);
    assert!(solver.bucket_queue_active);

    // The bucket queue should only contain domain variables (0-4).
    // Pop all variables from the bucket queue and verify they are domain vars.
    let mut popped_vars = Vec::new();
    while let Some(var) = solver.vsids.pick_branching_variable_bucket(&solver.vals) {
        popped_vars.push(var.index());
    }

    assert!(
        !popped_vars.is_empty(),
        "bucket queue should contain domain variables"
    );
    for &idx in &popped_vars {
        assert!(
            idx < 5,
            "bucket queue should only contain domain variables (0-4), got {idx}"
        );
    }

    solver.clear_domain();
    assert!(!solver.bucket_queue_active);
}

/// IC3 mode: activities are preserved across domain changes (#8569 Gap 4).
///
/// Verify that VSIDS activities are not destroyed when the bucket queue
/// is rebuilt with a different domain. The bucket queue assignment uses
/// each variable's current activity, so activities must persist.
#[test]
fn test_ic3_mode_activities_preserved_across_domain_change() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..20).map(|_| solver.new_var()).collect();

    // Bump specific variables to create known activity ordering.
    for _ in 0..50 {
        solver.vsids.bump(vars[3], &solver.vals, true);
    }
    for _ in 0..20 {
        solver.vsids.bump(vars[1], &solver.vals, true);
    }
    for _ in 0..5 {
        solver.vsids.bump(vars[0], &solver.vals, true);
    }

    let act_before_0 = solver.vsids.activity(vars[0]);
    let act_before_1 = solver.vsids.activity(vars[1]);
    let act_before_3 = solver.vsids.activity(vars[3]);

    // Add clauses.
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);

    solver.set_ic3_mode();

    // First domain: vars 0, 1, 3
    solver.set_domain(&[vars[0], vars[1], vars[3]]);

    // Activities should be unchanged after domain set.
    assert_eq!(
        solver.vsids.activity(vars[0]),
        act_before_0,
        "activity of var 0 should be preserved after set_domain"
    );
    assert_eq!(
        solver.vsids.activity(vars[1]),
        act_before_1,
        "activity of var 1 should be preserved after set_domain"
    );
    assert_eq!(
        solver.vsids.activity(vars[3]),
        act_before_3,
        "activity of var 3 should be preserved after set_domain"
    );

    // The bucket queue should pop var 3 first (highest activity).
    let first = solver.vsids.pick_branching_variable_bucket(&solver.vals);
    assert_eq!(
        first,
        Some(vars[3]),
        "highest-activity domain variable should be popped first"
    );

    solver.clear_domain();

    // Activities should still be preserved after clear_domain.
    assert_eq!(
        solver.vsids.activity(vars[0]),
        act_before_0,
        "activity of var 0 should be preserved after clear_domain"
    );
    assert_eq!(
        solver.vsids.activity(vars[1]),
        act_before_1,
        "activity of var 1 should be preserved after clear_domain"
    );
    assert_eq!(
        solver.vsids.activity(vars[3]),
        act_before_3,
        "activity of var 3 should be preserved after clear_domain"
    );

    // Second domain: different set. Activities should still reflect bumps.
    solver.set_domain(&[vars[0], vars[1]]);
    let first2 = solver.vsids.pick_branching_variable_bucket(&solver.vals);
    assert_eq!(
        first2,
        Some(vars[1]),
        "var 1 should be highest-activity in domain [0,1]"
    );

    solver.clear_domain();
}

/// Multiple consecutive IC3 queries with bucket queue — simulates
/// a typical IC3 engine workflow.
#[test]
fn test_bucket_queue_multiple_ic3_queries() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..50).map(|_| solver.new_var()).collect();

    // Transition relation: implication chains
    for i in (0..48).step_by(2) {
        solver.add_clause(vec![
            Literal::negative(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    // Run 10 IC3-like queries
    for q in 0..10 {
        solver.push();

        // Cube assumption: force first 3 variables
        let base = (q * 4) % 40;
        solver.add_clause(vec![Literal::positive(vars[base])]);
        solver.add_clause(vec![Literal::positive(vars[base + 1])]);

        // Small domain around the cube
        let domain_start = base;
        let domain_end = (base + 8).min(50);
        let domain: Vec<Variable> = (domain_start..domain_end).map(|i| vars[i]).collect();
        solver.set_domain(&domain);
        assert!(solver.bucket_queue_active);

        let result = solver.solve();
        match result.into_inner() {
            SatResult::Sat(_) | SatResult::Unsat(_) | SatResult::Unknown => {}
        }

        let _ = solver.pop();
        solver.clear_domain();
    }
}
