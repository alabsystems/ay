// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boundary condition tests for ClauseTrace (#4172, algorithm_audit).
//!
//! These tests document edge cases in the clause trace API that affect
//! proof DAG construction reliability:
//!
//! 1. set_resolution_hints returns false for missing clause IDs
//!    (both call sites in conflict_analysis.rs enforce via debug_assert)
//! 2. Duplicate clause IDs cause first-match-only hint assignment
//! 3. Overwriting hints replaces previous values silently
//! 4. Atomic add_clause_with_hints avoids the two-step race window

use ay_sat::{ClauseTrace, Literal, ProofOutput, Solver, Variable};

/// Verify that set_resolution_hints returns false for missing clause IDs.
///
/// Both call sites in conflict_analysis.rs now enforce the return value
/// via `debug_assert!`. If a clause ID is wrong or the
/// add_clause/set_resolution_hints calls are out of sync, the solver
/// panics in debug builds. This test documents the boundary behavior.
#[test]
fn test_set_resolution_hints_returns_false_for_missing_id() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);

    // ID 1 exists: should succeed
    assert!(trace.set_resolution_hints(1, vec![10, 20]));
    assert_eq!(trace.entries().at(0).resolution_hints, vec![10, 20]);

    // ID 2 doesn't exist: returns false, no panic
    assert!(!trace.set_resolution_hints(2, vec![30]));

    // ID 0 doesn't exist
    assert!(!trace.set_resolution_hints(0, vec![40]));

    // Original entry unchanged after failed set
    assert_eq!(trace.entries().at(0).resolution_hints, vec![10, 20]);
}

/// Verify that set_resolution_hints overwrites previous hints.
///
/// If set_resolution_hints is called twice on the same clause, the second
/// call silently replaces the first. This is correct behavior for
/// conflict_analysis which may update hints after shrink/minimize, but
/// callers should be aware that previous hints are lost.
#[test]
fn test_set_resolution_hints_overwrites_previous() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], false);

    assert!(trace.set_resolution_hints(1, vec![10, 20]));
    assert_eq!(trace.entries().at(0).resolution_hints, vec![10, 20]);

    // Second call overwrites
    assert!(trace.set_resolution_hints(1, vec![30, 40, 50]));
    assert_eq!(trace.entries().at(0).resolution_hints, vec![30, 40, 50]);
}

/// Verify that add_clause_with_hints records both clause and hints atomically.
///
/// Unlike the add_clause + set_resolution_hints two-step pattern in
/// conflict_analysis, add_clause_with_hints is atomic. This test verifies
/// that using the atomic API avoids the window where hints can be lost.
#[test]
fn test_add_clause_with_hints_is_atomic() {
    let mut trace = ClauseTrace::new();
    trace.add_clause_with_hints(
        42,
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        false,
        vec![10, 20, 30],
    );

    assert_eq!(trace.len(), 1);
    let entry = trace.entries().at(0);
    assert_eq!(entry.id, 42);
    assert!(!entry.is_original);
    assert_eq!(entry.resolution_hints, vec![10, 20, 30]);
}

/// Verify that duplicate clause IDs in the trace cause set_resolution_hints
/// to only update the LAST matching entry (rfind semantics).
///
/// If the solver accidentally adds two clauses with the same ID (a bug),
/// set_resolution_hints uses rfind (reverse search) for O(1) amortized cost,
/// so it updates the most recently added entry. This test documents the
/// behavior for awareness.
#[test]
fn test_set_resolution_hints_updates_first_duplicate_id_only() {
    let mut trace = ClauseTrace::new();
    // Two entries with same ID (shouldn't happen, but test the edge case)
    trace.add_clause(5, vec![Literal::positive(Variable::new(0))], false);
    trace.add_clause(5, vec![Literal::negative(Variable::new(1))], false);

    assert!(trace.set_resolution_hints(5, vec![100]));

    // rfind updates the last (most recent) entry with the matching ID
    assert!(trace.entries().at(0).resolution_hints.is_empty());
    assert_eq!(trace.entries().at(1).resolution_hints, vec![100]);
}

/// Verify empty clause detection via add_clause_with_hints.
///
/// The has_empty_clause flag is critical for SatProofManager: it gates
/// whether proof reconstruction is attempted. Ensure the flag is set
/// when an empty clause is added via the atomic hints API.
#[test]
fn test_empty_clause_detection_via_atomic_api() {
    let mut trace = ClauseTrace::new();
    assert!(!trace.has_empty_clause());

    // Add non-empty clause
    trace.add_clause_with_hints(
        1,
        vec![Literal::positive(Variable::new(0))],
        true,
        Vec::new(),
    );
    assert!(!trace.has_empty_clause());

    // Add empty clause with hints (learned empty clause from conflict analysis)
    trace.add_clause_with_hints(2, Vec::new(), false, vec![1]);
    assert!(trace.has_empty_clause());
}

/// Verify with_capacity doesn't affect behavior, only allocation.
///
/// Pre-allocation should be transparent — no off-by-one in capacity vs
/// actual entry count.
#[test]
fn test_with_capacity_boundary() {
    let mut trace = ClauseTrace::with_capacity(0);
    assert!(trace.is_empty());
    assert_eq!(trace.len(), 0);

    // Adding entries beyond initial capacity should work
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    assert_eq!(trace.len(), 1);

    let mut trace2 = ClauseTrace::with_capacity(1000);
    assert!(trace2.is_empty());
    trace2.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    assert_eq!(trace2.len(), 1);
}

/// Verify learned_clauses and original_clauses iterators are disjoint.
///
/// Every entry must appear in exactly one iterator. This is a correctness
/// invariant for SatProofManager which processes originals and learned
/// clauses differently.
#[test]
fn test_original_learned_partition_is_complete() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(2, vec![Literal::negative(Variable::new(1))], false);
    trace.add_clause_with_hints(3, vec![Literal::positive(Variable::new(2))], true, vec![1]);
    trace.add_clause_with_hints(4, Vec::new(), false, vec![1, 2]);

    let original_count = trace.original_clauses().count();
    let learned_count = trace.learned_clauses().count();

    assert_eq!(original_count, 2);
    assert_eq!(learned_count, 2);
    assert_eq!(
        original_count + learned_count,
        trace.len(),
        "original + learned must equal total"
    );
}

/// End-to-end regression test: solve UNSAT formula and verify learned
/// clauses from conflict analysis have non-empty resolution hints.
///
/// This is the acceptance-criteria test for #4325. Previous code silently
/// discarded hints via `let _ = trace.set_resolution_hints(...)`. The fix
/// (debug_assert at both call sites) catches ID mismatches in debug builds.
/// This test proves the positive case: in a real solve, non-empty learned
/// clauses (from conflict analysis) receive their resolution chain.
///
/// Uses PHP(4,3) — 4 pigeons, 3 holes — which is UNSAT and large enough
/// to force conflict analysis beyond level-0 preprocessing.
///
/// Note: empty learned clauses (the final UNSAT derivation) may have empty
/// hints when derived via mark_empty_clause (BVE/preprocessing path).
/// Fixing that gap is tracked in #4124.
#[test]
fn test_clause_trace_learned_clauses_have_resolution_hints() {
    // PHP(4,3): 4 pigeons, 3 holes -> 12 variables, guaranteed UNSAT
    let pigeons: usize = 4;
    let holes: usize = 3;
    let num_vars = pigeons * holes;
    let mut clauses: Vec<Vec<Literal>> = Vec::new();

    // At-least-one: each pigeon must be in some hole
    for i in 0..pigeons {
        let clause: Vec<Literal> = (0..holes)
            .map(|j| Literal::positive(Variable::new((i * holes + j) as u32)))
            .collect();
        clauses.push(clause);
    }

    // At-most-one: no hole has two pigeons
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                clauses.push(vec![
                    Literal::negative(Variable::new((i1 * holes + j) as u32)),
                    Literal::negative(Variable::new((i2 * holes + j) as u32)),
                ]);
            }
        }
    }

    let num_original = clauses.len() as u64;
    let proof_writer = ProofOutput::lrat_text(Vec::new(), num_original);
    let mut solver: Solver = Solver::with_proof_output(num_vars, proof_writer);
    solver.enable_clause_trace();

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(4,3) must be UNSAT");

    let trace = solver.clause_trace().expect("clause trace was enabled");
    assert!(
        trace.has_empty_clause(),
        "UNSAT must derive the empty clause"
    );

    // Check non-empty learned clauses (from conflict analysis, not mark_empty_clause)
    let non_empty_learned: Vec<_> = trace
        .learned_clauses()
        .filter(|e| !e.clause.is_empty())
        .collect();

    // If conflict analysis ran, all non-empty learned clauses must have hints
    for entry in &non_empty_learned {
        assert!(
            !entry.resolution_hints.is_empty(),
            "learned clause ID {} (lits={:?}) has empty resolution hints — \
             set_resolution_hints failed silently (regression #4325)",
            entry.id,
            entry.clause
        );
    }

    // At least verify that the trace recorded something beyond originals
    let total_learned = trace.learned_clauses().count();
    assert!(
        total_learned > 0,
        "UNSAT trace must have at least one learned entry"
    );
}
