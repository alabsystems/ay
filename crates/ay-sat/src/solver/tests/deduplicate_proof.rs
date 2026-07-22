// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof verification tests for binary clause deduplication.
//!
//! Deduplicate runs as a sub-step of decompose (not independently gated).
//! These tests verify that its LRAT/DRAT proof emissions and model
//! consistency are correct.

use super::*;

/// Verify that deduplicate's hyper-unary unit derivation emits a valid LRAT
/// proof step with correct antecedent hints.
///
/// Formula: (a ∨ b) ∧ (a ∨ ¬b) — resolving gives unit a.
/// The LRAT proof must contain a derived unit clause for `a` with hints
/// referencing both antecedent clause IDs.
#[test]
fn test_deduplicate_hyper_unary_emits_lrat_proof() {
    use crate::ProofOutput;

    // 2 original clauses → LRAT IDs start at 1, next derived ID = 3.
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 2);
    let mut solver: Solver = Solver::with_proof_output(2, proof);

    let a = Variable(0);
    let b = Variable(1);
    let a_pos = Literal::positive(a);

    // Clause 1: (a ∨ b), Clause 2: (a ∨ ¬b)
    solver.add_clause_db(&[a_pos, Literal::positive(b)], false);
    solver.add_clause_db(&[a_pos, Literal::negative(b)], false);
    solver.initialize_watches();

    let unsat = solver.deduplicate_binary_clauses();
    assert!(!unsat, "hyper-unary derivation should not mark UNSAT");
    assert_eq!(
        solver.get_var_assignment(a.index()),
        Some(true),
        "hyper-unary pair must derive unit a"
    );

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should exist");
    let proof_text =
        String::from_utf8(writer.into_vec().expect("proof flush")).expect("valid UTF-8");

    // Derived unit clause for literal `a` (DIMACS literal 1).
    // LRAT format: <id> <literals> 0 <hints> 0
    // The unit clause should reference both antecedent clause IDs (1 and 2).
    assert!(
        !proof_text.is_empty(),
        "LRAT proof must contain the hyper-unary derivation step"
    );
    assert!(
        proof_text.contains(" 1 0 "),
        "proof must contain derived unit clause for literal 1 (a): got: {proof_text}"
    );
    // Hints must reference both original clause IDs.
    assert!(
        proof_text.contains("1 ") && proof_text.contains("2 "),
        "proof hints must reference both antecedent clause IDs 1 and 2: got: {proof_text}"
    );
}

/// Verify that deduplicate emits valid DRAT proof steps for duplicate
/// clause deletion. DRAT deletions use `d <clause>` lines.
///
/// Formula: two copies of (a ∨ b). Deduplicate deletes one copy and the
/// DRAT proof must record the deletion.
#[test]
fn test_deduplicate_duplicate_deletion_emits_drat_proof() {
    use crate::ProofOutput;

    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver: Solver = Solver::with_proof_output(2, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    // Two identical binary clauses: (a ∨ b) and (a ∨ b).
    solver.add_clause_db(&[a, b], false);
    solver.add_clause_db(&[a, b], false);
    solver.initialize_watches();

    let unsat = solver.deduplicate_binary_clauses();
    assert!(!unsat, "simple dedup should not derive UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should exist");
    let proof_text =
        String::from_utf8(writer.into_vec().expect("proof flush")).expect("valid UTF-8");

    // DRAT proof should contain a deletion line for the duplicate clause.
    // DRAT deletion format: "d <literals> 0\n"
    assert!(
        proof_text.contains("d "),
        "DRAT proof must contain deletion step for duplicate clause: got: {proof_text}"
    );
}

/// Verify that deduplicate's hyper-unary unit derivation is model-consistent.
///
/// Formula: (a ∨ b) ∧ (a ∨ ¬b) ∧ (¬a ∨ c) — satisfiable with a=T, c=T.
/// After deduplicate derives unit a from the hyper-unary pair, check that
/// the derived assignment satisfies all original clauses.
#[test]
fn test_deduplicate_hyper_unary_model_consistent() {
    let mut solver: Solver = Solver::new(3);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let a_pos = Literal::positive(a);

    // Store original clauses for model verification.
    let clauses: Vec<Vec<Literal>> = vec![
        vec![a_pos, Literal::positive(b)],
        vec![a_pos, Literal::negative(b)],
        vec![Literal::negative(a), Literal::positive(c)],
    ];

    for cl in &clauses {
        solver.add_clause_db(cl, false);
    }
    solver.initialize_watches();

    let unsat = solver.deduplicate_binary_clauses();
    assert!(
        !unsat,
        "formula is satisfiable; deduplicate must not claim UNSAT"
    );

    // Deduplicate should have derived unit a.
    assert_eq!(
        solver.get_var_assignment(a.index()),
        Some(true),
        "hyper-unary pair must derive unit a"
    );

    // Propagate to check all consequences.
    assert!(
        !solver.propagate_check_unsat(),
        "propagation must not detect conflict on satisfiable formula"
    );

    // Verify model consistency: every original clause must have at least
    // one literal satisfied by the current assignment.
    for (i, cl) in clauses.iter().enumerate() {
        let satisfied = cl.iter().any(|&lit| solver.lit_value(lit) == Some(true));
        let has_unassigned = cl.iter().any(|&lit| solver.lit_value(lit).is_none());
        assert!(
            satisfied || has_unassigned,
            "clause {i} ({cl:?}) must be satisfiable under derived assignments"
        );
    }
}
