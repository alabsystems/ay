// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test that level-0 BCP conflicts produce LRAT proofs with non-empty hints.
//!
//! Regression test for #4397: `mark_empty_clause` wrote empty LRAT hints,
//! discarding the resolution chain collected by `record_level0_conflict_chain`.
//!
//! This test isolates the level-0 BCP conflict path from inprocessing hints
//! (#4398) by using a formula that is UNSAT purely from unit propagation at
//! decision level 0.

use ay_sat::{Literal, ProofOutput, Solver, Variable};

/// Formula: (a) ∧ (¬a ∨ b) ∧ (¬b) — UNSAT from level-0 BCP.
///
/// BCP at level 0:
/// - Unit clause (a) propagates a=true
/// - (¬a ∨ b) propagates b=true
/// - (¬b) conflicts
///
/// The empty clause must have resolution hints referencing the original clauses.
#[test]
fn test_lrat_level0_bcp_conflict_has_hints() {
    let proof_writer = ProofOutput::lrat_text(Vec::new(), 3);
    let mut solver = Solver::with_proof_output(2, proof_writer);

    let a = Literal::positive(Variable::new(0));
    let na = Literal::negative(Variable::new(0));
    let b = Literal::positive(Variable::new(1));
    let nb = Literal::negative(Variable::new(1));

    // 3 original clauses → clause IDs 1, 2, 3
    solver.add_clause(vec![a]); // clause 1: a
    solver.add_clause(vec![na, b]); // clause 2: ¬a ∨ b
    solver.add_clause(vec![nb]); // clause 3: ¬b

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    // The proof should contain the empty clause derivation with non-empty hints.
    // LRAT format: <id> <literals> 0 <hints> 0
    // With empty hints: <id> 0 0  (just "N 0 0")
    // With proper hints: <id> 0 <hint1> <hint2> ... 0
    let lines: Vec<&str> = proof.lines().collect();
    assert!(
        !lines.is_empty(),
        "LRAT proof must not be empty for UNSAT formula"
    );

    // The last line should be the empty clause (no literals before the first 0).
    let last_line = lines.last().expect("proof must have at least one line");
    let tokens: Vec<&str> = last_line.split_whitespace().collect();
    // Format: <id> 0 <hints...> 0
    assert!(
        tokens.len() >= 2,
        "Empty clause line too short: {last_line}"
    );

    // Find the first "0" (end of literals). For the empty clause, position 1.
    let first_zero = tokens
        .iter()
        .position(|t| *t == "0")
        .expect("missing literal terminator");
    assert_eq!(
        first_zero, 1,
        "Expected empty clause (first 0 at position 1), got: {last_line}"
    );

    // Everything between first_zero+1 and the trailing 0 is hints.
    let trailing_zero = tokens.len() - 1;
    let hint_count = trailing_zero - first_zero - 1;
    assert!(
        hint_count > 0,
        "BUG (#4397): Empty clause has NO resolution hints. \
         record_level0_conflict_chain must pass hints to proof_writer.\n\
         Proof line: {last_line}\nFull proof:\n{proof}"
    );
}

/// Verify that a formula with only contradictory unit clauses produces
/// a valid LRAT proof (or correctly derives UNSAT without needing hints).
///
/// Formula: (a) ∧ (¬a) — direct contradiction at level 0.
/// This may be handled by add_clause (mark_empty_clause) before solve(),
/// in which case empty hints are correct (the contradiction is trivial).
#[test]
fn test_lrat_contradictory_units() {
    let proof_writer = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(1, proof_writer);

    let a = Literal::positive(Variable::new(0));
    let na = Literal::negative(Variable::new(0));

    solver.add_clause(vec![a]); // clause 1: a
    solver.add_clause(vec![na]); // clause 2: ¬a

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    // The proof must not be empty — at minimum the empty clause must be derived.
    assert!(!proof.is_empty(), "LRAT proof must not be empty");
}
