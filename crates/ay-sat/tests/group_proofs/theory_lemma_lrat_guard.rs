// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{Literal, ProofOutput, Solver, Variable};

#[test]
fn test_theory_lemma_fail_closes_lrat_emission() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 1);
    let mut solver = Solver::with_proof_output(1, proof);
    let x0 = Literal::positive(Variable::new(0));

    assert!(solver.add_clause(vec![x0]), "input unit should be accepted");
    assert!(
        solver.add_theory_lemma(vec![x0.negated()]).is_some(),
        "unit theory lemma should be recorded as a watched clause"
    );
    assert!(
        solver.solve().is_unsat(),
        "formula must be UNSAT after contradictory theory lemma"
    );

    let proof_writer = solver.proof_writer().expect("proof writer must exist");
    assert_eq!(
        proof_writer.added_count(),
        1,
        "theory lemma must be suppressed; only final empty clause may remain"
    );

    let proof_bytes = solver
        .take_proof_writer()
        .expect("proof writer should be available")
        .into_vec()
        .expect("proof extraction should succeed");
    let proof_text = String::from_utf8(proof_bytes).expect("proof bytes must be UTF-8");
    let lines: Vec<&str> = proof_text.lines().collect();
    assert_eq!(
        lines.len(),
        1,
        "proof must contain exactly one line (final empty-clause step)"
    );
    // The LRAT empty clause step has format: ID 0 [hints...] 0
    // The first 0 terminates the (empty) literal list; hints may follow
    // (#7108 added level-0 unit proof IDs as hints for the empty clause).
    let tokens: Vec<&str> = lines[0].split_whitespace().collect();
    assert!(
        tokens.len() >= 3 && tokens[1] == "0",
        "remaining LRAT step should be an empty-clause addition: {}",
        lines[0]
    );
}

#[test]
fn test_pure_sat_lrat_still_emits_proof_steps() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 2);
    let mut solver = Solver::with_proof_output(1, proof);
    let x0 = Literal::positive(Variable::new(0));

    assert!(
        solver.add_clause(vec![x0]),
        "first unit clause should be accepted"
    );
    assert!(
        solver.add_clause(vec![x0.negated()]),
        "second conflicting unit clause should be accepted"
    );
    assert!(
        solver.solve().is_unsat(),
        "pure SAT contradictory units must be UNSAT"
    );

    let proof_writer = solver.proof_writer().expect("proof writer must exist");
    assert!(
        proof_writer.added_count() > 0,
        "pure SAT LRAT path must still emit derived proof steps"
    );
}

#[test]
fn test_theory_lemma_fail_close_keeps_clause_trace_ids_unique() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 2);
    let mut solver = Solver::with_proof_output(2, proof);
    solver.enable_clause_trace();

    let x0 = Literal::positive(Variable::new(0));
    let x1 = Literal::positive(Variable::new(1));
    let nx0 = x0.negated();
    let nx1 = x1.negated();

    // SAT base formula.
    assert!(
        solver.add_clause(vec![x0, x1]),
        "base clause should be accepted"
    );
    assert!(
        solver.add_clause(vec![nx0, x1]),
        "base clause should be accepted"
    );

    // Theory lemma is non-empty and hintless in LRAT mode; fail-close blocks
    // non-empty proof writes but the clause still gets a solver-side clause ID.
    assert!(
        solver.add_theory_lemma(vec![nx1]).is_some(),
        "theory lemma should be added to clause DB"
    );
    assert!(
        solver.solve().is_unsat(),
        "theory lemma should make formula UNSAT"
    );

    let trace = solver
        .take_clause_trace()
        .expect("clause trace should be enabled");
    let ids: Vec<u64> = trace.entries().iter().map(|e| e.id).collect();
    let unique_ids: std::collections::HashSet<u64> = ids.iter().copied().collect();

    assert_eq!(
        unique_ids.len(),
        ids.len(),
        "clause trace IDs must remain unique under LRAT fail-close: {ids:?}"
    );
    assert!(
        ids.windows(2).all(|w| w[0] < w[1]),
        "clause trace IDs must be strictly increasing: {ids:?}"
    );
}
