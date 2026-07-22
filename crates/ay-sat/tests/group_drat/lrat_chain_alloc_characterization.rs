// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Performance characterization tests for LRAT proof chain allocation patterns.
//!
//! These tests exercise the LRAT hint chain construction paths that have
//! known per-call O(num_vars) allocations and O(n²) dedup behavior.
//! They verify correctness while documenting the performance gap.
//!
//! ## Known Allocation Sites (all LRAT-enabled only)
//!
//! 1. `collect_resolution_chain` (conflict_analysis.rs:1140) — allocates
//!    `vec![false; num_vars]` per call. Should use solver-level scratch buffer
//!    (lrat_needed/lrat_marks pattern).
//!
//! 2. `replace_clause_impl` (mutate.rs:453,460) — allocates TWO
//!    `vec![false; num_vars]` per clause replacement. Called from vivification
//!    (per strengthened clause) and OTFS.
//!
//! 3. `inprocessing.rs:954-955` — two more `vec![false; num_vars]` in the
//!    level-0 LRAT chain collector for failed literal probing.
//!
//! ## Known Quadratic Sites
//!
//! `push_lrat_hint` (mutate.rs:71) pushes non-zero hints. Deduplication
//! is handled at the proof output boundary in `ProofManager::emit_add`
//! (#5248) using a HashSet.
//!
//! ## References
//!
//! - #4172 (sat-debuggability tracking)
//! - CaDiCaL uses reusable stamp arrays (reference/cadical/src/analyze.cpp)
//! - Solver already has the correct pattern: minimize_visited/minimize_to_clear

use ay_sat::{parse_dimacs, ProofOutput, Solver};
use ntest::timeout;

/// PHP(5,4): 20 vars, 45 clauses. Large enough to trigger vivification.
const PHP54_DIMACS: &str = "\
p cnf 20 45
1 2 3 4 0
5 6 7 8 0
9 10 11 12 0
13 14 15 16 0
17 18 19 20 0
-1 -5 0
-1 -9 0
-1 -13 0
-1 -17 0
-5 -9 0
-5 -13 0
-5 -17 0
-9 -13 0
-9 -17 0
-13 -17 0
-2 -6 0
-2 -10 0
-2 -14 0
-2 -18 0
-6 -10 0
-6 -14 0
-6 -18 0
-10 -14 0
-10 -18 0
-14 -18 0
-3 -7 0
-3 -11 0
-3 -15 0
-3 -19 0
-7 -11 0
-7 -15 0
-7 -19 0
-11 -15 0
-11 -19 0
-15 -19 0
-4 -8 0
-4 -12 0
-4 -16 0
-4 -20 0
-8 -12 0
-8 -16 0
-8 -20 0
-12 -16 0
-12 -20 0
-16 -20 0
";

/// Solve a DIMACS formula with LRAT enabled and return the proof text.
fn solve_with_lrat(dimacs: &str) -> String {
    let formula = parse_dimacs(dimacs).expect("parse DIMACS");
    let proof_output = ProofOutput::lrat_text(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_output);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "formula must be UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should exist");
    let proof = String::from_utf8(writer.into_vec().expect("proof flush")).expect("Valid UTF-8");
    assert!(!proof.is_empty(), "LRAT proof must not be empty");
    proof
}

/// Check if any LRAT proof line has more than `min_hints` hint IDs.
fn has_nontrivial_hints(proof: &str, min_hints: usize) -> bool {
    proof.lines().any(|line| {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if let Some(first_zero_pos) = parts.iter().position(|&p| p == "0") {
            let hint_count = parts[first_zero_pos + 1..]
                .iter()
                .filter(|&&p| p != "0")
                .count();
            hint_count > min_hints
        } else {
            false
        }
    })
}

/// Exercise the LRAT hint chain allocation paths with PHP(4,3).
///
/// Targets `collect_resolution_chain` and `append_lrat_unit_chain`
/// which allocate `vec![false; num_vars]` per call.
#[test]
#[timeout(10_000)]
fn lrat_chain_alloc_exercised_on_php43() {
    let php43 = "\
p cnf 12 22
1 2 3 0
4 5 6 0
7 8 9 0
10 11 12 0
-1 -4 0
-1 -7 0
-1 -10 0
-4 -7 0
-4 -10 0
-7 -10 0
-2 -5 0
-2 -8 0
-2 -11 0
-5 -8 0
-5 -11 0
-8 -11 0
-3 -6 0
-3 -9 0
-3 -12 0
-6 -9 0
-6 -12 0
-9 -12 0
";

    let proof = solve_with_lrat(php43);

    // Each learned clause exercised the chain allocator
    let add_steps = proof.lines().count();
    assert!(
        add_steps >= 5,
        "PHP(4,3) should produce at least 5 LRAT proof steps (got {add_steps})"
    );
}

/// Exercise LRAT chain with vivification. Vivification calls
/// `replace_clause_impl` which allocates two `vec![false; num_vars]`
/// per strengthened clause when LRAT is enabled.
#[test]
#[timeout(30_000)]
fn lrat_chain_alloc_with_vivification() {
    let proof = solve_with_lrat(PHP54_DIMACS);

    assert!(
        has_nontrivial_hints(&proof, 2),
        "LRAT proof should contain at least one step with >2 hints \
         (exercising the chain allocator)"
    );
}

/// Verify LRAT proofs with many level-0 propagations.
///
/// Creates a unit-chain formula where all propagation happens at level 0.
/// Each level-0 conflict exercises `record_level0_conflict_chain` →
/// `collect_resolution_chain`, which allocates `vec![false; num_vars]`.
#[test]
#[timeout(10_000)]
fn lrat_chain_with_many_level0_propagations() {
    // Chain: a→b→c→d→e→f, then ¬f — conflict at level 0.
    let dimacs = "\
p cnf 6 7
1 0
-1 2 0
-2 3 0
-3 4 0
-4 5 0
-5 6 0
-6 0
";

    let proof = solve_with_lrat(dimacs);

    // Last LRAT step should derive the empty clause with hint chain
    // referencing most/all of the 7 original clauses.
    let last_line = proof.lines().last().expect("proof should have lines");
    assert!(
        last_line.contains(" 0 "),
        "last proof step should contain the empty clause marker"
    );

    let parts: Vec<&str> = last_line.split_whitespace().collect();
    if let Some(first_zero) = parts.iter().position(|&p| p == "0") {
        let hints: Vec<&str> = parts[first_zero + 1..]
            .iter()
            .copied()
            .filter(|&p| p != "0")
            .collect();
        assert!(
            hints.len() >= 2,
            "level-0 conflict chain should have >=2 hint IDs (got {}): {:?}",
            hints.len(),
            hints
        );
    }
}
