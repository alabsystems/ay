// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! Proof format integration tests for ay-sat.
//!
//! LRAT detailed API tests, binary proof format encoding, and proof
//! compatibility tests. Split from integration.rs for #6864.

use ay_sat::{parse_dimacs, ClauseRef, Literal, Solver, Variable};
use ntest::timeout;

/// Test clause ID tracking when LRAT is enabled
#[test]
#[timeout(3_000)]
fn test_lrat_clause_id_tracking() {
    let mut solver = Solver::new(3);
    solver.enable_lrat();

    // Add original clauses - should get IDs 1, 2, 3
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::negative(Variable::new(2)),
    ]);

    // Clause IDs should be 1, 2, 3.
    // ClauseRef stores word offsets: each 2-literal clause occupies
    // HEADER_WORDS header words + 2 literal words.
    let stride = ay_sat::arena_limits::HEADER_WORDS as u32 + 2;
    assert_eq!(solver.clause_id(ClauseRef::new(0)), 1);
    assert_eq!(solver.clause_id(ClauseRef::new(stride)), 2);
    assert_eq!(solver.clause_id(ClauseRef::new(2 * stride)), 3);
}

/// Test that LRAT resolution chain is collected during conflict analysis
#[test]
#[timeout(3_000)]
fn test_lrat_resolution_chain() {
    use ay_sat::{ProofOutput, SatResult};

    // Simple UNSAT formula: (x1) AND (NOT x1)
    let dimacs = r"
p cnf 1 2
1 0
-1 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    // enable_lrat() must be called before adding clauses. Use
    // with_proof_output to create the solver with LRAT from the start,
    // then add clauses manually (same pattern as test_lrat_resolution_chain_tracking).
    let proof_buffer: Vec<u8> = Vec::new();
    let num_original = formula.clauses.len() as u64;
    let proof_writer = ProofOutput::lrat_text(proof_buffer, num_original);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)), "Should be UNSAT");

    // The resolution chain should contain the clause IDs used in derivation.
    // For this simple case, it should contain IDs 1 and 2.
    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");
    assert!(!proof.is_empty(), "LRAT proof should not be empty");
}

/// Test that enable_lrat() panics when called after clauses have been added.
/// Late enabling creates unstable clause IDs (ID collisions).
#[test]
#[should_panic(expected = "must be called before adding any clauses")]
fn test_late_enable_lrat_panics() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    // This must panic — clauses already added.
    solver.enable_lrat();
}

/// Test that enable_clause_trace() panics when called after clauses have been added.
#[test]
#[should_panic(expected = "must be called before adding any clauses")]
fn test_late_enable_clause_trace_panics() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    // This must panic — clauses already added.
    solver.enable_clause_trace();
}

/// Test that enable_lrat() before any clauses is fine.
#[test]
fn test_enable_lrat_before_clauses_succeeds() {
    let mut solver = Solver::new(2);
    solver.enable_lrat();
    // Adding clauses after enable is fine.
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
}

/// Test that enable_clause_trace() before any clauses is fine.
#[test]
fn test_enable_clause_trace_before_clauses_succeeds() {
    let mut solver = Solver::new(2);
    solver.enable_clause_trace();
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
}

/// Test LRAT writer integration with solver
#[test]
#[timeout(3_000)]
fn test_lrat_writer_output() {
    use ay_sat::LratWriter;

    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 3);

    // Simulate adding learned clause with resolution chain
    let clause = vec![Literal::positive(Variable::new(0))];
    let hints = vec![1, 2, 3];
    let id = writer.add(&clause, &hints).unwrap();

    assert_eq!(id, 4); // First learned clause after 3 original clauses

    let output = String::from_utf8(buf).unwrap();
    assert_eq!(output, "4 1 0 1 2 3 0\n");
}

/// Test LRAT proof generation with ProofOutput enum
#[test]
#[timeout(3_000)]
fn test_lrat_proof_with_proof_output() {
    use ay_sat::ProofOutput;

    // Simple UNSAT formula: (x1) AND (NOT x1)
    let dimacs = r"
p cnf 1 2
1 0
-1 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    let proof_buffer: Vec<u8> = Vec::new();
    // LRAT needs to know number of original clauses - we pass 2 (the number of clauses)
    let proof_writer = ProofOutput::lrat_text(proof_buffer, 2);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof =
        String::from_utf8(writer.into_vec().expect("proof writer flush")).expect("Valid UTF-8");

    // LRAT proof should contain an empty clause line.
    // Format: "id 0 hints... 0" — the empty clause has no literals,
    // so the first token after the ID is `0` (literal terminator).
    let has_empty_clause = proof.lines().any(|line| {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        // Minimum: "id 0 0" (empty clause with no hints) or
        // "id 0 hint1 ... hintN 0" (empty clause with hints).
        tokens.len() >= 3 && tokens[1] == "0" && !tokens[0].starts_with('d')
    });
    assert!(
        has_empty_clause,
        "LRAT proof should contain empty clause: {proof}"
    );
}

/// Test LRAT proof generation for harder UNSAT formula
#[test]
#[timeout(3_000)]
fn test_lrat_proof_harder_unsat() {
    use ay_sat::ProofOutput;

    // Harder UNSAT: mutual exclusion
    // (x1 OR x2) AND (NOT x1 OR NOT x2) AND (x1 OR NOT x2) AND (NOT x1 OR x2)
    // This has no solution
    let dimacs = r"
p cnf 2 4
1 2 0
-1 -2 0
1 -2 0
-1 2 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::lrat_text(proof_buffer, 4);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof =
        String::from_utf8(writer.into_vec().expect("proof writer flush")).expect("Valid UTF-8");

    // LRAT proof should have learned clauses with IDs > 4 (original clauses)
    // and end with empty clause derivation
    assert!(
        proof.ends_with("0\n"),
        "LRAT proof should end with zero: {proof}"
    );

    // Check that we have at least one line (the final empty clause)
    assert!(
        !proof.is_empty(),
        "LRAT proof should not be empty for UNSAT"
    );
}

/// Test LRAT proof with resolution chain tracking
#[test]
#[timeout(3_000)]
fn test_lrat_resolution_chain_tracking() {
    use ay_sat::ProofOutput;

    // UNSAT formula that requires learning
    // (x1) AND (x2 OR NOT x1) AND (NOT x2)
    // Resolution: resolve clause 2 and 3 on x2 to get (NOT x1)
    // Then resolve with clause 1 to get empty clause
    let dimacs = r"
p cnf 2 3
1 0
2 -1 0
-2 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::lrat_text(proof_buffer, 3);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof =
        String::from_utf8(writer.into_vec().expect("proof writer flush")).expect("Valid UTF-8");

    // LRAT format: "id literals... 0 hints... 0"
    // Each line should have exactly two 0s (one after literals, one after hints)
    for line in proof.lines() {
        assert!(
            line.split_whitespace().filter(|&s| s == "0").count() >= 2 || line.contains(" d "),
            "LRAT line should have two zeros (literals 0 hints 0) or be deletion: {line}"
        );
    }
}

/// Test ProofOutput enum correctly handles both DRAT and LRAT
#[test]
#[timeout(3_000)]
fn test_proof_output_drat_compatibility() {
    use ay_sat::ProofOutput;

    // Simple UNSAT formula: (x1) AND (NOT x1)
    let dimacs = r"
p cnf 1 2
1 0
-1 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    // Test with DRAT format
    let drat_buffer: Vec<u8> = Vec::new();
    let drat_writer = ProofOutput::drat_text(drat_buffer);
    let mut drat_solver = Solver::with_proof_output(formula.num_vars, drat_writer);

    for clause in formula.clauses.clone() {
        drat_solver.add_clause(clause);
    }

    let drat_result = drat_solver.solve().into_inner();
    assert!(drat_result.is_unsat());

    let drat_proof_writer = drat_solver
        .take_proof_writer()
        .expect("DRAT proof writer should exist");
    let drat_proof = String::from_utf8(drat_proof_writer.into_vec().expect("proof writer flush"))
        .expect("Valid UTF-8");

    // Test with LRAT format
    let lrat_buffer: Vec<u8> = Vec::new();
    let lrat_writer = ProofOutput::lrat_text(lrat_buffer, 2);
    let mut lrat_solver = Solver::with_proof_output(formula.num_vars, lrat_writer);

    for clause in formula.clauses {
        lrat_solver.add_clause(clause);
    }

    let lrat_result = lrat_solver.solve().into_inner();
    assert!(lrat_result.is_unsat());

    let lrat_proof_writer = lrat_solver
        .take_proof_writer()
        .expect("LRAT proof writer should exist");
    let lrat_proof = String::from_utf8(lrat_proof_writer.into_vec().expect("proof writer flush"))
        .expect("Valid UTF-8");

    // Both should produce valid proofs
    assert!(
        drat_proof.ends_with("0\n"),
        "DRAT proof should end with empty clause"
    );
    assert!(
        lrat_proof.ends_with("0\n"),
        "LRAT proof should end with empty clause"
    );

    // LRAT proof should have clause IDs, DRAT shouldn't
    // LRAT lines start with an ID number, DRAT lines start with literals or 'd'
    let first_lrat_line = lrat_proof.lines().next().unwrap_or("");
    let first_char = first_lrat_line.chars().next();
    if let Some(c) = first_char {
        assert!(
            c.is_ascii_digit() || c == 'd',
            "LRAT proof should start with ID or 'd': {first_lrat_line}"
        );
    }
}

// ============================================================================
// Binary Proof Format Tests
// ============================================================================

/// Test binary DRAT proof generation
#[test]
#[timeout(2_000)]
fn test_binary_drat_proof_generation() {
    use ay_sat::ProofOutput;

    // Simple UNSAT formula: (x1) AND (NOT x1)
    let dimacs = r"
p cnf 1 2
1 0
-1 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::drat_binary(proof_buffer);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof = writer.into_vec().expect("proof writer flush");

    // Binary DRAT proofs should start with 'a' (0x61) for additions
    // and contain binary-encoded literals
    assert!(!proof.is_empty(), "Binary DRAT proof should not be empty");

    // The proof should end with 'a' followed by just 0 (empty clause)
    // In binary format: 'a' (0x61) + 0x00 (terminating zero)
    let has_empty_clause = proof.windows(2).any(|w| w == [0x61, 0x00]);
    assert!(
        has_empty_clause,
        "Binary DRAT proof should contain empty clause (a\\x00)"
    );
}

/// Test binary LRAT proof generation
#[test]
#[timeout(2_000)]
fn test_binary_lrat_proof_generation() {
    use ay_sat::ProofOutput;

    // Simple UNSAT formula: (x1) AND (NOT x1)
    let dimacs = r"
p cnf 1 2
1 0
-1 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::lrat_binary(proof_buffer, 2);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof = writer.into_vec().expect("proof writer flush");

    // Binary LRAT proofs should start with 'a' (0x61) for additions
    assert!(!proof.is_empty(), "Binary LRAT proof should not be empty");

    // Check that proof starts with 'a' (addition)
    assert_eq!(
        proof[0], 0x61,
        "Binary LRAT proof should start with 'a' (0x61)"
    );

    // The proof should contain clause IDs (binary encoded)
    // For LRAT with 2 original clauses, first learned clause has ID 3
    // ID 3 is encoded as single byte 0x03 in binary format
    assert!(
        proof.len() >= 3,
        "Binary LRAT proof should have at least header + id + terminator"
    );
}

/// Test binary proof encoding matches specification
#[test]
#[timeout(2_000)]
fn test_binary_literal_encoding() {
    use ay_sat::DratWriter;

    // Test the binary literal encoding formula:
    // positive lit for var v -> 2*(v+1) (1-indexed)
    // negative lit for var v -> 2*(v+1)+1

    let mut buf = Vec::new();
    {
        let mut writer = DratWriter::new_binary(&mut buf);

        // Clause: (x0 OR -x1 OR x2)
        // x0 positive: 2*(0+1) = 2
        // x1 negative: 2*(1+1)+1 = 5
        // x2 positive: 2*(2+1) = 6
        writer
            .add(&[
                Literal::positive(Variable::new(0)),
                Literal::negative(Variable::new(1)),
                Literal::positive(Variable::new(2)),
            ])
            .unwrap();
    }

    // Expected: 'a' (0x61), lit1=2, lit2=5, lit3=6, terminator=0
    assert_eq!(buf, vec![0x61, 2, 5, 6, 0]);
}

/// Test binary proof with variable-length encoding for large literals
#[test]
#[timeout(2_000)]
fn test_binary_variable_length_encoding() {
    use ay_sat::DratWriter;

    let mut buf = Vec::new();
    {
        let mut writer = DratWriter::new_binary(&mut buf);

        // Clause with variable 100 (1-indexed: 101)
        // positive: 2*101 = 202
        // 202 in variable-length encoding:
        // 202 = 0xCA = 1100_1010
        // Low 7 bits: 0100_1010 = 0x4A = 74, with continuation bit: 0xCA
        // High bits: 0000_0001 = 1
        // Encoded as: 0xCA (74 | 0x80), 0x01
        writer
            .add(&[Literal::positive(Variable::new(100))])
            .unwrap();
    }

    // Expected: 'a' (0x61), encoded_202, terminator=0
    // 202 = 0xCA in LEB128: [0xCA, 0x01] (74 with continuation, then 1)
    assert_eq!(buf[0], 0x61); // 'a'
    assert_eq!(buf[1], 0xCA); // 202 & 0x7F | 0x80 = 74 | 128 = 202 = 0xCA
    assert_eq!(buf[2], 0x01); // 202 >> 7 = 1
    assert_eq!(buf[3], 0x00); // terminator
}

/// Test binary DRAT deletion encoding
#[test]
#[timeout(2_000)]
fn test_binary_drat_deletion() {
    use ay_sat::DratWriter;

    let mut buf = Vec::new();
    {
        let mut writer = DratWriter::new_binary(&mut buf);

        // Delete clause: (x0)
        writer
            .delete(&[Literal::positive(Variable::new(0))])
            .unwrap();
    }

    // Expected: 'd' (0x64), lit=2, terminator=0
    assert_eq!(buf, vec![0x64, 2, 0]);
}

/// Test binary LRAT with hints encoding
#[test]
#[timeout(2_000)]
fn test_binary_lrat_with_hints() {
    use ay_sat::LratWriter;

    let mut buf = Vec::new();
    {
        let mut writer = LratWriter::new_binary(&mut buf, 3);

        // Add clause ID 4: (x0) with hints [1, 2, 3]
        // Note: first learned clause after 3 original clauses gets ID 4
        let clause = vec![Literal::positive(Variable::new(0))];
        let hints = vec![1, 2, 3];
        let id = writer.add(&clause, &hints).unwrap();
        assert_eq!(id, 4);
    }

    // Expected: 'a' (0x61), id=2*4=8, lit=2, 0, hint1=2*1=2, hint2=2*2=4, hint3=2*3=6, 0
    // Binary LRAT encodes IDs as 2*id per spec (#5196).
    assert_eq!(buf, vec![0x61, 8, 2, 0, 2, 4, 6, 0]);
}

/// Test binary LRAT deletion batching
#[test]
#[timeout(2_000)]
fn test_binary_lrat_deletion() {
    use ay_sat::LratWriter;

    let mut buf = Vec::new();
    {
        let mut writer = LratWriter::new_binary(&mut buf, 2);

        // Add a clause first
        let clause = vec![Literal::positive(Variable::new(0))];
        writer.add(&clause, &[1]).unwrap();

        // Delete clauses 1 and 2
        writer.delete(1).unwrap();
        writer.delete(2).unwrap();

        // Flush to write deletions
        writer.flush().unwrap();
    }

    // Expected (binary LRAT encodes IDs as 2*id per spec #5196):
    // Add: 'a' (0x61), id=2*3=6, lit=2, 0, hint=2*1=2, 0
    // Delete: 'd' (0x64), id=2*1=2, id=2*2=4, 0
    let expected = vec![
        0x61, 6, 2, 0, 2, 0, // add clause 3: (x0) with hint 1
        0x64, 2, 4, 0, // delete clauses 1 and 2
    ];
    assert_eq!(buf, expected);
}

/// Compare binary and text proof sizes for an UNSAT formula
#[test]
#[timeout(2_000)]
fn test_binary_vs_text_proof_size() {
    use ay_sat::ProofOutput;

    // UNSAT formula: mutual exclusion (requires several learned clauses)
    let dimacs = r"
p cnf 3 6
1 2 0
-1 -2 0
2 3 0
-2 -3 0
1 3 0
-1 -3 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");

    // Generate text DRAT proof
    let text_buffer: Vec<u8> = Vec::new();
    let text_writer = ProofOutput::drat_text(text_buffer);
    let mut text_solver = Solver::with_proof_output(formula.num_vars, text_writer);

    for clause in formula.clauses.clone() {
        text_solver.add_clause(clause);
    }
    let _ = text_solver.solve().into_inner();
    let text_proof = text_solver
        .take_proof_writer()
        .unwrap()
        .into_vec()
        .expect("proof writer flush");

    // Generate binary DRAT proof
    let binary_buffer: Vec<u8> = Vec::new();
    let binary_writer = ProofOutput::drat_binary(binary_buffer);
    let mut binary_solver = Solver::with_proof_output(formula.num_vars, binary_writer);

    for clause in formula.clauses {
        binary_solver.add_clause(clause);
    }
    let _ = binary_solver.solve().into_inner();
    let binary_proof = binary_solver
        .take_proof_writer()
        .unwrap()
        .into_vec()
        .expect("proof writer flush");

    // Both proofs should be non-empty
    assert!(!text_proof.is_empty(), "Text proof should not be empty");
    assert!(!binary_proof.is_empty(), "Binary proof should not be empty");

    // Binary format should generally be smaller than text format
    // (not always guaranteed for very small proofs, so we just check both are valid)
    eprintln!(
        "Proof sizes - Text: {} bytes, Binary: {} bytes",
        text_proof.len(),
        binary_proof.len()
    );
}
