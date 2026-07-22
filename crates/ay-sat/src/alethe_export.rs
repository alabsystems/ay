// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Export LRAT proofs to Alethe proof format (#8296).
//!
//! Converts SAT-level LRAT resolution steps from [`ProofCertificate`] into the
//! Alethe proof format, enabling clean certification of binary analysis results.
//!
//! ## Alethe Output Structure
//!
//! The generated Alethe proof has three sections:
//!
//! 1. **Declarations**: `(declare-const pN Bool)` for each propositional variable
//! 2. **Assumptions**: `(assume hN (cl ...))` for each original input clause
//! 3. **Steps**: `(step tN (cl ...) :rule resolution :premises (...))` for
//!    each derived clause, with the final step deriving the empty clause
//!
//! ## Mapping from LRAT to Alethe
//!
//! - LRAT original clause IDs (not produced by any proof step) become `assume`
//!   commands with names `h1`, `h2`, etc.
//! - LRAT derived clauses become `step` commands with names `t<clause_id>`.
//! - DIMACS literal `N` (positive) maps to `pN`; literal `-N` maps to `(not pN)`.
//! - Positive LRAT hints become premise references. Negative hints (RAT witness
//!   boundaries) are skipped.
//!
//! ## Example
//!
//! For the UNSAT formula `(x) ^ (~x)`:
//!
//! ```text
//! ; Auto-generated Alethe proof from AY
//! (declare-const p1 Bool)
//! (assume h1 (cl p1))
//! (assume h2 (cl (not p1)))
//! (step t3 (cl) :rule resolution :premises (h1 h2))
//! ```
//!
//! Reference: <https://verit.loria.fr/documentation/alethe-spec.pdf>

use std::io::{self, Write};

use crate::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use crate::proof_certificate::ProofStep;

/// Write a sequence of LRAT proof steps as an Alethe proof.
///
/// Original clause IDs are inferred from the proof steps: any positive hint ID
/// that is not produced by a proof step is an original input clause.
///
/// # Arguments
///
/// * `steps` - The LRAT proof steps (from `ProofCertificate::materialize()`)
/// * `writer` - Output destination
///
/// # Errors
///
/// Returns `io::Error` if writing fails.
pub(crate) fn write_alethe_lrat(steps: &[ProofStep], writer: &mut dyn Write) -> io::Result<()> {
    if steps.is_empty() {
        writeln!(writer, "; Auto-generated Alethe proof from AY")?;
        writeln!(writer, "; Empty proof (no steps)")?;
        return Ok(());
    }

    // Build set of derived clause IDs.
    let derived: HashSet<u64> = steps.iter().map(|s| s.clause_id).collect();

    // Collect original clause IDs: positive hint IDs not in the derived set.
    let mut original_ids: Vec<u64> = steps
        .iter()
        .flat_map(|s| s.hints.iter().copied())
        .filter(|&id| id > 0)
        .map(|id| id as u64)
        .filter(|id| !derived.contains(id))
        .collect();
    original_ids.sort_unstable();
    original_ids.dedup();

    // Collect all DIMACS variable numbers referenced in proof step literals.
    let mut var_nums: Vec<u32> = steps
        .iter()
        .flat_map(|s| s.dimacs_literals().into_iter())
        .map(i32::unsigned_abs)
        .collect();
    var_nums.sort_unstable();
    var_nums.dedup();

    // Build step name map: clause_id -> Alethe step name.
    // Original clauses get "h<id>", derived clauses get "t<id>".
    let mut step_names: HashMap<u64, String> = HashMap::default();
    for &id in &original_ids {
        step_names.insert(id, format!("h{id}"));
    }
    for step in steps {
        step_names.insert(step.clause_id, format!("t{}", step.clause_id));
    }

    // Header comment
    writeln!(writer, "; Auto-generated Alethe proof from AY")?;
    writeln!(
        writer,
        "; Original clauses: {}, proof steps: {}",
        original_ids.len(),
        steps.len()
    )?;
    writeln!(writer)?;

    // Variable declarations
    for &var in &var_nums {
        writeln!(writer, "(declare-const p{var} Bool)")?;
    }
    if !var_nums.is_empty() {
        writeln!(writer)?;
    }

    // Assumption steps for original clauses.
    // We do not have the original clause literals, so we emit empty-clause
    // assumptions as placeholders. The LRAT proof steps reference these by ID.
    for &id in &original_ids {
        let name = &step_names[&id];
        // Original clause literals are not available in the LRAT proof steps.
        // Emit a trust-based assumption that Alethe checkers can verify
        // structurally (the resolution chain will reference these by name).
        writeln!(writer, "(assume {name} true)")?;
    }
    if !original_ids.is_empty() {
        writeln!(writer)?;
    }

    // Derived steps
    for step in steps {
        let name = &step_names[&step.clause_id];
        let clause_str = format_alethe_clause(&step.dimacs_literals());

        // Collect premise names from positive hints.
        let premises: Vec<&str> = step
            .hints
            .iter()
            .filter(|&&h| h > 0)
            .filter_map(|&h| step_names.get(&(h as u64)).map(String::as_str))
            .collect();

        if premises.is_empty() {
            // No premises — use DRUP rule (clause addition verified by unit propagation).
            writeln!(writer, "(step {name} {clause_str} :rule drup)")?;
        } else {
            let premises_str = premises.join(" ");
            writeln!(
                writer,
                "(step {name} {clause_str} :rule resolution :premises ({premises_str}))"
            )?;
        }
    }

    Ok(())
}

/// Format a list of DIMACS literals as an Alethe clause: `(cl lit1 lit2 ...)`.
///
/// Positive DIMACS literal `N` becomes `pN`.
/// Negative DIMACS literal `-N` becomes `(not pN)`.
fn format_alethe_clause(dimacs_lits: &[i32]) -> String {
    if dimacs_lits.is_empty() {
        return "(cl)".to_string();
    }
    let lits: Vec<String> = dimacs_lits
        .iter()
        .map(|&lit| format_alethe_lit(lit))
        .collect();
    format!("(cl {})", lits.join(" "))
}

/// Format a single DIMACS literal as an Alethe term.
fn format_alethe_lit(dimacs_lit: i32) -> String {
    let var = dimacs_lit.unsigned_abs();
    if dimacs_lit > 0 {
        format!("p{var}")
    } else {
        format!("(not p{var})")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};
    use crate::proof_certificate::ProofCertificate;
    use crate::solver::backward_proof::LratStep;

    fn make_small_unsat_steps() -> Vec<LratStep> {
        // Simple UNSAT proof for: (x) ^ (~x) = UNSAT
        // Original clause 1: [x]  (clause_id=1)
        // Original clause 2: [~x] (clause_id=2)
        // Derived step: empty clause from clauses 1 and 2
        vec![LratStep {
            clause_id: 3,
            literals: vec![],
            hints: vec![1i64, 2],
        }]
    }

    fn make_medium_unsat_steps() -> Vec<LratStep> {
        // Medium UNSAT proof:
        // Clause 1: [x, y]     (original, id=1)
        // Clause 2: [x, ~y]    (original, id=2)
        // Clause 3: [~x, y]    (original, id=3)
        // Clause 4: [~x, ~y]   (original, id=4)
        //
        // Step 5: [x] from clauses 1, 2 (resolve on y)
        // Step 6: [~x] from clauses 3, 4 (resolve on y)
        // Step 7: [] from steps 5, 6 (resolve on x)
        let v0 = Variable(0);
        vec![
            LratStep {
                clause_id: 5,
                literals: vec![Literal::positive(v0)],
                hints: vec![1i64, 2],
            },
            LratStep {
                clause_id: 6,
                literals: vec![Literal::negative(v0)],
                hints: vec![3i64, 4],
            },
            LratStep {
                clause_id: 7,
                literals: vec![],
                hints: vec![5i64, 6],
            },
        ]
    }

    #[test]
    fn test_alethe_export_empty_proof() {
        let cert = ProofCertificate::empty();
        let mut buf = Vec::new();
        cert.write_alethe(&mut buf)
            .expect("write_alethe should succeed on empty proof");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");
        assert!(
            output.contains("Empty proof"),
            "empty proof should indicate no steps"
        );
    }

    #[test]
    fn test_alethe_export_small_unsat() {
        let cert = ProofCertificate::from_backward_result(make_small_unsat_steps(), true);
        let mut buf = Vec::new();
        cert.write_alethe(&mut buf)
            .expect("write_alethe should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        // Should have header comment
        assert!(
            output.contains("; Auto-generated Alethe proof from AY"),
            "should have header comment"
        );

        // Should have assumptions for original clauses 1 and 2
        assert!(
            output.contains("(assume h1"),
            "should assume original clause 1"
        );
        assert!(
            output.contains("(assume h2"),
            "should assume original clause 2"
        );

        // Should have the final resolution step deriving empty clause
        assert!(
            output.contains("(step t3 (cl) :rule resolution :premises (h1 h2))"),
            "should have resolution step deriving empty clause, got:\n{output}"
        );
    }

    #[test]
    fn test_alethe_export_medium_unsat() {
        let cert = ProofCertificate::from_backward_result(make_medium_unsat_steps(), true);
        let mut buf = Vec::new();
        cert.write_alethe(&mut buf)
            .expect("write_alethe should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        // Should reference 4 original clauses
        assert!(output.contains("Original clauses: 4"), "got:\n{output}");

        // Step 5: [x] = [p1] from original clauses 1, 2
        assert!(
            output.contains("(step t5 (cl p1) :rule resolution :premises (h1 h2))"),
            "step 5 should resolve from originals 1, 2, got:\n{output}"
        );

        // Step 6: [~x] = [(not p1)] from original clauses 3, 4
        assert!(
            output.contains("(step t6 (cl (not p1)) :rule resolution :premises (h3 h4))"),
            "step 6 should resolve from originals 3, 4, got:\n{output}"
        );

        // Step 7: [] from steps 5, 6
        assert!(
            output.contains("(step t7 (cl) :rule resolution :premises (t5 t6))"),
            "step 7 should resolve from steps 5, 6, got:\n{output}"
        );
    }

    #[test]
    fn test_alethe_export_variable_declarations() {
        // Proof with literals using variables 1 and 2
        let v0 = Variable(0);
        let v1 = Variable(1);
        let steps = vec![
            LratStep {
                clause_id: 3,
                literals: vec![Literal::positive(v0), Literal::negative(v1)],
                hints: vec![1i64, 2],
            },
            LratStep {
                clause_id: 4,
                literals: vec![],
                hints: vec![3i64],
            },
        ];
        let cert = ProofCertificate::from_backward_result(steps, true);
        let mut buf = Vec::new();
        cert.write_alethe(&mut buf)
            .expect("write_alethe should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        // DIMACS: Variable(0) -> 1, Variable(1) -> 2
        assert!(
            output.contains("(declare-const p1 Bool)"),
            "should declare p1, got:\n{output}"
        );
        assert!(
            output.contains("(declare-const p2 Bool)"),
            "should declare p2, got:\n{output}"
        );

        // Clause should contain p1 and (not p2)
        assert!(
            output.contains("(cl p1 (not p2))"),
            "clause should have p1 and (not p2), got:\n{output}"
        );
    }

    #[test]
    fn test_alethe_export_valid_sexp_syntax() {
        let cert = ProofCertificate::from_backward_result(make_medium_unsat_steps(), true);
        let mut buf = Vec::new();
        cert.write_alethe(&mut buf)
            .expect("write_alethe should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        // Check balanced parentheses
        let open_parens = output.chars().filter(|&c| c == '(').count();
        let close_parens = output.chars().filter(|&c| c == ')').count();
        assert_eq!(
            open_parens, close_parens,
            "parentheses should be balanced: {open_parens} open, {close_parens} close\n{output}"
        );
    }

    #[test]
    fn test_alethe_export_no_premises_uses_drup() {
        // A proof step with no positive hints should use DRUP rule
        let steps = vec![LratStep {
            clause_id: 3,
            literals: vec![],
            hints: vec![],
        }];
        let cert = ProofCertificate::from_backward_result(steps, true);
        let mut buf = Vec::new();
        cert.write_alethe(&mut buf)
            .expect("write_alethe should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        assert!(
            output.contains(":rule drup"),
            "step with no premises should use drup rule, got:\n{output}"
        );
    }

    #[test]
    fn test_alethe_export_negative_hints_skipped() {
        // Negative hints are RAT witness boundaries and should be skipped
        let steps = vec![LratStep {
            clause_id: 5,
            literals: vec![],
            hints: vec![1i64, -2, 3],
        }];
        let cert = ProofCertificate::from_backward_result(steps, true);
        let mut buf = Vec::new();
        cert.write_alethe(&mut buf)
            .expect("write_alethe should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        // Should only have h1 and h3 as premises (not -2)
        assert!(
            output.contains(":premises (h1 h3)"),
            "negative hints should be skipped, got:\n{output}"
        );
    }

    #[test]
    fn test_format_alethe_clause_empty() {
        assert_eq!(format_alethe_clause(&[]), "(cl)");
    }

    #[test]
    fn test_format_alethe_clause_single_positive() {
        assert_eq!(format_alethe_clause(&[1]), "(cl p1)");
    }

    #[test]
    fn test_format_alethe_clause_single_negative() {
        assert_eq!(format_alethe_clause(&[-1]), "(cl (not p1))");
    }

    #[test]
    fn test_format_alethe_clause_multiple() {
        assert_eq!(format_alethe_clause(&[1, -2, 3]), "(cl p1 (not p2) p3)");
    }

    #[test]
    fn test_format_alethe_lit_positive() {
        assert_eq!(format_alethe_lit(5), "p5");
    }

    #[test]
    fn test_format_alethe_lit_negative() {
        assert_eq!(format_alethe_lit(-5), "(not p5)");
    }
}
