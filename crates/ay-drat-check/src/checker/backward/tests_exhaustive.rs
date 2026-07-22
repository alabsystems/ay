// Copyright 2026 Andrew Yates
// Exhaustive forward/backward parity tests for small formulas.
//
// Enumerates all non-empty subsets of 2-variable clauses (up to 4 clauses)
// and all 1-2 step proof sequences. For each (formula, proof) pair, verifies
// that the forward and backward checkers agree on accept/reject.
//
// Reference: #5260 acceptance criteria.

use super::*;
use crate::checker::test_helpers::lit;

/// All non-tautological clauses over 2 variables (width 1-2).
fn all_clauses_2var() -> Vec<Vec<Literal>> {
    vec![
        vec![lit(0, true)],                 // (a)
        vec![lit(0, false)],                // (~a)
        vec![lit(1, true)],                 // (b)
        vec![lit(1, false)],                // (~b)
        vec![lit(0, true), lit(1, true)],   // (a v b)
        vec![lit(0, true), lit(1, false)],  // (a v ~b)
        vec![lit(0, false), lit(1, true)],  // (~a v b)
        vec![lit(0, false), lit(1, false)], // (~a v ~b)
    ]
}

/// All possible proof step clauses: the 8 non-tautological clauses + empty.
fn all_proof_clauses_2var() -> Vec<Vec<Literal>> {
    let mut clauses = all_clauses_2var();
    clauses.push(vec![]); // empty clause
    clauses
}

/// Check forward/backward agreement for a single (formula, proof) pair.
/// Returns None if they agree, Some(description) if they disagree.
fn check_parity(clauses: &[Vec<Literal>], steps: &[ProofStep]) -> Option<String> {
    let mut fwd = DratChecker::new(2, false);
    let fwd_result = fwd.verify(clauses, steps);

    let mut bwd = BackwardChecker::new(2, false);
    let bwd_result = bwd.verify(clauses, steps);

    if fwd_result.is_ok() != bwd_result.is_ok() {
        let clause_strs: Vec<String> = clauses
            .iter()
            .map(|c| {
                let lits: Vec<i32> = c.iter().map(|l| l.to_dimacs()).collect();
                format!("{lits:?}")
            })
            .collect();
        let step_strs: Vec<String> = steps
            .iter()
            .map(|s| match s {
                ProofStep::Add(c) => {
                    let lits: Vec<i32> = c.iter().map(|l| l.to_dimacs()).collect();
                    format!("Add({lits:?})")
                }
                ProofStep::Delete(c) => {
                    let lits: Vec<i32> = c.iter().map(|l| l.to_dimacs()).collect();
                    format!("Del({lits:?})")
                }
                ProofStep::AddPr { clause, witness } => {
                    let c: Vec<i32> = clause.iter().map(|l| l.to_dimacs()).collect();
                    let w: Vec<i32> = witness.iter().map(|l| l.to_dimacs()).collect();
                    format!("AddPr({c:?}; {w:?})")
                }
            })
            .collect();
        Some(format!(
            "PARITY MISMATCH: clauses={clause_strs:?} steps={step_strs:?} \
             fwd={fwd_result:?} bwd={bwd_result:?}"
        ))
    } else {
        None
    }
}

/// Exhaustive 2-variable enumeration: all formula subsets (1-4 clauses) x
/// all 1-step proof sequences. Tests forward/backward agreement.
#[test]
fn test_exhaustive_2var_1step() {
    let all_clauses = all_clauses_2var();
    let proof_clauses = all_proof_clauses_2var();
    let mut tested = 0u64;
    let mut mismatches = Vec::new();

    // Enumerate all non-empty subsets of clauses with 1-4 elements.
    let n = all_clauses.len(); // 8
    for mask in 1u32..(1 << n) {
        if mask.count_ones() > 4 {
            continue;
        }
        let formula: Vec<Vec<Literal>> = (0..n)
            .filter(|&i| mask & (1 << i) != 0)
            .map(|i| all_clauses[i].clone())
            .collect();

        // 1-step proofs: Add each possible clause.
        for pc in &proof_clauses {
            let steps = vec![ProofStep::Add(pc.clone())];
            if let Some(msg) = check_parity(&formula, &steps) {
                mismatches.push(msg);
            }
            tested += 1;
        }
    }

    assert!(
        mismatches.is_empty(),
        "Forward/backward parity violations ({tested} tested):\n{}",
        mismatches.join("\n")
    );
}

/// Exhaustive 2-variable enumeration: all formula subsets (1-3 clauses) x
/// all 2-step proof sequences. Tests forward/backward agreement.
#[test]
fn test_exhaustive_2var_2step() {
    let all_clauses = all_clauses_2var();
    let proof_clauses = all_proof_clauses_2var();
    let mut tested = 0u64;
    let mut mismatches = Vec::new();

    let n = all_clauses.len(); // 8
    for mask in 1u32..(1 << n) {
        if mask.count_ones() > 3 {
            continue;
        }
        let formula: Vec<Vec<Literal>> = (0..n)
            .filter(|&i| mask & (1 << i) != 0)
            .map(|i| all_clauses[i].clone())
            .collect();

        // 2-step proofs: Add x Add.
        for pc1 in &proof_clauses {
            for pc2 in &proof_clauses {
                let steps = vec![ProofStep::Add(pc1.clone()), ProofStep::Add(pc2.clone())];
                if let Some(msg) = check_parity(&formula, &steps) {
                    mismatches.push(msg);
                }
                tested += 1;
            }
        }
    }

    assert!(
        mismatches.is_empty(),
        "Forward/backward parity violations ({tested} tested):\n{}",
        mismatches.join("\n")
    );
}

/// Exhaustive 2-variable enumeration: all formula subsets (1-2 clauses) x
/// all 3-step proof sequences. Tests forward/backward agreement.
#[test]
fn test_exhaustive_2var_3step() {
    let all_clauses = all_clauses_2var();
    let proof_clauses = all_proof_clauses_2var();
    let mut tested = 0u64;
    let mut mismatches = Vec::new();

    let n = all_clauses.len(); // 8
    for mask in 1u32..(1 << n) {
        if mask.count_ones() > 2 {
            continue;
        }
        let formula: Vec<Vec<Literal>> = (0..n)
            .filter(|&i| mask & (1 << i) != 0)
            .map(|i| all_clauses[i].clone())
            .collect();

        // 3-step proofs: Add x Add x Add.
        for pc1 in &proof_clauses {
            for pc2 in &proof_clauses {
                for pc3 in &proof_clauses {
                    let steps = vec![
                        ProofStep::Add(pc1.clone()),
                        ProofStep::Add(pc2.clone()),
                        ProofStep::Add(pc3.clone()),
                    ];
                    if let Some(msg) = check_parity(&formula, &steps) {
                        mismatches.push(msg);
                    }
                    tested += 1;
                }
            }
        }
    }

    assert!(
        mismatches.is_empty(),
        "Forward/backward parity violations ({tested} tested):\n{}",
        mismatches.join("\n")
    );
}
