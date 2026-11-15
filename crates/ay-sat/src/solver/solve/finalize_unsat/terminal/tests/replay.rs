// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

/// Serialize the actual derived row order and IDs without reconstruction,
/// widening, repair or extra original premises.
pub(super) fn serialized(
    rows: &[(u64, Vec<Literal>, bool, Vec<u64>)],
    omit: Option<usize>,
) -> String {
    let mut proof = String::new();
    for (id, clause, original, hints) in rows {
        if *original {
            continue;
        }
        proof.push_str(&format!("{id} "));
        for lit in clause {
            proof.push_str(&format!("{} ", dimacs(*lit)));
        }
        proof.push_str("0 ");
        for (i, hint) in hints.iter().enumerate() {
            if !(clause.is_empty() && omit == Some(i)) {
                proof.push_str(&format!("{hint} "));
            }
        }
        proof.push_str("0\n");
    }
    proof
}

fn dimacs(lit: Literal) -> i64 {
    let var = lit.variable().index() as i64 + 1;
    if lit.is_positive() {
        var
    } else {
        -var
    }
}

pub(super) fn strict(original: &[Vec<Literal>], proof: &str) -> bool {
    let mut text = format!("p cnf 3 {}\n", original.len());
    for clause in original {
        for lit in clause {
            text.push_str(&format!("{} ", dimacs(*lit)));
        }
        text.push_str("0\n");
    }
    let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(text.as_bytes()).unwrap();
    let steps = ay_lrat_check::lrat_parser::parse_text_lrat(proof).unwrap();
    let mut checker = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);
    for (id, clause) in cnf.clauses {
        assert!(checker.add_original(id, &clause));
    }
    checker.verify_proof(&steps)
}
