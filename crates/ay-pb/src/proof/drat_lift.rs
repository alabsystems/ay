// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lift an ay-sat DRAT refutation into a VeriPB v3 proof of the original PB
//! instance's unsatisfiability — the general (non-bespoke) certified-UNSAT route
//! for the DEC-LIN-CERT track.
//!
//! Soundness model (see proofs/2026-06-17-pb-cert-drat-lift.md): we only ever
//! emit `rup` (reverse-unit-propagation) steps, which VeriPB *checks*; we never
//! emit an unchecked assertion. The whole proof is additionally re-checked with
//! the external VeriPB checker before any CERTIFIED claim is made (verify-before-
//! claim, in [`super::cert`]).
//!
//! AUX-FREE GATE (increment 1): a PB->CNF encoding may introduce auxiliary
//! (Tseitin / cardinality-counter) variables whose indices exceed `num_pb_vars`.
//! Those aux vars must first be *introduced* in the VeriPB database (via `red`,
//! a later increment). Until then, [`parse_aux_free_drat`] returns `None` if any
//! DRAT clause mentions a literal over an aux variable, so we simply decline to
//! certify rather than emit an unsound/unverifiable proof. The reported SAT/UNSAT
//! answer is unaffected — only the *certificate* is withheld.

use std::io::Write;

use super::steps::{ConstraintId, ProofStep};
use super::veripb::{Result, VeriPbWriter};

/// Parse DRAT-text bytes into the sequence of ADDED clauses (DIMACS signed
/// literals), dropping deletion (`d `) lines. Returns `None` (the aux-free gate)
/// if any literal references a variable index `> num_pb_vars`, i.e. an encoding
/// auxiliary variable not yet introduced in the VeriPB proof.
///
/// DRAT-text grammar (ay-sat `DratWriter`, drat.rs): an add line is space-
/// separated DIMACS i32 literals terminated by `0`; a delete line is prefixed
/// `d `. Literals are 1-indexed (`Literal::to_dimacs`).
pub fn parse_aux_free_drat(drat: &[u8], num_pb_vars: u32) -> Option<Vec<Vec<i32>>> {
    let text = std::str::from_utf8(drat).ok()?;
    let mut adds: Vec<Vec<i32>> = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        // Drop deletions (optional for soundness; they only shrink the DB).
        if line == "d" || line.starts_with("d ") {
            continue;
        }
        let mut clause: Vec<i32> = Vec::new();
        for tok in line.split_whitespace() {
            let lit: i32 = tok.parse().ok()?;
            if lit == 0 {
                break; // clause terminator
            }
            if lit.unsigned_abs() > num_pb_vars {
                return None; // aux-free gate: not 1:1 liftable yet
            }
            clause.push(lit);
        }
        adds.push(clause);
    }
    Some(adds)
}

/// Format a CNF clause (DIMACS signed literals) as a VeriPB RUP constraint body
/// `1 x{a} 1 ~x{b} ... >= 1 ;` (with the trailing semicolon `ProofStep::Rup`
/// expects). A clause `(a ∨ ¬b)` is exactly the PB constraint `a + (1-b) >= 1`.
/// The empty clause renders as `>= 1 ;` (an unsatisfiable RUP target).
fn rup_body(clause: &[i32]) -> String {
    let mut body = String::new();
    for &lit in clause {
        if lit > 0 {
            body.push_str(&format!("1 x{lit} "));
        } else {
            body.push_str(&format!("1 ~x{} ", -lit));
        }
    }
    body.push_str(">= 1 ;");
    body
}

/// Emit the lifted DRAT refutation as VeriPB `rup` steps, returning the
/// `ConstraintId` of the final (empty) clause to point the conclusion at, or
/// `Ok(None)` if the aux-free gate declined (an aux variable was present) or the
/// refutation contained no clauses (nothing to conclude from).
pub fn emit_decision_unsat_proof<W: Write>(
    writer: &mut VeriPbWriter<W>,
    drat: &[u8],
    num_pb_vars: u32,
) -> Result<Option<ConstraintId>> {
    let Some(adds) = parse_aux_free_drat(drat, num_pb_vars) else {
        return Ok(None);
    };
    let mut last: Option<ConstraintId> = None;
    for clause in &adds {
        let id = writer.log_step(ProofStep::Rup(rup_body(clause)))?;
        last = Some(id);
    }
    // A sound refutation must derive the empty clause; require the final lifted
    // clause to be empty so the conclusion points at a genuine contradiction.
    match adds.last() {
        Some(clause) if clause.is_empty() => Ok(last),
        _ => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aux_free_gate_rejects_aux_literals() {
        // num_pb_vars = 6; a literal over var 15 (aux) must trip the gate.
        assert!(parse_aux_free_drat(b"-15 0\n0\n", 6).is_none());
        // All literals within the PB range pass.
        let parsed = parse_aux_free_drat(b"1 -2 0\n0\n", 6).expect("aux-free");
        assert_eq!(parsed, vec![vec![1, -2], vec![]]);
    }

    #[test]
    fn deletions_are_dropped() {
        let parsed = parse_aux_free_drat(b"1 2 0\nd 1 2 0\n0\n", 3).expect("aux-free");
        assert_eq!(parsed, vec![vec![1, 2], vec![]]);
    }

    #[test]
    fn rup_body_formats_literals() {
        assert_eq!(rup_body(&[1, -2, 3]), "1 x1 1 ~x2 1 x3 >= 1 ;");
        assert_eq!(rup_body(&[]), ">= 1 ;");
    }
}
