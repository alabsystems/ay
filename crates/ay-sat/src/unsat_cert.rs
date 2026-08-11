// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Route-b in-memory UNSAT certificate API (feature `unsat-cert`).
//!
//! # Why this module exists (Program CK1, WS1-M1 "route (b)")
//!
//! external-codegen's t-silicon P3 lane certifies IR→machine lowering rules by
//! bit-blasting an IR-vs-machine miter to CNF with its **own** untrusted
//! blaster, recording a DRAT proof, and rechecking the refutation in
//! downstream proof consumer's verified `checkRefutes3`. The residual trust boundary is
//! *encoding fidelity*: that the blaster computed the rule's real semantics.
//! Route (b) closes it by solving the same CNF with **ay's** solver and
//! routing **ay's** proof through the same certificate, so an encoding bug
//! must exist identically in two independently written blasters to survive.
//!
//! This module is the consumable entry point for that bridge:
//!
//! * [`prove_cnf_unsat_dimacs`] — solve a caller-supplied CNF (DIMACS-signed
//!   literals, the interchange external-codegen's miter fixtures already speak) and
//!   return the solver's own refutation as an in-memory
//!   [`ResolutionDag`]: the original clause DB plus LRAT-style derivation
//!   steps ([`crate::RupStep`] — each derived clause with its positive
//!   unit-propagation hint ids), terminating at the empty clause. No file
//!   round-trip: the LRAT channel is an in-memory buffer end to end.
//! * [`ResolutionDag::validate`] — an independent, hint-driven RUP replay of
//!   the certificate (CaDiCaL `lratchecker.cpp` semantics). This is the
//!   tamper gate: a corrupted clause, hint, or truncated trace is refused
//!   with a typed [`ResolutionDagValidateError`].
//!
//! For bit-blasted BV queries the same channel is already plumbed one level
//! up: `ay-proof`'s `surface_bv_cnf_refutation` (production BV-solver CNF →
//! [`ResolutionDag`]) and `export_bv_blast_proof_expr` (BV expression
//! equality → structured `BvBlastProof`) both ride
//! [`prove_unsat_resolution_dag`].
//!
//! # Fail-closed posture
//!
//! Nothing here fabricates or trusts a proof:
//!
//! * a SAT formula yields [`ResolutionDagError::Satisfiable`];
//! * RAT steps (negative hints) are refused upstream by
//!   [`prove_unsat_resolution_dag`] ([`ResolutionDagError::RatStepUnsupported`]);
//! * unhinted "trusted transform" additions from inprocessing (which the
//!   lenient external checker registers as axioms) do **not** replay by RUP
//!   and are refused by [`ResolutionDag::validate`]
//!   ([`ResolutionDagValidateError::NoConflict`]) — a route-b consumer must
//!   never be handed a step the kernel cannot re-derive;
//! * [`prove_cnf_unsat_dimacs`] replays its own output before returning it,
//!   so a certificate that escapes this API has already survived the same
//!   check the consumer will run.

use crate::literal::Literal;
use crate::resolution_dag::{prove_unsat_resolution_dag, ResolutionDag, ResolutionDagError};
pub use crate::resolution_validate::ResolutionDagValidateError;

/// Errors from [`prove_cnf_unsat_dimacs`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum CnfCertError {
    /// A caller-supplied literal is zero (the DIMACS clause terminator) or
    /// names a variable outside `1..=num_vars`.
    #[error(
        "clause {clause_index}: literal {literal} is malformed \
         (zero, or variable outside 1..={num_vars})"
    )]
    MalformedLiteral {
        /// Index of the offending clause in the input slice.
        clause_index: usize,
        /// The offending DIMACS literal.
        literal: i32,
        /// Declared variable count.
        num_vars: usize,
    },
    /// Solving / proof surfacing failed (SAT formula, resource limit, RAT
    /// step, malformed emitted LRAT — see [`ResolutionDagError`]).
    #[error(transparent)]
    Solve(#[from] ResolutionDagError),
    /// The solver-emitted certificate failed the internal RUP replay. This
    /// should be unreachable for a healthy solver; it exists so the API is
    /// fail-closed rather than trusting its own output.
    #[error("solver-emitted certificate failed replay: {0}")]
    Invalid(#[from] ResolutionDagValidateError),
}

/// Solve a caller-supplied CNF to UNSAT and return the solver's refutation as
/// a validated, in-memory [`ResolutionDag`] (route-b entry point).
///
/// `clauses` use DIMACS-signed literals (`±v`, `1 <= v <= num_vars`, no `0`
/// terminator). On UNSAT the returned certificate carries the original clause
/// DB (LRAT ids `1..=n` in input order) and the LRAT-style derivation steps —
/// each derived clause with its positive unit-propagation hint ids — ending at
/// the empty clause. The certificate has already passed
/// [`ResolutionDag::validate`]; adversarial consumers should still re-run
/// `validate` (or their own checker) after any transport or mutation.
///
/// This is a proof-export entry point, **not** a hot solve path: proof
/// materialization is always on. Callers that only want a verdict should use
/// [`crate::Solver`] directly.
///
/// # Errors
/// * [`CnfCertError::MalformedLiteral`] — zero or out-of-range input literal.
/// * [`CnfCertError::Solve`] — SAT formula ([`ResolutionDagError::Satisfiable`]),
///   resource limit, RAT step, or unparseable emitted proof.
/// * [`CnfCertError::Invalid`] — the emitted certificate failed replay
///   (fail-closed; should be unreachable).
pub fn prove_cnf_unsat_dimacs(
    num_vars: usize,
    clauses: &[Vec<i32>],
) -> Result<ResolutionDag, CnfCertError> {
    let mut sat_clauses: Vec<Vec<Literal>> = Vec::with_capacity(clauses.len());
    for (clause_index, clause) in clauses.iter().enumerate() {
        let mut lits = Vec::with_capacity(clause.len());
        for &literal in clause {
            if literal == 0 || literal.unsigned_abs() as usize > num_vars {
                return Err(CnfCertError::MalformedLiteral {
                    clause_index,
                    literal,
                    num_vars,
                });
            }
            lits.push(Literal::from_dimacs(literal));
        }
        sat_clauses.push(lits);
    }

    let dag = prove_unsat_resolution_dag(num_vars, &sat_clauses)?;
    dag.validate()?;
    Ok(dag)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_lrat_check::checker::LratChecker;
    use ay_lrat_check::lrat_parser::LratStep;

    /// Pigeonhole CNF PHP(pigeons, holes): UNSAT whenever pigeons > holes.
    /// Var(p, h) = p * holes + h + 1 (DIMACS 1-based).
    fn php_cnf(pigeons: usize, holes: usize) -> (usize, Vec<Vec<i32>>) {
        let var = |p: usize, h: usize| -> i32 { (p * holes + h + 1) as i32 };
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        // Every pigeon sits in some hole.
        for p in 0..pigeons {
            clauses.push((0..holes).map(|h| var(p, h)).collect());
        }
        // No two pigeons share a hole.
        for h in 0..holes {
            for p1 in 0..pigeons {
                for p2 in (p1 + 1)..pigeons {
                    clauses.push(vec![-var(p1, h), -var(p2, h)]);
                }
            }
        }
        (pigeons * holes, clauses)
    }

    /// Cross-check a [`ResolutionDag`] with the standalone `ay-lrat-check`
    /// checker (independent implementation of the same LRAT semantics).
    fn lrat_check_verdict(dag: &ResolutionDag) -> bool {
        let conv = |l: &Literal| ay_lrat_check::dimacs::Literal::from_dimacs(l.to_dimacs());
        let mut checker = LratChecker::new(dag.num_vars);
        for (id, lits) in &dag.original_clauses {
            let lits: Vec<_> = lits.iter().map(conv).collect();
            assert!(checker.add_original(*id, &lits), "original {id} rejected");
        }
        let steps: Vec<LratStep> = dag
            .derived
            .iter()
            .map(|s| LratStep::Add {
                id: s.id,
                clause: s.clause.iter().map(conv).collect(),
                hints: s.rup_hints.iter().map(|&h| h as i64).collect(),
            })
            .collect();
        checker.verify_proof(&steps)
    }

    // ── Deliverable (a): export a structured proof and validate it. ──────────

    #[test]
    fn pigeonhole_cert_exports_and_validates() {
        let (num_vars, clauses) = php_cnf(4, 3);
        let dag = prove_cnf_unsat_dimacs(num_vars, &clauses).expect("PHP(4,3) is UNSAT");
        assert_eq!(dag.original_clauses.len(), clauses.len());
        assert_eq!(dag.num_vars, num_vars);
        let last = dag.derived.last().expect("has steps");
        assert!(last.clause.is_empty(), "terminates at the empty clause");
        assert_eq!(dag.empty_clause_id, last.id);
        // Every derived step carries its unit-propagation hint chain.
        assert!(dag.derived.iter().all(|s| !s.rup_hints.is_empty()));
        // Explicit re-validation (the API already validated once internally).
        dag.validate().expect("certificate replays");
    }

    #[test]
    fn certificate_cross_checked_by_ay_lrat_check() {
        let (num_vars, clauses) = php_cnf(4, 3);
        let dag = prove_cnf_unsat_dimacs(num_vars, &clauses).expect("UNSAT");
        assert!(
            lrat_check_verdict(&dag),
            "independent ay-lrat-check must accept the surfaced certificate"
        );
    }

    // A t-silicon-shaped lowering-miter certificate is exercised end to end
    // (validate + independent ay-lrat-check cross-check + overhead numbers)
    // in `tests/unsat_cert_overhead.rs`, which owns the miter generator.

    // ── Deliverable (b): tamper negatives. ───────────────────────────────────

    #[test]
    fn tampered_hint_is_refused() {
        let (num_vars, clauses) = php_cnf(4, 3);
        let mut dag = prove_cnf_unsat_dimacs(num_vars, &clauses).expect("UNSAT");
        // Drop the terminal (conflicting) hint of the final empty-clause step:
        // the surviving prefix only unit-propagates, so the replay must run out
        // of hints without a conflict. (Dropping a *prefix* hint is not a
        // guaranteed tamper: solver hint chains may carry redundant hints.)
        let last = dag.derived.last_mut().expect("steps");
        assert!(last.rup_hints.len() >= 2, "meaningful tamper target");
        last.rup_hints.pop();
        let err = dag.validate().expect_err("dropped hint must be refused");
        assert!(
            matches!(
                err,
                ResolutionDagValidateError::HintNotUnit { .. }
                    | ResolutionDagValidateError::NoConflict { .. }
            ),
            "unexpected error: {err:?}"
        );
        assert!(!lrat_check_verdict(&dag), "ay-lrat-check must also refuse");
    }

    #[test]
    fn tampered_derived_clause_is_refused() {
        let (num_vars, clauses) = php_cnf(4, 3);
        let mut dag = prove_cnf_unsat_dimacs(num_vars, &clauses).expect("UNSAT");
        // Flip the polarity of a literal in the first derived clause.
        let step = dag
            .derived
            .iter_mut()
            .find(|s| !s.clause.is_empty())
            .expect("a non-empty derived clause exists");
        step.clause[0] = step.clause[0].negated();
        assert!(
            dag.validate().is_err(),
            "corrupted derived clause must be refused"
        );
        assert!(!lrat_check_verdict(&dag), "ay-lrat-check must also refuse");
    }

    #[test]
    fn tampered_original_clause_is_refused() {
        let (num_vars, clauses) = php_cnf(4, 3);
        let mut dag = prove_cnf_unsat_dimacs(num_vars, &clauses).expect("UNSAT");
        // Corrupt the clause DB itself: flip a literal of an original clause.
        let (_, lits) = &mut dag.original_clauses[0];
        lits[0] = lits[0].negated();
        assert!(
            dag.validate().is_err(),
            "corrupted clause DB must be refused"
        );
    }

    #[test]
    fn truncated_trace_is_refused() {
        let (num_vars, clauses) = php_cnf(4, 3);
        let mut dag = prove_cnf_unsat_dimacs(num_vars, &clauses).expect("UNSAT");
        dag.derived.pop();
        let err = dag.validate().expect_err("truncated trace must be refused");
        assert!(
            matches!(
                err,
                ResolutionDagValidateError::FinalClauseNotEmpty { .. }
                    | ResolutionDagValidateError::NoSteps
            ),
            "unexpected error: {err:?}"
        );
    }

    // ── Fail-closed and input-validation paths. ──────────────────────────────

    #[test]
    fn sat_cnf_is_fail_closed() {
        let err = prove_cnf_unsat_dimacs(2, &[vec![1, 2]]).expect_err("SAT");
        assert_eq!(
            err,
            CnfCertError::Solve(ResolutionDagError::Satisfiable),
            "no certificate may be fabricated for a SAT formula"
        );
    }

    #[test]
    fn malformed_literals_rejected() {
        let err = prove_cnf_unsat_dimacs(2, &[vec![1, 0]]).expect_err("zero literal");
        assert!(matches!(
            err,
            CnfCertError::MalformedLiteral { literal: 0, .. }
        ));
        let err = prove_cnf_unsat_dimacs(2, &[vec![1, -3]]).expect_err("var out of range");
        assert!(matches!(
            err,
            CnfCertError::MalformedLiteral { literal: -3, .. }
        ));
    }

    // Deliverable (c), the proof-materialization overhead measurement, lives
    // in `tests/unsat_cert_overhead.rs` (an integration test): unit tests
    // compile the library with `cfg(test)`, which activates the internal
    // debug-only LRAT chain checker and grossly inflates the number.
}
