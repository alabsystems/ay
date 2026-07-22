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

/// Errors from [`ResolutionDag::validate`] — each names the first defect found
/// in a certificate that does not replay.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ResolutionDagValidateError {
    /// An original clause's LRAT id is not its 1-based input position (the
    /// convention [`prove_unsat_resolution_dag`] guarantees).
    #[error("original clause at index {index} has id {id}, expected {expected}")]
    NonCanonicalOriginalId {
        /// Position in `original_clauses`.
        index: usize,
        /// Recorded LRAT id.
        id: u64,
        /// Expected id (`index + 1`).
        expected: u64,
    },
    /// A literal references a variable outside `0..num_vars`.
    #[error("clause id {clause}: variable index {var} out of range (num_vars {num_vars})")]
    VarOutOfRange {
        /// LRAT id of the offending clause.
        clause: u64,
        /// Variable index seen.
        var: usize,
        /// Declared variable count.
        num_vars: usize,
    },
    /// A derived step's id does not strictly increase (CaDiCaL parity: LRAT
    /// clause ids are strictly monotone).
    #[error("derived step id {id} not strictly greater than previous id {prev}")]
    NonMonotoneStepId {
        /// Offending step id.
        id: u64,
        /// Highest id seen before it.
        prev: u64,
    },
    /// A hint names no clause known at that point (missing, deleted from the
    /// surfaced DB, or a forward reference).
    #[error("step {step}: hint {hint} names no known clause")]
    UnknownHint {
        /// Derived step id.
        step: u64,
        /// Offending hint id.
        hint: u64,
    },
    /// Under the negated-clause assumption a hint clause had two or more
    /// non-falsified literals — it neither propagates nor conflicts, so the
    /// chain is not a valid LRAT certificate (CaDiCaL parity).
    #[error("step {step}: hint {hint} is not unit under the current assignment")]
    HintNotUnit {
        /// Derived step id.
        step: u64,
        /// Offending hint id.
        hint: u64,
    },
    /// The hint chain ran out without reaching a conflict: the derived clause
    /// is not RUP from its hints. This also refuses unhinted ("trusted
    /// transform") additions — fail-closed, they cannot be kernel-re-derived.
    #[error("step {step}: hint chain exhausted without conflict (clause not RUP from its hints)")]
    NoConflict {
        /// Derived step id.
        step: u64,
    },
    /// The refutation carries no derived steps at all.
    #[error("refutation has no derived steps")]
    NoSteps,
    /// The final derived clause is not the empty clause.
    #[error("final derived clause is not empty (has {len} literals)")]
    FinalClauseNotEmpty {
        /// Literal count of the final clause.
        len: usize,
    },
    /// The recorded `empty_clause_id` does not name the final (empty) step.
    #[error("recorded empty_clause_id {recorded} does not match final step id {actual}")]
    EmptyClauseIdMismatch {
        /// The id recorded on the [`ResolutionDag`].
        recorded: u64,
        /// The actual final step id.
        actual: u64,
    },
}

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

/// Outcome of scanning one hint clause during RUP replay.
enum HintScan {
    /// Every literal falsified — conflict, the step is verified.
    Conflict,
    /// Exactly one non-falsified literal, unassigned — propagate it.
    Propagate(Literal),
    /// Exactly one non-falsified literal, already true — no-op.
    SatisfiedUnit,
    /// Two or more non-falsified literals — invalid hint.
    NonUnit,
}

impl ResolutionDag {
    /// Replay the certificate and confirm it is a well-formed LRAT/RUP
    /// refutation of `original_clauses`.
    ///
    /// Checks, in order: canonical original ids (`1..=n`), variable ranges,
    /// strictly monotone derived ids, and — for every derived step — that
    /// assuming the negation of its clause and unit-propagating its hints in
    /// order reaches a conflict, with every hint either propagating exactly
    /// one literal, being an already-satisfied unit, or conflicting (CaDiCaL
    /// `lratchecker.cpp` hint classification). Finally the last step must be
    /// the empty clause and match [`ResolutionDag::empty_clause_id`].
    ///
    /// A tautological derived clause (containing `l` and `¬l`) is accepted
    /// without consulting hints: it is entailed by anything, so admitting it
    /// cannot make an unsatisfiable clause set appear satisfiable (and the
    /// final step, being empty, can never be tautological).
    ///
    /// This is the in-tree tamper gate for route-b consumers: any corrupted
    /// clause literal, corrupted/dropped hint, or truncated trace fails with
    /// a typed error.
    ///
    /// # Errors
    /// Returns the first [`ResolutionDagValidateError`] encountered.
    pub fn validate(&self) -> Result<(), ResolutionDagValidateError> {
        use std::collections::HashMap;

        let check_lits =
            |clause_id: u64, lits: &[Literal]| -> Result<(), ResolutionDagValidateError> {
                for lit in lits {
                    let var = lit.variable().index();
                    if var >= self.num_vars {
                        return Err(ResolutionDagValidateError::VarOutOfRange {
                            clause: clause_id,
                            var,
                            num_vars: self.num_vars,
                        });
                    }
                }
                Ok(())
            };

        // 1. Original clause DB: canonical dense ids, in-range literals.
        let mut db: HashMap<u64, &[Literal]> =
            HashMap::with_capacity(self.original_clauses.len() + self.derived.len());
        for (index, (id, lits)) in self.original_clauses.iter().enumerate() {
            let expected = index as u64 + 1;
            if *id != expected {
                return Err(ResolutionDagValidateError::NonCanonicalOriginalId {
                    index,
                    id: *id,
                    expected,
                });
            }
            check_lits(*id, lits)?;
            db.insert(*id, lits.as_slice());
        }

        // 2. Derived steps: monotone ids + hint-driven RUP replay.
        //    `assign[var]`: current truth value under the step's assumption.
        //    A trail records assignments for O(step) undo.
        let mut last_id = self.original_clauses.len() as u64;
        let mut assign: Vec<Option<bool>> = vec![None; self.num_vars];
        let mut trail: Vec<usize> = Vec::new();
        for step in &self.derived {
            if step.id <= last_id {
                return Err(ResolutionDagValidateError::NonMonotoneStepId {
                    id: step.id,
                    prev: last_id,
                });
            }
            check_lits(step.id, &step.clause)?;

            let result = replay_rup(step, &db, &mut assign, &mut trail);
            for &var in &trail {
                assign[var] = None;
            }
            trail.clear();
            result?;

            db.insert(step.id, step.clause.as_slice());
            last_id = step.id;
        }

        // 3. The refutation must end at the empty clause, and the recorded
        //    empty-clause id must name it.
        let Some(last) = self.derived.last() else {
            return Err(ResolutionDagValidateError::NoSteps);
        };
        if !last.clause.is_empty() {
            return Err(ResolutionDagValidateError::FinalClauseNotEmpty {
                len: last.clause.len(),
            });
        }
        if self.empty_clause_id != last.id {
            return Err(ResolutionDagValidateError::EmptyClauseIdMismatch {
                recorded: self.empty_clause_id,
                actual: last.id,
            });
        }
        Ok(())
    }
}

/// Replay one derived step by RUP over its hint chain. `assign`/`trail` are
/// caller-owned scratch (caller undoes the trail afterwards, success or fail).
fn replay_rup(
    step: &crate::resolution_dag::RupStep,
    db: &std::collections::HashMap<u64, &[Literal]>,
    assign: &mut [Option<bool>],
    trail: &mut Vec<usize>,
) -> Result<(), ResolutionDagValidateError> {
    // Assume the negation of the derived clause.
    for lit in &step.clause {
        let var = lit.variable().index();
        let forced = !lit.is_positive(); // ¬lit is true
        match assign[var] {
            None => {
                assign[var] = Some(forced);
                trail.push(var);
            }
            Some(v) if v == forced => {} // duplicate literal
            Some(_) => {
                // The clause contains l and ¬l: a tautology, entailed by
                // anything. Accept without hints (sound; see `validate` docs).
                return Ok(());
            }
        }
    }

    // Walk the hint chain: every hint must be a no-op satisfied unit, a unit
    // propagation, or the terminal conflict.
    for &hint in &step.rup_hints {
        let Some(hint_clause) = db.get(&hint) else {
            return Err(ResolutionDagValidateError::UnknownHint {
                step: step.id,
                hint,
            });
        };
        match scan_hint(hint_clause, assign) {
            HintScan::Conflict => return Ok(()),
            HintScan::Propagate(lit) => {
                let var = lit.variable().index();
                assign[var] = Some(lit.is_positive());
                trail.push(var);
            }
            HintScan::SatisfiedUnit => {}
            HintScan::NonUnit => {
                return Err(ResolutionDagValidateError::HintNotUnit {
                    step: step.id,
                    hint,
                });
            }
        }
    }
    Err(ResolutionDagValidateError::NoConflict { step: step.id })
}

/// Classify a hint clause under the current assignment (CaDiCaL parity: at
/// most one non-falsified literal is allowed).
fn scan_hint(clause: &[Literal], assign: &[Option<bool>]) -> HintScan {
    let mut non_falsified: Option<(Literal, bool)> = None; // (lit, is_satisfied)
    for &lit in clause {
        let truth = assign[lit.variable().index()].map(|v| v == lit.is_positive());
        match truth {
            Some(false) => {} // falsified
            Some(true) | None => {
                if non_falsified.is_some() {
                    return HintScan::NonUnit;
                }
                non_falsified = Some((lit, truth == Some(true)));
            }
        }
    }
    match non_falsified {
        None => HintScan::Conflict,
        Some((_, true)) => HintScan::SatisfiedUnit,
        Some((lit, false)) => HintScan::Propagate(lit),
    }
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
