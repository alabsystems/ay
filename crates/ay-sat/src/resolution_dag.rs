// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In-memory, consumable CDCL refutation for the bit-blasted BV fragment.
//!
//! # Why this module exists
//!
//! `proof_manager.rs` already records the solver's refutation, but it only
//! *emits* it as an LRAT byte stream that is gated behind the file-emission and
//! external-checker authority handshakes (`LearnedLrat*`,
//! `validate_*_main_proof_authority`). There is no public, in-memory accessor
//! that returns the refutation as a resolution/RUP DAG a downstream zero-trust
//! reconstructor (`ay-proof`'s `bv_blast_export`) can replay.
//!
//! This module adds exactly that, **without** touching or weakening the
//! authority-gated LRAT path:
//!
//! * [`prove_unsat_resolution_dag`] drives a fresh [`Solver`] over a CNF with a
//!   plain in-memory LRAT text writer (`ProofOutput::lrat_text(Vec, n)`), solves
//!   it, and on UNSAT parses the emitted LRAT text into a [`ResolutionDag`].
//! * The plain LRAT writer path is the ordinary CDCL proof channel; it is *not*
//!   the `LearnedLrat*` materializer/authority channel, so no handshake is
//!   bypassed — that channel is for theory-lemma materialization and is left
//!   fully intact.
//!
//! # What is surfaced (honest scope)
//!
//! Each derived clause is surfaced as a [`RupStep`] carrying its **positive
//! RUP antecedent clause-ids** — the exact hint chain the LRAT line encodes.
//! This is precisely what a checker needs to re-derive the clause by reverse
//! unit propagation, and what `ay-proof` expands into pairwise resolution.
//!
//! What is deliberately **not** surfaced here (fail-closed):
//! * RAT steps (negative/signed hints): the BV bit-blast fragment is refuted by
//!   pure RUP, so any negative hint makes [`prove_unsat_resolution_dag`] return
//!   [`ResolutionDagError::RatStepUnsupported`] rather than emit something a
//!   pairwise-resolution consumer cannot check.
//! * Clause-deletion provenance and learned-clause materializer provenance:
//!   deletions are dropped (they do not affect soundness of a forward replay),
//!   and the theory-lemma materializer/authority records stay in
//!   `proof_manager.rs` untouched.

use crate::literal::Literal;
use crate::proof::ProofOutput;
use crate::solver::{SatResult, Solver};

/// One derived clause of the refutation together with the positive RUP
/// antecedent clause-ids the solver used to derive it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RupStep {
    /// LRAT clause id of this derived clause (unique, monotone, `> num_clauses`).
    pub id: u64,
    /// The derived clause literals.
    pub clause: Vec<Literal>,
    /// Positive RUP antecedent clause-ids (the LRAT hint chain), in order.
    pub rup_hints: Vec<u64>,
}

/// A consumable, in-memory CDCL refutation: the original clauses (with their
/// solver-assigned LRAT ids) plus the ordered list of derived RUP steps, the
/// last of which is the empty clause.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolutionDag {
    /// Number of Boolean variables.
    pub num_vars: usize,
    /// Original clauses paired with their LRAT id. Ids are `1..=clauses.len()`
    /// in input order (the LRAT convention the writer uses).
    pub original_clauses: Vec<(u64, Vec<Literal>)>,
    /// Derived clauses in derivation order; the final step is the empty clause.
    pub derived: Vec<RupStep>,
    /// LRAT id of the final (empty) derived clause.
    pub empty_clause_id: u64,
}

/// Failure modes for [`prove_unsat_resolution_dag`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ResolutionDagError {
    /// The CNF was satisfiable; there is no refutation to surface.
    #[error("formula is satisfiable: no refutation")]
    Satisfiable,
    /// The solver returned Unknown (resource limit / interruption).
    #[error("solver returned unknown; no refutation produced")]
    Unknown,
    /// The proof writer could not be recovered or flushed.
    #[error("proof writer unavailable or flush failed")]
    ProofWriterUnavailable,
    /// The emitted LRAT proof was not valid UTF-8 text.
    #[error("emitted LRAT proof is not UTF-8 text")]
    ProofNotUtf8,
    /// An LRAT line could not be parsed.
    #[error("malformed LRAT line: {0}")]
    MalformedLratLine(String),
    /// The proof used a RAT step (signed/negative hint), which this surfacing
    /// path intentionally does not lift (fail-closed; pure-RUP only).
    #[error("proof contains a RAT step (negative hint); not surfaced (RUP-only)")]
    RatStepUnsupported,
    /// The emitted proof did not end in the empty clause.
    #[error("emitted LRAT proof does not derive the empty clause")]
    NoEmptyClause,
}

/// Drive a fresh solver over `clauses` (over `num_vars` variables) with an
/// in-memory LRAT writer, and on UNSAT surface the refutation as a
/// [`ResolutionDag`].
///
/// This is the ungated, consumable accessor referenced in the module docs. It
/// uses the ordinary CDCL LRAT channel only; the authority-gated learned-LRAT
/// materializer path in `proof_manager.rs` is not involved.
///
/// # Errors
/// See [`ResolutionDagError`] — notably [`ResolutionDagError::Satisfiable`] when
/// the obligation is SAT (so no bogus refutation is produced) and
/// [`ResolutionDagError::RatStepUnsupported`] when the proof is not pure RUP.
pub fn prove_unsat_resolution_dag(
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> Result<ResolutionDag, ResolutionDagError> {
    let mut solver = Solver::with_proof_output(
        num_vars,
        ProofOutput::lrat_text(Vec::<u8>::new(), clauses.len() as u64),
    );
    // This API promises a directly consumable pure-RUP refutation.  Keep its
    // producer on the ordinary CDCL lane: preprocessing can perform
    // equisatisfiable transforms whose trust classification cannot be encoded
    // in LRAT, causing an otherwise valid UNSAT result to fail closed to
    // Unknown (or leaving a hint chain that is not a forward RUP derivation).
    // The formulas served here are already bit-blasted CNF, so preprocessing
    // is neither part of the contract nor required for completeness.
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }

    match solver.solve().into_inner() {
        SatResult::Unsat(_) => {}
        SatResult::Sat(_) => return Err(ResolutionDagError::Satisfiable),
        SatResult::Unknown => return Err(ResolutionDagError::Unknown),
    }

    let writer = solver
        .take_proof_writer()
        .ok_or(ResolutionDagError::ProofWriterUnavailable)?;
    let bytes = writer
        .into_vec()
        .map_err(|_| ResolutionDagError::ProofWriterUnavailable)?;
    let text = String::from_utf8(bytes).map_err(|_| ResolutionDagError::ProofNotUtf8)?;

    let original_clauses: Vec<(u64, Vec<Literal>)> = clauses
        .iter()
        .enumerate()
        .map(|(i, c)| (i as u64 + 1, c.clone()))
        .collect();

    parse_lrat_text_into_dag(num_vars, original_clauses, &text)
}

/// Parse plain-text LRAT into a [`ResolutionDag`].
///
/// The LRAT text grammar this consumes (the subset the writer emits):
///   `<id> <lit>* 0 <hint>* 0`      — clause addition (positive hints only here)
///   `<id> d <delid>* 0`            — clause deletion (dropped)
/// A deletion line is recognised by a `d` token in the first field after the id.
fn parse_lrat_text_into_dag(
    num_vars: usize,
    original_clauses: Vec<(u64, Vec<Literal>)>,
    text: &str,
) -> Result<ResolutionDag, ResolutionDagError> {
    let mut derived: Vec<RupStep> = Vec::new();

    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() {
            continue;
        }
        let mut toks = line.split_whitespace();
        let id: u64 = toks
            .next()
            .and_then(|t| t.parse().ok())
            .ok_or_else(|| ResolutionDagError::MalformedLratLine(line.to_string()))?;

        // Peek the next token: a literal/`0`, or the deletion marker `d`.
        let mut rest = toks.peekable();
        if rest.peek().copied() == Some("d") {
            // Deletion line: irrelevant to a forward resolution replay; drop it.
            continue;
        }

        // Clause literals up to the terminating 0.
        let mut clause: Vec<Literal> = Vec::new();
        for tok in rest.by_ref() {
            let v: i32 = tok
                .parse()
                .map_err(|_| ResolutionDagError::MalformedLratLine(line.to_string()))?;
            if v == 0 {
                break;
            }
            clause.push(Literal::from_dimacs(v));
        }

        // Hint chain up to the terminating 0. Negative hints = RAT (unsupported).
        let mut rup_hints: Vec<u64> = Vec::new();
        for tok in rest {
            let v: i64 = tok
                .parse()
                .map_err(|_| ResolutionDagError::MalformedLratLine(line.to_string()))?;
            if v == 0 {
                break;
            }
            if v < 0 {
                return Err(ResolutionDagError::RatStepUnsupported);
            }
            rup_hints.push(v as u64);
        }

        derived.push(RupStep {
            id,
            clause,
            rup_hints,
        });
    }

    let empty_clause_id = derived
        .iter()
        .rev()
        .find(|s| s.clause.is_empty())
        .map(|s| s.id)
        .ok_or(ResolutionDagError::NoEmptyClause)?;

    Ok(ResolutionDag {
        num_vars,
        original_clauses,
        derived,
        empty_clause_id,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn p(i: u32) -> Literal {
        Literal::positive(Variable::new(i))
    }
    fn n(i: u32) -> Literal {
        Literal::negative(Variable::new(i))
    }

    #[test]
    fn unsat_two_var_grid_surfaces_rup_dag() {
        let clauses = vec![
            vec![p(0), p(1)],
            vec![p(0), n(1)],
            vec![n(0), p(1)],
            vec![n(0), n(1)],
        ];
        let dag = prove_unsat_resolution_dag(2, &clauses).expect("unsat");
        assert_eq!(dag.original_clauses.len(), 4);
        assert_eq!(dag.original_clauses[0].0, 1);
        // Final derived clause is empty, with positive-only hints throughout.
        assert!(dag.derived.last().expect("steps").clause.is_empty());
        assert_eq!(dag.empty_clause_id, dag.derived.last().unwrap().id);
        for step in &dag.derived {
            assert!(step.id > 4, "derived ids namespaced after originals");
        }
    }

    #[test]
    fn sat_formula_yields_satisfiable_error() {
        let clauses = vec![vec![p(0), p(1)]];
        let err = prove_unsat_resolution_dag(2, &clauses).expect_err("sat");
        assert_eq!(err, ResolutionDagError::Satisfiable);
    }
}
