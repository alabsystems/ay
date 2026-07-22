// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Deterministic proof replay for SAT certificates.
//!
//! Given an LRAT proof and the originating CNF clauses, re-validate the proof
//! via [`ay_lrat_check::checker::LratChecker`] and report a
//! [`ReplayOutcome`].
//!
//! The [`drat`] module also provides sequential DRAT replay.
//! Takes a solver-emitted DRAT proof plus the originating DIMACS and walks
//! the proof linearly with **RUP-only** checks (no RAT fallback). This is
//! deliberately a strict subset of DRAT; proofs that require RAT are rejected.
//! See benchmarks in
//! `crates/ay-replay/src/drat/tests.rs` for the fresh-solve-vs-replay
//! wall-clock comparison on PHP(3,2).
//!
//! # Usage
//!
//! ```no_run
//! use ay_replay::{DeterministicReplayer, ProofReplayer, ReplayInput, ReplayOutcome};
//!
//! // Minimal UNSAT CNF: (x) and (-x).
//! let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
//! // LRAT proof: clause 3 = empty, resolving 1 and 2.
//! let proof = b"3 0 1 2 0\n";
//!
//! let mut replayer = DeterministicReplayer::new();
//! let plan = replayer.load_lrat(&ReplayInput { cnf, proof }).expect("valid LRAT");
//! let outcome = replayer.replay(&plan);
//! assert!(matches!(outcome, ReplayOutcome::Success { .. }));
//! ```

pub mod drat;

use std::fmt;

use ay_lrat_check::checker::{LratChecker, Stats};
use ay_lrat_check::dimacs::{parse_cnf_with_ids, CnfFormulaWithIds, Literal};
use ay_lrat_check::lrat_parser::{
    is_binary_lrat, parse_binary_lrat, parse_text_lrat, LratParseError, LratStep,
};
use ay_proof_common::ParseError as CommonParseError;
use thiserror::Error;

/// Input to the replayer: originating CNF plus the LRAT proof to replay.
///
/// Both fields are borrowed byte slices so callers can stream them from disk
/// or memory without forcing an extra copy. The CNF is required because LRAT
/// is a *delta* over an input clause set — original clause IDs are referenced
/// by hints in the proof.
#[derive(Debug, Clone, Copy)]
pub struct ReplayInput<'a> {
    /// DIMACS CNF bytes (the formula that produced the proof).
    pub cnf: &'a [u8],
    /// LRAT proof bytes. Text or binary format is auto-detected via
    /// [`is_binary_lrat`].
    pub proof: &'a [u8],
}

/// A parsed, ready-to-replay proof plan.
///
/// The field set is `#[non_exhaustive]` so replay metadata can grow without
/// breaking callers.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ReplayPlan {
    /// DIMACS variable count parsed from the CNF header.
    pub num_vars: usize,
    /// Original CNF clauses, keyed by the LRAT clause IDs that correspond to
    /// them. LRAT uses `1..=num_clauses` for originals.
    pub originals: Vec<(u64, Vec<Literal>)>,
    /// Parsed LRAT step sequence in proof order.
    pub steps: Vec<LratStep>,
    /// Whether the input was a binary LRAT stream (informational).
    pub binary: bool,
}

impl ReplayPlan {
    /// Number of LRAT steps in the plan (add + delete).
    #[must_use]
    pub fn step_count(&self) -> usize {
        self.steps.len()
    }

    /// Number of `add` (derivation) steps — an upper bound on unique derived
    /// clause IDs the proof introduces.
    #[must_use]
    pub fn add_step_count(&self) -> usize {
        self.steps
            .iter()
            .filter(|s| matches!(s, LratStep::Add { .. }))
            .count()
    }
}

/// Per-replay trace recording the deterministic progress of a replay run.
///
/// Records the step count, final checker statistics, and any failure.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ReplayTrace {
    /// Number of LRAT steps consumed before termination (success or failure).
    pub steps_replayed: usize,
    /// Final stats from the underlying `LratChecker` (may be partial on failure).
    pub checker_stats: Stats,
}

/// Outcome of a proof-replay invocation.
///
/// `Success` means the proof re-validated against the given CNF. `Diverged`
/// means a replay implementation disagreed with its authoritative checker.
/// `InvalidProof` means the LRAT proof does not check out.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ReplayOutcome {
    /// Replay completed, proof verified end-to-end.
    Success { trace: ReplayTrace },
    /// A replay implementation disagreed with its authoritative checker.
    Diverged(String),
    /// The LRAT proof was well-formed but did not verify against the CNF.
    InvalidProof(String),
}

impl ReplayOutcome {
    #[must_use]
    pub const fn is_success(&self) -> bool {
        matches!(self, Self::Success { .. })
    }
}

/// Errors from loading or replaying a proof.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ReplayError {
    #[error("invalid DIMACS CNF: {0}")]
    Cnf(#[from] CommonParseError),
    #[error("invalid LRAT proof: {0}")]
    Lrat(#[from] LratParseError),
    /// The CNF parsed but declared zero clauses. LRAT needs at least one
    /// original clause or an empty-clause axiom to be meaningful.
    #[error("degenerate CNF: {detail}")]
    DegenerateCnf { detail: String },
    #[error("CNF variable count {requested} exceeds LRAT replay maximum {maximum}")]
    ResourceLimit { requested: usize, maximum: usize },
}

/// Interface for proof replay implementations.
///
/// [`DeterministicReplayer`] is the in-tree LRAT implementation and wraps
/// `ay-lrat-check`.
pub trait ProofReplayer {
    /// Parse the CNF + LRAT bytes into a [`ReplayPlan`].
    ///
    /// The default implementation uses the text/binary auto-detecting parsers
    /// from `ay-lrat-check`. Implementations that want to augment the plan
    /// with extra metadata (dependency graph, diff markers) may override this.
    fn load_lrat(&mut self, input: &ReplayInput<'_>) -> Result<ReplayPlan, ReplayError> {
        load_plan(input)
    }

    /// Replay the plan and return an outcome.
    fn replay(&mut self, plan: &ReplayPlan) -> ReplayOutcome;
}

/// Default LRAT replayer: re-validates via `ay-lrat-check`.
///
/// Deterministic by construction: given identical input, returns the same
/// outcome on every run. No internal randomness or shared mutable state.
#[derive(Debug, Default, Clone, Copy)]
pub struct DeterministicReplayer;

impl DeterministicReplayer {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }
}

impl ProofReplayer for DeterministicReplayer {
    fn replay(&mut self, plan: &ReplayPlan) -> ReplayOutcome {
        let mut checker = LratChecker::new(plan.num_vars);
        for (id, clause) in &plan.originals {
            if !checker.add_original(*id, clause) {
                let stats = checker.stats().clone();
                return ReplayOutcome::InvalidProof(format!(
                    "rejected original clause id={id} (failures={})",
                    stats.failures
                ));
            }
        }

        let ok = checker.verify_proof(&plan.steps);
        let trace = ReplayTrace {
            steps_replayed: plan.steps.len(),
            checker_stats: checker.stats().clone(),
        };
        if ok {
            ReplayOutcome::Success { trace }
        } else {
            ReplayOutcome::InvalidProof(format!(
                "LRAT verification failed after {} steps (failures={})",
                trace.steps_replayed, trace.checker_stats.failures
            ))
        }
    }
}

/// Free-function form of [`ProofReplayer::load_lrat`] for callers that do
/// not want to construct a replayer just to parse.
///
/// Detects text vs binary LRAT via [`is_binary_lrat`] and dispatches to the
/// matching parser. Returns `DegenerateCnf` if the CNF has zero clauses.
pub fn load_plan(input: &ReplayInput<'_>) -> Result<ReplayPlan, ReplayError> {
    let CnfFormulaWithIds { num_vars, clauses } = parse_cnf_with_ids(input.cnf)?;
    if num_vars > ay_lrat_check::checker::MAX_DENSE_VARS {
        return Err(ReplayError::ResourceLimit {
            requested: num_vars,
            maximum: ay_lrat_check::checker::MAX_DENSE_VARS,
        });
    }
    if clauses.is_empty() {
        return Err(ReplayError::DegenerateCnf {
            detail: "CNF declared zero clauses".into(),
        });
    }
    let binary = is_binary_lrat(input.proof);
    let steps = if binary {
        parse_binary_lrat(input.proof)?
    } else {
        let text = std::str::from_utf8(input.proof).map_err(|e| {
            ReplayError::Lrat(LratParseError::InvalidStep {
                detail: format!("LRAT proof is not valid UTF-8 (and not binary-LRAT): {e}"),
            })
        })?;
        parse_text_lrat(text)?
    };
    Ok(ReplayPlan {
        num_vars,
        originals: clauses,
        steps,
        binary,
    })
}

impl fmt::Display for ReplayOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Success { trace } => write!(
                f,
                "Success({} steps, {} derived, {} originals)",
                trace.steps_replayed, trace.checker_stats.derived, trace.checker_stats.originals
            ),
            Self::Diverged(msg) => write!(f, "Diverged({msg})"),
            Self::InvalidProof(msg) => write!(f, "InvalidProof({msg})"),
        }
    }
}

#[cfg(test)]
mod tests;
