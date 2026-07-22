// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sequential, RUP-only DRAT replay.
//!
//! Given a DRAT proof emitted by a previous UNSAT solve plus the originating
//! DIMACS CNF, walk the proof steps in order and verify each derivation via
//! **RUP only** — *not* full DRAT (no RAT fallback). The replayer does not
//! search; it checks the recorded additions with reverse unit propagation.
//!
//! The underlying [`DratChecker`] (with `check_rat = false`) implements RUP
//! checking with a two-watched-literal BCP engine. A proof containing an
//! addition that requires RAT is rejected rather than silently accepted.
//!
//! # When to use this vs. the LRAT path
//!
//! | Path                     | Proof format | RAT support |
//! |--------------------------|--------------|-------------|
//! | `DeterministicReplayer`  | LRAT         | Not applicable; LRAT carries hints |
//! | `SequentialReplayer`     | DRAT         | No; rejects non-RUP additions |
//! | `DratChecker::new(_, true)` | DRAT     | Yes |
//!
//! Use strict sequential replay when the proof producer is expected to emit
//! only RUP additions. Use the full checker when RAT steps are possible.
//!
//! # Usage
//!
//! ```no_run
//! use ay_replay::drat::{DratReplayInput, SequentialReplayer};
//!
//! // Minimal UNSAT CNF: (x) AND (-x).
//! let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
//! // DRAT proof: derive empty clause (RUP-implied because unit `x` then
//! // unit `-x` conflict on propagation).
//! let proof = b"0\n";
//! let mut replayer = SequentialReplayer::new();
//! let plan = replayer.load(&DratReplayInput { cnf, proof }).expect("load");
//! let outcome = replayer.replay(&plan).expect("replay");
//! assert!(outcome.verified);
//! ```

use std::fmt;

use ay_drat_check::checker::{ConcludeFailure, ConcludeResult, DratChecker, Stats};
use ay_drat_check::cnf_parser::{parse_cnf, CnfFormula};
use ay_drat_check::drat_parser::{is_binary_drat, parse_binary_drat, parse_text_drat, ProofStep};
use ay_drat_check::error::{DratCheckError, DratParseError};
use ay_proof_common::literal::Literal;
use ay_proof_common::ParseError as CommonParseError;
use thiserror::Error;

/// Input to the sequential DRAT replayer.
#[derive(Debug, Clone, Copy)]
pub struct DratReplayInput<'a> {
    /// DIMACS CNF bytes.
    pub cnf: &'a [u8],
    /// DRAT proof bytes (text or binary — auto-detected).
    pub proof: &'a [u8],
}

/// Parsed DRAT proof plan: the originating formula plus the proof-step sequence.
///
/// The sequence is kept in authoring order. Sequential replay walks it linearly.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct DratReplayPlan {
    /// Variable count parsed from the CNF header.
    pub num_vars: usize,
    /// Original clauses in the order they appeared in the DIMACS file.
    pub originals: Vec<Vec<Literal>>,
    /// DRAT proof steps in authoring order. Each step is either an
    /// `Add(clause)` (RUP-implied derivation) or `Delete(clause)`.
    pub steps: Vec<ProofStep>,
    /// Whether the proof was read as binary DRAT (informational).
    pub binary: bool,
    /// Precomputed execution profile used by the sequential replay loop.
    pub execution_profile: DratReplayExecutionProfile,
}

impl DratReplayPlan {
    /// Total number of proof steps (add + delete).
    #[must_use]
    pub fn step_count(&self) -> usize {
        self.steps.len()
    }

    /// Number of `Add` (derivation) steps — unit-propagation checks that
    /// will actually be performed during replay.
    #[must_use]
    pub fn add_step_count(&self) -> usize {
        self.steps
            .iter()
            .filter(|s| matches!(s, ProofStep::Add(_)))
            .count()
    }

    /// Number of proof steps the replay loop must execute to reach the first
    /// derived empty clause.
    #[must_use]
    pub const fn replay_step_limit(&self) -> usize {
        self.execution_profile.replay_step_limit
    }
}

/// Precomputed execution profile for a parsed DRAT proof.
///
/// Sequential replay only needs to execute through the first empty-clause
/// addition. Any later proof steps cannot affect the UNSAT conclusion, so this
/// profile lets the loop avoid post-conclusion work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct DratReplayExecutionProfile {
    /// Exclusive step count needed to reach the proof conclusion.
    pub replay_step_limit: usize,
    /// Index of the first empty-clause add step, if present.
    pub concluding_empty_clause_step: Option<usize>,
    /// Steps after the first empty clause that replay can skip.
    pub trailing_steps_skipped: usize,
}

impl DratReplayExecutionProfile {
    #[must_use]
    fn from_steps(steps: &[ProofStep]) -> Self {
        let concluding_empty_clause_step = steps
            .iter()
            .position(|step| matches!(step, ProofStep::Add(lits) if lits.is_empty()));
        let replay_step_limit = concluding_empty_clause_step.map_or(steps.len(), |idx| idx + 1);
        Self {
            replay_step_limit,
            concluding_empty_clause_step,
            trailing_steps_skipped: steps.len().saturating_sub(replay_step_limit),
        }
    }
}

/// Outcome of a single sequential DRAT replay run.
///
/// `verified == true` iff every `Add` step was RUP-implied by the running
/// clause database *and* the proof concluded with the empty clause. A single
/// non-RUP step fails the run: we do not fall back to RAT.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SequentialReplayOutcome {
    /// Overall verdict: did the proof check out end-to-end.
    pub verified: bool,
    /// Number of add steps that passed RUP.
    pub add_steps_verified: usize,
    /// Number of delete steps applied.
    pub delete_steps_applied: usize,
    /// Number of proof steps actually executed before conclusion or failure.
    pub steps_replayed: usize,
    /// Number of post-conclusion proof steps skipped by the execution profile.
    pub trailing_steps_skipped: usize,
    /// Final checker statistics.
    pub stats: Stats,
    /// If not verified, a short human-readable reason.
    pub failure_reason: Option<String>,
}

impl SequentialReplayOutcome {
    #[must_use]
    pub const fn is_verified(&self) -> bool {
        self.verified
    }
}

impl fmt::Display for SequentialReplayOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.verified {
            write!(
                f,
                "Verified({} add, {} del, {} RUP)",
                self.add_steps_verified, self.delete_steps_applied, self.stats.additions
            )
        } else {
            write!(
                f,
                "Failed({} add ok, reason={})",
                self.add_steps_verified,
                self.failure_reason.as_deref().unwrap_or("unknown")
            )
        }
    }
}

/// Errors from loading or running a sequential DRAT replay.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum DratReplayError {
    #[error("invalid DIMACS CNF: {0}")]
    Cnf(#[from] CommonParseError),
    #[error("invalid DRAT proof: {0}")]
    Drat(#[from] DratParseError),
    /// The CNF parsed but declared zero clauses.
    #[error("degenerate CNF: {detail}")]
    DegenerateCnf { detail: String },
    #[error("CNF variable count {requested} exceeds DRAT replay maximum {maximum}")]
    ResourceLimit { requested: usize, maximum: usize },
}

/// Fast sequential DRAT replayer.
///
/// State-free by construction: a fresh [`DratChecker`] is built for every
/// [`Self::replay`] call, so the replayer itself can be reused across proofs
/// without poisoning.
#[derive(Debug, Default, Clone, Copy)]
pub struct SequentialReplayer;

impl SequentialReplayer {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    /// Parse CNF + DRAT bytes into a replay plan.
    ///
    /// Auto-detects text vs binary DRAT via [`is_binary_drat`] and dispatches
    /// to the matching parser.
    pub fn load(&self, input: &DratReplayInput<'_>) -> Result<DratReplayPlan, DratReplayError> {
        let CnfFormula { num_vars, clauses } = parse_cnf(input.cnf)?;
        if num_vars > ay_drat_check::checker::MAX_DENSE_VARS {
            return Err(DratReplayError::ResourceLimit {
                requested: num_vars,
                maximum: ay_drat_check::checker::MAX_DENSE_VARS,
            });
        }
        if clauses.is_empty() {
            return Err(DratReplayError::DegenerateCnf {
                detail: "CNF declared zero clauses".into(),
            });
        }
        let binary = is_binary_drat(input.proof);
        let steps = if binary {
            parse_binary_drat(input.proof)?
        } else {
            parse_text_drat(input.proof)?
        };
        Ok(DratReplayPlan {
            num_vars,
            originals: clauses,
            execution_profile: DratReplayExecutionProfile::from_steps(&steps),
            steps,
            binary,
        })
    }

    /// Sequentially apply every proof step, RUP-checking each `Add`.
    ///
    /// **Not** a full DRAT check: RAT fallback is disabled. A non-RUP `Add`
    /// step aborts the run with `verified = false`.
    pub fn replay(
        &self,
        plan: &DratReplayPlan,
    ) -> Result<SequentialReplayOutcome, DratReplayError> {
        // RUP-only: pass `check_rat = false`. Forbidding RAT is a deliberate
        // speed choice; it also makes this path the strict subset every valid
        // ay-emitted proof lives in.
        let mut checker = DratChecker::new(plan.num_vars, /* check_rat = */ false);
        for clause in &plan.originals {
            checker.add_original(clause);
        }

        let mut add_ok: usize = 0;
        let mut dels: usize = 0;
        let mut failure_reason: Option<String> = None;

        let mut steps_replayed = 0;
        for (idx, step) in plan
            .steps
            .iter()
            .take(plan.execution_profile.replay_step_limit)
            .enumerate()
        {
            steps_replayed += 1;
            match step {
                ProofStep::Add(lits) => match checker.add_derived(lits) {
                    Ok(()) => add_ok += 1,
                    Err(DratCheckError::NotImplied { clause, step, kind }) => {
                        failure_reason = Some(format!(
                            "step {}: clause {clause} not {kind}implied (reported step {step})",
                            idx + 1
                        ));
                        break;
                    }
                    Err(other) => {
                        failure_reason = Some(format!("step {}: {other}", idx + 1));
                        break;
                    }
                },
                ProofStep::Delete(lits) => {
                    checker.delete_clause(lits);
                    dels += 1;
                }
                // `ProofStep` is #[non_exhaustive]; any step kind this RUP/RAT
                // replay checker does not handle — `AddPr` (PR/DPR clauses need a
                // verified LPR checker) and any future variant — cannot be
                // soundly verified here. Fail closed: never conclude the proof
                // verified on the strength of a step we could not check.
                other => {
                    failure_reason = Some(format!(
                        "step {}: unsupported proof step {other:?} for the RUP/RAT replay checker",
                        idx + 1
                    ));
                    break;
                }
            }
        }

        let conclusion = if failure_reason.is_none() {
            checker.conclude_unsat()
        } else {
            ConcludeResult::Failed(ConcludeFailure::StepFailures)
        };
        let verified = matches!(conclusion, ConcludeResult::Verified);
        let trailing_steps_skipped = if failure_reason.is_none()
            && steps_replayed == plan.execution_profile.replay_step_limit
        {
            plan.execution_profile.trailing_steps_skipped
        } else {
            0
        };
        if verified {
            Ok(SequentialReplayOutcome {
                verified: true,
                add_steps_verified: add_ok,
                delete_steps_applied: dels,
                steps_replayed,
                trailing_steps_skipped,
                stats: checker.stats().clone(),
                failure_reason: None,
            })
        } else {
            let reason = failure_reason.unwrap_or_else(|| match conclusion {
                ConcludeResult::Failed(f) => format!("conclude: {f}"),
                ConcludeResult::Verified => "internal: verified but flagged".into(),
            });
            Ok(SequentialReplayOutcome {
                verified: false,
                add_steps_verified: add_ok,
                delete_steps_applied: dels,
                steps_replayed,
                trailing_steps_skipped,
                stats: checker.stats().clone(),
                failure_reason: Some(reason),
            })
        }
    }
}

#[cfg(test)]
mod tests;
