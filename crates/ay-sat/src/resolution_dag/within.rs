// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! [`super::prove_unsat_resolution_dag`] inside a counted work envelope.
//!
//! The unbounded entry point runs until the formula is decided. A caller that
//! asks it from inside a solve can poll its own stop
//! ([`super::prove_unsat_resolution_dag_until`]), but a caller with neither an
//! interrupt nor a deadline then waits as long as the formula takes: measured
//! on the elaborated 64-bit affine identity `bv_affine_source` certifies
//! (`(set-option :check-proofs-strict true)`, no `:timeout`, read from stdin),
//! the complete bit-blast's monolithic refutation of its 5,079-gate,
//! 16,511-clause blast was still searching when the run was killed at 280 s.
//!
//! An envelope bounds that search by the solver's own deterministic counters
//! (conflicts and decisions, `Solver::set_conflict_budget` and
//! `Solver::set_decision_budget`). The solver reads either budget only to ask
//! whether it is spent, so neither steers the search: while the envelope
//! holds, the refutation is the one the unbounded solve finds, and where the
//! envelope runs out is a function of the search trajectory. That trajectory
//! is host-independent only under `--sat-deterministic-inproc`
//! (`determinism.rs`); by default the first attempt's inprocessing is
//! scheduled by wall-clock caps, so a formula at the envelope's very edge may
//! be refuted on one run and refused on another.

use super::{ordinary, Literal, ResolutionDag, ResolutionDagCancellationError, ResolutionDagError};
use crate::solver::{SatUnknownReason, Solver};

/// A counted work envelope: the most conflicts and decisions one refutation
/// may spend, over every attempt it makes (an LRAT authority retry spends
/// what the first attempt left).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ResolutionDagWork {
    /// Solver conflicts.
    pub max_conflicts: u64,
    /// Solver decisions.
    pub max_decisions: u64,
}

impl ResolutionDagWork {
    /// Install what is left of this envelope as `solver`'s budgets.
    pub(super) fn install(self, solver: &mut Solver) {
        solver.set_conflict_budget(Some(self.max_conflicts));
        solver.set_decision_budget(Some(self.max_decisions));
    }

    /// Charge what `solver` spent against this envelope.
    pub(super) fn charge(&mut self, solver: &Solver) {
        self.max_conflicts = self.max_conflicts.saturating_sub(solver.num_conflicts());
        self.max_decisions = self.max_decisions.saturating_sub(solver.num_decisions());
    }
}

/// Whether an `Unknown` from `solver`, run inside an envelope, is the
/// envelope running out rather than a stop or a failure.
pub(super) fn ran_out(solver: &Solver) -> bool {
    solver.last_unknown_reason() == Some(SatUnknownReason::ResourceBudget)
}

/// [`super::prove_unsat_resolution_dag`] within `work`, and stopped when
/// `should_stop` (if any) returns `true`.
///
/// While the envelope holds and the stop does not fire, the refutation is the
/// one the unbounded solve finds. An exhausted envelope is
/// [`ResolutionDagError::OverEnvelope`], a stop
/// [`ResolutionDagError::Unknown`]; neither is a refutation or a satisfiable
/// verdict.
///
/// # Errors
/// [`super::prove_unsat_resolution_dag`]'s, plus
/// [`ResolutionDagError::OverEnvelope`].
pub fn prove_unsat_resolution_dag_within(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    work: ResolutionDagWork,
    should_stop: Option<&dyn Fn() -> bool>,
) -> Result<ResolutionDag, ResolutionDagError> {
    ordinary::with_work(
        num_vars,
        clauses,
        &mut || !should_stop.is_some_and(|stop| stop()),
        Some(work),
    )
    .map_err(|error| match error {
        ResolutionDagCancellationError::Cancelled => ResolutionDagError::Unknown,
        ResolutionDagCancellationError::Resolution(error) => error,
    })
}
