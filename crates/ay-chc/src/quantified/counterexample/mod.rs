// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact source-derivation counterexamples, never SAT from an instantiated skeleton.

use std::sync::Arc;
use std::time::Duration;

use ay_core::time::Instant;

use super::{solve, QuantifiedChcProblem};
use crate::smt::{ScopedSmtDeadline, SmtContext};
use crate::transform::array_ghost_pairs::source_premises::SourceControl;
use crate::CancellationToken;

mod derivation;
mod exploration;
// Keep the prior linear enumerator only as a frozen regression oracle.
#[cfg(test)]
mod paths;
mod render;
#[cfg(test)]
#[path = "render/tests/oracle.rs"]
mod render_oracle;
mod replay;
mod search_trees;
mod trace;
// Frozen small-tree enumerator for differential regression tests only.
#[cfg(test)]
mod trees;
mod values;

pub use trace::{
    QuantifiedChcCompleteTrace, QuantifiedChcCompleteTraceBinding, QuantifiedChcCompleteValue,
    QuantifiedChcTrace, QuantifiedChcTraceArtifactError, QuantifiedChcTraceBinding,
    QuantifiedChcTraceLiftError, QuantifiedChcTraceStepView, QuantifiedChcTraceView,
    QuantifiedChcValidatedCompleteTraceArtifact, QuantifiedChcValidatedTraceArtifact,
};

use derivation::Derivation;

#[cfg(test)]
const MAX_PATH_CLAUSES: usize = 8;
#[cfg(test)]
const MAX_PATHS: usize = 64;

/// Construction-sealed evidence for a reachable original quantified query.
///
/// A complete original-source derivation conjunction was SAT with sealed native
/// model validation. This is not a portable ground derivation or kernel proof,
/// and contains no conversion to ordinary quantifier-free CHC artifacts.
#[derive(Debug)]
pub struct QuantifiedChcCounterexample {
    source: Arc<str>,
    clause_indices: Vec<usize>,
    premise_steps: Vec<Vec<usize>>,
    topology_sha256: [u8; 32],
    obligation: String,
    memory_budget: Option<usize>,
}

impl QuantifiedChcCounterexample {
    /// Complete canonical source, including clauses not used by this derivation.
    pub fn source_smtlib(&self) -> &str {
        &self.source
    }

    /// Original clause indices in topological occurrence order, ending in the
    /// false-head query. Repeated indices denote independently freshened clause
    /// occurrences. Use [`Self::premise_steps`] to interpret branching edges;
    /// this list alone does not describe a nonlinear derivation.
    pub fn clause_indices(&self) -> &[usize] {
        &self.clause_indices
    }

    /// Premise occurrence indices for each step, in original body-predicate
    /// order. Every index precedes its consumer, and each non-query occurrence
    /// has exactly one consumer. Bodyless facts/query steps have an empty list.
    /// This borrowed topology is not a concrete value trace or portable proof.
    pub fn premise_steps(&self) -> &[Vec<usize>] {
        &self.premise_steps
    }

    /// Standalone SAT obligation containing complete original premises.
    pub fn replay_obligation(&self) -> &str {
        &self.obligation
    }

    /// Rebuild this derivation from the complete source and freshly validate SAT.
    ///
    /// A changed source/topology/script, incomplete model, resource refusal or
    /// observed cancellation rejects. Replay retains the original term budget
    /// tightened by an enclosing budget; it cannot extend a parent deadline.
    pub fn recheck(
        &self,
        problem: &QuantifiedChcProblem,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> bool {
        solve::checked_attempt(time_budget, cancellation, |deadline, attempt| {
            let context = SmtContext::new();
            let memory = solve::tighter_budget(context.term_memory_budget, self.memory_budget);
            let _memory = SmtContext::scoped_thread_term_memory_budget(memory);
            let _deadline = ScopedSmtDeadline::install_until(deadline);
            let control = SourceControl::new(deadline, attempt);
            control.bytes(problem.source_smtlib().len())?;
            if self.source.as_ref() != problem.source_smtlib() {
                return None;
            }
            if derivation::fingerprint(&self.clause_indices, &self.premise_steps, &control)?
                != self.topology_sha256
            {
                return None;
            }
            let obligation = render::render_derivation(
                problem,
                &self.clause_indices,
                &self.premise_steps,
                &control,
            )
            .ok()?;
            control.bytes(obligation.len())?;
            if obligation != self.obligation {
                return None;
            }
            let valid = replay::validate(&obligation, deadline, memory, attempt, &control);
            drop(obligation);
            control.poll()?;
            valid.then_some(())
        })
        .is_some()
    }
}

/// Lazy, resource-bounded original occurrence-tree search. Failure proves nothing.
pub(super) fn search(
    problem: &QuantifiedChcProblem,
    deadline: Instant,
    memory_budget: Option<usize>,
    cancellation: &CancellationToken,
) -> Option<QuantifiedChcCounterexample> {
    exploration::run(problem, deadline, memory_budget, cancellation)
}

/// Complete discovery has no public credential until acquisition and full
/// canonical original-source pinned replay both land within the same owner.
pub(super) fn search_complete(
    problem: &QuantifiedChcProblem,
    search_deadline: Instant,
    deadline: Instant,
    memory_budget: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Option<QuantifiedChcCompleteTrace> {
    exploration::run_complete(
        problem,
        search_deadline,
        deadline,
        memory_budget,
        cancellation,
        control,
    )
}

#[cfg(test)]
mod tests;
