// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact, source-bound safety query decomposition; never a solved verdict.

mod association;
mod control;
mod copy;
mod origins;
mod plan;
#[cfg(test)]
mod tests;

use super::{QuantifiedChcProblem, QuantifiedHornClause};
use crate::{CancellationToken, ChcError, ChcResult};
use ay_core::time::Instant;
use control::Control;
use sha2::{Digest, Sha256};
use std::sync::Arc;
use std::time::Duration;

pub use origins::QuantifiedChcClauseOrigin;

/// Identity of one obligation within the complete original quantified source.
/// Equal slice contents do not merge distinct source occurrences.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedChcQueryId {
    source_query_ordinal: usize,
    query_clause_index: usize,
    defining_clause_index: Option<usize>,
    label: String,
    aggregate_source: Arc<str>,
    aggregate_source_sha256: String,
    content_sha256: String,
    clause_origins: Arc<[QuantifiedChcClauseOrigin]>,
}

impl QuantifiedChcQueryId {
    /// Absolute ordinal among the aggregate source's false-head clauses.
    pub fn source_query_ordinal(&self) -> usize {
        self.source_query_ordinal
    }

    /// Aggregate clause index of the original false-head query.
    pub fn query_clause_index(&self) -> usize {
        self.query_clause_index
    }

    /// Aggregate defining clause unfolded for this marker branch, if any.
    pub fn defining_clause_index(&self) -> Option<usize> {
        self.defining_clause_index
    }

    /// Human-readable source marker label; not a unique identity by itself.
    pub fn label(&self) -> &str {
        &self.label
    }

    /// SHA-256 of the complete aggregate canonical source, including premises.
    pub fn aggregate_source_sha256(&self) -> &str {
        &self.aggregate_source_sha256
    }

    /// SHA-256 of this complete canonical slice, including unused declarations.
    pub fn content_sha256(&self) -> &str {
        &self.content_sha256
    }

    /// Aggregate origin of every clause in slice order, including its query.
    ///
    /// Counterexample/trace clause indices are local to the supplied slice.
    /// An unfolded marker is a composition of two aggregate source clauses,
    /// not an unchanged aggregate clause. Bind this ID's source hashes before
    /// using these coordinates with a separately retained problem.
    pub fn clause_origins(&self) -> &[QuantifiedChcClauseOrigin] {
        &self.clause_origins
    }

    /// Constant-time checked lookup by a slice-local clause index.
    pub fn clause_origin(&self, slice_index: usize) -> Option<QuantifiedChcClauseOrigin> {
        self.clause_origins.get(slice_index).copied()
    }
}

/// Immutable quantified source slice and its aggregate-source identity.
#[derive(Debug, Clone)]
pub struct QuantifiedChcQueryObligation {
    id: QuantifiedChcQueryId,
    problem: QuantifiedChcProblem,
}

impl QuantifiedChcQueryObligation {
    /// Source location and content identity of this obligation.
    pub fn id(&self) -> &QuantifiedChcQueryId {
        &self.id
    }

    /// Complete immutable slice; universal premises remain explicitly scoped.
    pub fn problem(&self) -> &QuantifiedChcProblem {
        &self.problem
    }

    /// Transfer the identity and slice together without cloning either.
    pub fn into_parts(self) -> (QuantifiedChcQueryId, QuantifiedChcProblem) {
        (self.id, self.problem)
    }

    /// Authenticate canonical aggregate identity and every mapped raw clause,
    /// without copying clauses, reparsing text or constructing another slice.
    pub(in crate::quantified) fn authenticate_aggregate(
        &self,
        aggregate: &QuantifiedChcProblem,
        deadline: Instant,
        token: &CancellationToken,
        parent: &crate::transform::array_ghost_pairs::source_premises::SourceControl<'_>,
    ) -> Option<()> {
        let control = Control::with_source(deadline, token, parent);
        association::authenticate(self, aggregate, &control).ok()
    }
}

impl QuantifiedChcProblem {
    /// Hash the exact canonical typed source, not the caller's textual spelling.
    pub fn source_sha256(&self) -> String {
        digest(self.source_smtlib())
    }

    /// Decompose safety queries without simplifying clauses or losing premises.
    ///
    /// Retains all declarations and predicate IDs. Each slice contains its
    /// query and the exact backwards dependency cone, in source clause order.
    /// An unconstrained nullary marker query with no universal premises may
    /// unfold one level into separate defining-clause bodies. Other queries
    /// remain intact; variable scopes are never combined. Duplicate and
    /// vacuous source rows remain distinct. The aggregate is Safe exactly when
    /// every returned slice is Safe; this method itself proves none of them.
    ///
    /// One original deadline, sticky cancellation observation and fixed shared
    /// work/copy/output limits cover the whole batch. Any refusal returns an
    /// error, never a partial prefix. Individual admitted cloning, formatting
    /// and hashing calls remain opaque; there is no wall-clock latency bound.
    pub fn query_obligations(
        &self,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> ChcResult<Vec<QuantifiedChcQueryObligation>> {
        let start = Instant::now();
        let deadline = start
            .checked_add(time_budget)
            .ok_or_else(|| invalid("deadline overflow"))?;
        let deadline = crate::smt::deadline::current_smt_deadline()
            .map_or(deadline, |parent| parent.min(deadline));
        if Instant::now() >= deadline
            || cancellation.is_cancelled()
            || ay_core::TermStore::global_memory_exceeded()
        {
            return Err(invalid("entry deadline, cancellation or memory refusal"));
        }
        let attempt = cancellation.sticky_child();
        let control = Control::new(deadline, &attempt);
        enumerate_checked(self, &control)
    }
}

fn enumerate_checked(
    source: &QuantifiedChcProblem,
    control: &Control<'_>,
) -> ChcResult<Vec<QuantifiedChcQueryObligation>> {
    let result = enumerate(source, control)?;
    // All planning/census scratch has been destroyed before publication.
    control.poll()?;
    Ok(result)
}

fn enumerate(
    source: &QuantifiedChcProblem,
    control: &Control<'_>,
) -> ChcResult<Vec<QuantifiedChcQueryObligation>> {
    control.poll()?;
    let census = copy::Census::new(source, control)?;
    let plans = plan::plans(source, control)?;
    control.charge(1, source.source_smtlib().len())?;
    let aggregate_hash = digest(source.source_smtlib());
    control.poll()?;
    let aggregate_source = association::retain_source(source.source_smtlib(), control)?;
    let mut result = Vec::new();
    control.charge(plans.len(), plans.len().saturating_mul(512))?;
    result
        .try_reserve_exact(plans.len())
        .map_err(|_| invalid("allocation"))?;
    for plan in plans {
        control.poll()?;
        let selected = plan::cone(source, &plan, &census.definitions, control)?;
        census.charge_slice(&selected, plan.selected(), control)?;
        let declarations = copy::declarations(source.source_problem(), control)?;
        let functions = copy::functions(source, control)?;
        let copied = copy::clauses(source, &plan, &selected, control)?;
        control.poll()?;
        let problem =
            QuantifiedChcProblem::new_with_functions(declarations, functions, copied.clauses)?;
        census.charge_conservation(&selected, plan.selected(), control)?;
        let clause_origins =
            origins::seal(source, &plan, &selected, &problem, copied.origins, control)?;
        control.poll()?;
        control.charge(1, problem.source_smtlib().len())?;
        let content_sha256 = digest(problem.source_smtlib());
        control.poll()?;
        result.push(QuantifiedChcQueryObligation {
            id: QuantifiedChcQueryId {
                source_query_ordinal: plan.ordinal,
                query_clause_index: plan.query,
                defining_clause_index: plan.definition,
                label: plan.label,
                aggregate_source: Arc::clone(&aggregate_source),
                aggregate_source_sha256: aggregate_hash.clone(),
                content_sha256,
                clause_origins,
            },
            problem,
        });
    }
    control.poll()?;
    Ok(result)
}

fn invalid(message: &str) -> ChcError {
    ChcError::Verification(format!("quantified query slicing: {message}"))
}

fn digest(source: &str) -> String {
    format!("{:x}", Sha256::digest(source.as_bytes()))
}
