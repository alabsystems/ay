// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lift coordinates, never model values. Only complete aggregate pinned SAT
//! authorizes replacing the retained source and occurrence topology.

use super::*;
use crate::quantified::{QuantifiedChcQueryId, QuantifiedChcQueryObligation};

mod mapping;

/// Aggregate association, topology, replay or resource refusal.
///
/// Owns the original, unchanged slice trace, so a failed attempt never loses
/// the caller's concrete assignment or silently substitutes another model.
#[derive(Debug, thiserror::Error)]
#[error("quantified trace lift refused: source association, replay or resource limit")]
pub struct QuantifiedChcTraceLiftError {
    trace: QuantifiedChcTrace,
}

impl QuantifiedChcTraceLiftError {
    /// The original trace, including its original source and exact pins.
    pub fn trace(&self) -> &QuantifiedChcTrace {
        &self.trace
    }

    /// Recover the original assignment without cloning or reacquiring values.
    pub fn into_trace(self) -> QuantifiedChcTrace {
        self.trace
    }
}

impl QuantifiedChcTrace {
    /// Bind this query-slice trace to its complete aggregate and freshly replay.
    ///
    /// Authenticates the sealed query identity, exact aggregate canonical text,
    /// all mapped typed clauses and the original slice pins. Slice occurrences
    /// are translated to aggregate coordinates; an unfolded marker's final
    /// occurrence becomes its original definition followed by the original
    /// nullary query. Earlier recursive occurrences remain distinct.
    ///
    /// Every typed value and total function interpretation is moved unchanged.
    /// The complete aggregate obligation, including every universal premise,
    /// must receive fresh native SAT with those same pins. There is no model
    /// acquisition, unpinned fallback or conversion to a kernel proof. On any
    /// refusal the error retains the original trace for inspection or retry.
    ///
    /// One deadline, sticky cancellation and shared work/copy allowance cover
    /// association, rendering and replay. The tighter parent/original term cap
    /// applies; zero refuses. These are not RSS or whole-call latency bounds.
    /// After success, artifact export/recheck use `aggregate`, not the slice.
    // Return the already-owned trace without allocating on resource refusal.
    // Boxing only Err cannot remove the equally large Ok trace payload.
    #[allow(clippy::result_large_err)]
    pub fn lift_to_aggregate(
        mut self,
        obligation: &QuantifiedChcQueryObligation,
        aggregate: &QuantifiedChcProblem,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> Result<Self, QuantifiedChcTraceLiftError> {
        let lifted = solve::checked_attempt(time_budget, cancellation, |deadline, token| {
            let context = SmtContext::new();
            let memory = solve::tighter_budget(context.term_memory_budget, self.base.memory_budget);
            if memory == Some(0) {
                return None;
            }
            let _memory = SmtContext::scoped_thread_term_memory_budget(memory);
            let _deadline = ScopedSmtDeadline::install_until(deadline);
            let control = SourceControl::new(deadline, token);
            obligation.authenticate_aggregate(aggregate, deadline, token, &control)?;
            authenticate_slice(&self, obligation.problem(), &control)?;
            let prepared = prepare(&self, obligation.id(), aggregate, &control)?;
            let result = prepared.replay(aggregate, deadline, memory, token, &control);
            control.poll()?;
            result
        });
        let Some((base, pinned)) = lifted else {
            return Err(QuantifiedChcTraceLiftError { trace: self });
        };
        // Native contexts/guards have been destroyed and checked. Only plain
        // owned metadata is replaced here; the value/function vectors never
        // move their allocations or invoke deep clones/decoders.
        self.base = base;
        self.pinned_obligation = pinned;
        Ok(self)
    }
}

fn authenticate_slice(
    trace: &QuantifiedChcTrace,
    slice: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<()> {
    let rendered = bound_render(&trace.base, slice, control)?;
    let registry = registry(slice, control)?;
    let pinned = pins::render(
        &rendered,
        &trace.bindings,
        &trace.functions,
        slice,
        &registry,
        control,
    )?;
    control.bytes(pinned.len())?;
    if pinned != trace.pinned_obligation {
        return None;
    }
    drop((rendered, registry, pinned));
    control.poll()
}

/// Untrusted prepared coordinates/pins. Native replay is the only seal.
struct Prepared {
    derivation: derivation::Derivation,
    topology_sha256: [u8; 32],
    obligation: String,
    pinned: String,
}

fn prepare(
    trace: &QuantifiedChcTrace,
    id: &QuantifiedChcQueryId,
    aggregate: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<Prepared> {
    let derivation = mapping::map(trace, id, control)?;
    let rendered = render::render_with_bindings(
        aggregate,
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    )
    .ok()?;
    if rendered.bindings.len() > MAX_BINDINGS {
        return None;
    }
    let registry = registry(aggregate, control)?;
    let pinned = pins::render(
        &rendered,
        &trace.bindings,
        &trace.functions,
        aggregate,
        &registry,
        control,
    )?;
    let topology_sha256 = derivation::fingerprint(
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    )?;
    drop((rendered.bindings, registry));
    control.poll()?;
    Some(Prepared {
        derivation,
        topology_sha256,
        obligation: rendered.obligation,
        pinned,
    })
}

impl Prepared {
    fn replay(
        self,
        aggregate: &QuantifiedChcProblem,
        deadline: Instant,
        memory: Option<usize>,
        token: &CancellationToken,
        control: &SourceControl<'_>,
    ) -> Option<(QuantifiedChcCounterexample, String)> {
        if !replay::validate(&self.pinned, deadline, memory, token, control) {
            return None;
        }
        control.bytes(aggregate.source_smtlib().len().checked_add(64)?)?;
        let base = QuantifiedChcCounterexample {
            source: Arc::from(aggregate.source_smtlib()),
            clause_indices: self.derivation.clause_indices,
            premise_steps: self.derivation.premise_steps,
            topology_sha256: self.topology_sha256,
            obligation: self.obligation,
            memory_budget: memory,
        };
        control.poll()?;
        Some((base, self.pinned))
    }
}

#[cfg(test)]
mod tests;
