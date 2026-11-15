// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Durable data is never a replay permit. Both boundaries require fresh native
//! SAT for the complete original derivation with precisely the retained pins.

use super::*;

mod bindings;
pub(super) mod functions;
mod rebuild;
pub(super) mod transport;
mod wire;

/// Refusal of malformed, mismatched, unsupported, unverified or over-budget
/// quantified trace transport. No partial artifact or unchecked trace escapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("quantified trace artifact refused: invalid data, replay or resource limit")]
pub struct QuantifiedChcTraceArtifactError;

/// A retained artifact's exact assignment after fresh complete native replay.
///
/// The digest binds the accepted input bytes, not a caller-supplied hash. This
/// is native checked SAT evidence, not an independent kernel proof. Import
/// itself performs no query-to-aggregate lift; a trace explicitly lifted before
/// export instead names the aggregate source. No public deserializer or
/// unchecked constructor can produce this wrapper.
///
/// ```compile_fail
/// use ay_chc::quantified::QuantifiedChcValidatedTraceArtifact;
/// let forged = QuantifiedChcValidatedTraceArtifact {};
/// ```
#[derive(Debug)]
pub struct QuantifiedChcValidatedTraceArtifact {
    trace: QuantifiedChcTrace,
    artifact_sha256: String,
}

impl QuantifiedChcValidatedTraceArtifact {
    /// Source-bound, complete concrete assignment accepted by this import.
    pub fn trace(&self) -> &QuantifiedChcTrace {
        &self.trace
    }

    /// Lowercase SHA-256 of the exact accepted artifact bytes.
    pub fn artifact_sha256(&self) -> &str {
        &self.artifact_sha256
    }

    /// Transfer the checked trace without another solve or model substitution.
    pub fn into_trace(self) -> QuantifiedChcTrace {
        self.trace
    }
}

impl QuantifiedChcTrace {
    /// Export a versioned source-bound artifact after fresh same-assignment SAT.
    ///
    /// Includes the complete canonical source, ordered occurrence tree, every
    /// typed local as a closed literal, all total function definitions and the
    /// regenerated pinned-obligation digest. No debug strings, finite function
    /// samples or omitted array defaults substitute for a value.
    ///
    /// The source must be the exact retained typed problem. A slice artifact
    /// refers only to that slice; aggregate query IDs and origins are not part
    /// of this version. Import must independently retain that same source.
    /// To save an aggregate trace, first use [`Self::lift_to_aggregate`], then
    /// export with the retained aggregate problem.
    ///
    /// Transport is bounded to 16 MiB and JSON nesting 16, with the existing
    /// shared source work/copy limits and at most 4096 local bindings. These
    /// bounds can refuse otherwise admitted traces. One deadline and sticky
    /// cancellation span rendering, serialization and fresh native replay;
    /// tighter parent/original term-memory caps apply. These are not RSS or
    /// whole-call latency guarantees, and no verifier or solver fallback exists.
    /// The emitted bytes traverse the same bounded importer before return, so
    /// serialization cannot hide a literal/metadata admission incompatibility.
    pub fn export_artifact(
        &self,
        problem: &QuantifiedChcProblem,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> Result<Vec<u8>, QuantifiedChcTraceArtifactError> {
        attempt(
            time_budget,
            self.base.memory_budget,
            cancellation,
            |deadline, memory, token, control| {
                let rendered = bound_render(&self.base, problem, control)?;
                let registry = registry(problem, control)?;
                let pinned = pins::render(
                    &rendered,
                    &self.bindings,
                    &self.functions,
                    problem,
                    &registry,
                    control,
                )?;
                control.bytes(pinned.len())?;
                if pinned != self.pinned_obligation {
                    return None;
                }
                let wire = wire::export(self, problem, &registry, control)?;
                let bytes = transport::encode(&wire, control)?;
                drop((wire, rendered, registry));
                let imported = import(&bytes, problem, deadline, memory, token, control)?;
                control.bytes(pinned.len())?;
                if imported.trace.replay_obligation() != pinned {
                    return None;
                }
                drop((pinned, imported));
                control.poll()?;
                Some(bytes)
            },
        )
        .ok_or(QuantifiedChcTraceArtifactError)
    }
}

impl QuantifiedChcProblem {
    /// Decode and freshly replay the exact saved quantified assignment.
    ///
    /// `self`, not the payload, supplies source and sort authority. Complete
    /// canonical source bytes must match, including unused declarations and
    /// all premises. Never reparse artifact source text to obtain `self`:
    /// parser binder freshening and fixedpoint provenance are not idempotent.
    /// Retain the original typed problem or reconstruct from identical original
    /// input with the same source admission semantics.
    ///
    /// Topology and the entire occurrence/name/sort inventory are rebuilt from
    /// that source. All values and total functions are decoded as bounded data,
    /// then the full pinned original obligation must receive fresh native SAT
    /// with model validation. An unsatisfying saved assignment cannot be
    /// replaced by another model. Ordinary/QF or query-tagged artifacts refuse.
    /// No finite-instance, debug-only or externally authored permit is accepted.
    ///
    /// The export transport bounds and existing typed-decoder limits apply.
    /// One original deadline, sticky cancellation and shared work/copy allowance
    /// cover the complete import. `memory_budget` is a term-store byte cap,
    /// tightened by the parent; zero refuses. It is not process-RSS isolation.
    pub fn validate_trace_artifact(
        &self,
        bytes: &[u8],
        time_budget: Duration,
        memory_budget: Option<usize>,
        cancellation: &CancellationToken,
    ) -> Result<QuantifiedChcValidatedTraceArtifact, QuantifiedChcTraceArtifactError> {
        attempt(
            time_budget,
            memory_budget,
            cancellation,
            |deadline, memory, token, control| {
                import(bytes, self, deadline, memory, token, control)
            },
        )
        .ok_or(QuantifiedChcTraceArtifactError)
    }
}

fn import(
    bytes: &[u8],
    problem: &QuantifiedChcProblem,
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Option<QuantifiedChcValidatedTraceArtifact> {
    let wire = transport::decode::<wire::Wire>(bytes, control)?;
    let prepared = rebuild::prepare(problem, &wire, control)?;
    let artifact_sha256 = transport::digest(bytes, control)?;
    drop(wire);
    let trace = prepared.replay(problem, deadline, memory, cancellation, control)?;
    control.poll()?;
    Some(QuantifiedChcValidatedTraceArtifact {
        trace,
        artifact_sha256,
    })
}

fn attempt<T>(
    budget: Duration,
    requested_memory: Option<usize>,
    cancellation: &CancellationToken,
    work: impl FnOnce(Instant, Option<usize>, &CancellationToken, &SourceControl<'_>) -> Option<T>,
) -> Option<T> {
    solve::checked_attempt(budget, cancellation, |deadline, token| {
        let context = SmtContext::new();
        let memory = solve::tighter_budget(context.term_memory_budget, requested_memory);
        if memory == Some(0) {
            return None;
        }
        let _memory = SmtContext::scoped_thread_term_memory_budget(memory);
        let _deadline = ScopedSmtDeadline::install_until(deadline);
        let control = SourceControl::new(deadline, token);
        let result = work(deadline, memory, token, &control);
        control.poll()?;
        result
    })
}

#[cfg(test)]
mod tests;
