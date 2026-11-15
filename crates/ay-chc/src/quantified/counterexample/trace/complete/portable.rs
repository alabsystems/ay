// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded complete MODEL DATA becomes a credential only after original replay.

use super::super::artifact::{
    functions as codec_functions, transport as codec_transport, QuantifiedChcTraceArtifactError,
};
use super::*;

mod arrays;
mod bindings;
mod rebuild;
mod scalar;
#[cfg(test)]
mod tests;
mod wire;

/// Exact accepted bytes and a construction-sealed complete same-assignment trace.
/// Native checked SAT, not a kernel proof, interpreter playback, or MODEL_CHECKER_CONSUMER
/// evidence admission. Wire names/sorts/digests carry no independent authority.
///
/// ```compile_fail
/// use ay_chc::quantified::QuantifiedChcValidatedCompleteTraceArtifact;
/// let forged = QuantifiedChcValidatedCompleteTraceArtifact {};
/// ```
#[derive(Debug)]
pub struct QuantifiedChcValidatedCompleteTraceArtifact {
    trace: QuantifiedChcCompleteTrace,
    artifact_sha256: String,
}

impl QuantifiedChcValidatedCompleteTraceArtifact {
    pub fn trace(&self) -> &QuantifiedChcCompleteTrace {
        &self.trace
    }
    pub fn artifact_sha256(&self) -> &str {
        &self.artifact_sha256
    }
    pub fn into_trace(self) -> QuantifiedChcCompleteTrace {
        self.trace
    }
}

impl QuantifiedChcCompleteTrace {
    /// Export complete ordered finite/store/range DATA after fresh full-source
    /// same-assignment native SAT. Arrays are whole BV64-indexed Bool/BV<=128
    /// functions, never sampled cells, lambda text or another model's values.
    ///
    /// Reuses the literal codec's 16MiB/JSON-depth16 limits and the SAME original
    /// source work/copy ledger, absolute wall, sticky token and minimum term cap.
    /// Snapshot topology also has aggregate4096-node/32768-store/depth64 bounds
    /// and one prepaid subledger per boundary; no per-array allowance resets.
    /// These logical bounds are not hard RSS, allocator or preemption guarantees.
    /// The exact emitted wire traverses the complete importer before returning.
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
                let rendered = bound(&self.base, problem, control)?;
                let registry = registry(problem, control)?;
                let pinned = pins::render(
                    &rendered,
                    &self.bindings,
                    &self.functions,
                    problem,
                    &registry,
                    control,
                )?;
                control.debit(pinned.len(), pinned.len())?;
                if pinned != self.pinned_obligation {
                    return None;
                }
                let mut catalog = arrays::Catalog::new(control, self.bindings.len())?;
                let steps = bindings::export(self, &registry, &mut catalog, control)?;
                let functions = codec_functions::export(&self.functions, problem, control)?;
                let pinned_sha256 = codec_transport::digest(pinned.as_bytes(), control)?;
                control.bytes(
                    problem
                        .source_smtlib()
                        .len()
                        .checked_add(wire::SCHEMA.len())?,
                )?;
                let wire = wire::Wire {
                    schema: wire::SCHEMA.to_owned(),
                    source: problem.source_smtlib().to_owned(),
                    steps,
                    graphs: catalog.graphs,
                    functions,
                    pinned_sha256,
                };
                let bytes = codec_transport::encode(&wire, control)?;
                drop((wire, rendered, registry));
                let imported = import(&bytes, problem, deadline, memory, token, control)?;
                control.debit(pinned.len(), 0)?;
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
    /// Import exact saved complete values under the retained ORIGINAL typed
    /// source, never reparsed payload source or an unchecked DTO credential.
    ///
    /// Every raw graph/node/capture is bounded and validated, including unused
    /// nodes, overwritten stores and both sides of empty/reversed ranges. All
    /// DAG edges point backwards. Source-variable sorts/names and derivation
    /// membership are regenerated. All original forall assertions + exact full
    /// pins must freshly receive native checked SAT before any trace escapes.
    /// A stale or unsatisfying saved value is NEVER replaced by a fresh model.
    /// The export bounds and parent minimum original wall/token/term cap apply.
    pub fn validate_complete_trace_artifact(
        &self,
        bytes: &[u8],
        time_budget: Duration,
        memory_budget: Option<usize>,
        cancellation: &CancellationToken,
    ) -> Result<QuantifiedChcValidatedCompleteTraceArtifact, QuantifiedChcTraceArtifactError> {
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
) -> Option<QuantifiedChcValidatedCompleteTraceArtifact> {
    let wire = codec_transport::decode::<wire::Wire>(bytes, control)?;
    let prepared = rebuild::prepare(problem, &wire, control)?;
    let artifact_sha256 = codec_transport::digest(bytes, control)?;
    drop(wire);
    let trace = prepared.replay(problem, deadline, memory, cancellation, control)?;
    control.poll()?;
    Some(QuantifiedChcValidatedCompleteTraceArtifact {
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
