// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete immutable data becomes a trace only after full original pinned SAT.

use super::*;
use ay_model_check::ArraySnapshot;

mod acquire;
mod pins;
mod portable;
pub use portable::QuantifiedChcValidatedCompleteTraceArtifact;
mod snapshots;
#[cfg(test)]
mod tests;

/// Complete value DATA. Structural inequality is not array disequality.
/// No SAT, Unsafe, proof, source-membership or replay credential is carried.
#[derive(Clone, Debug)]
pub enum QuantifiedChcCompleteValue {
    Literal(SmtValue),
    FunctionalArray(Arc<ArraySnapshot>),
}

/// One original occurrence-local variable, excluding universal binders.
#[derive(Debug)]
pub struct QuantifiedChcCompleteTraceBinding {
    occurrence: usize,
    variable: ChcVar,
    value: QuantifiedChcCompleteValue,
}

impl QuantifiedChcCompleteTraceBinding {
    pub fn occurrence(&self) -> usize {
        self.occurrence
    }
    pub fn variable(&self) -> &ChcVar {
        &self.variable
    }
    pub fn value(&self) -> &QuantifiedChcCompleteValue {
        &self.value
    }
}

/// A construction-sealed same-assignment full-source native trace.
/// This is not a portable proof or ordinary ground CHC credential. No unchecked
/// constructor, unchecked artifact deserializer or finite-read admission is provided.
#[derive(Debug)]
pub struct QuantifiedChcCompleteTrace {
    base: QuantifiedChcCounterexample,
    bindings: Vec<QuantifiedChcCompleteTraceBinding>,
    functions: Vec<ScalarFunctionModel>,
    pinned_obligation: String,
}

impl QuantifiedChcCompleteTrace {
    pub fn source_smtlib(&self) -> &str {
        self.base.source_smtlib()
    }
    pub fn clause_indices(&self) -> &[usize] {
        self.base.clause_indices()
    }
    pub fn premise_steps(&self) -> &[Vec<usize>] {
        self.base.premise_steps()
    }
    pub fn bindings(&self) -> &[QuantifiedChcCompleteTraceBinding] {
        &self.bindings
    }
    pub fn function_models(&self) -> &[ScalarFunctionModel] {
        &self.functions
    }
    pub fn replay_obligation(&self) -> &str {
        &self.pinned_obligation
    }

    /// Regenerate every original assertion and exact complete pin, then require
    /// fresh native checked SAT. A changed source, model or stop refuses.
    pub fn recheck(
        &self,
        problem: &QuantifiedChcProblem,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> bool {
        attempt(
            &self.base,
            time_budget,
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
                control.bytes(pinned.len())?;
                if pinned != self.pinned_obligation {
                    return None;
                }
                let valid = replay::validate(&pinned, deadline, memory, token, control);
                drop((pinned, rendered, registry));
                control.poll()?;
                valid.then_some(())
            },
        )
        .is_some()
    }
}

impl QuantifiedChcCompleteTrace {
    /// An advice candidate has no base evidence. Only full canonical original
    /// assertions AND exact same-model pins can construct the returned trace.
    pub(in crate::quantified::counterexample) fn from_discovery(
        problem: &QuantifiedChcProblem,
        derivation: super::super::Derivation,
        topology: [u8; 32],
        deadline: Instant,
        memory: Option<usize>,
        cancellation: &CancellationToken,
        control: &SourceControl<'_>,
    ) -> Option<Self> {
        if derivation::fingerprint(
            &derivation.clause_indices,
            &derivation.premise_steps,
            control,
        )? != topology
        {
            return None;
        }
        let rendered = render::render_complete(
            problem,
            &derivation.clause_indices,
            &derivation.premise_steps,
            control,
        )
        .ok()?;
        let registry = registry(problem, control)?;
        let advice = render::render_advice(
            problem,
            &derivation.clause_indices,
            &derivation.premise_steps,
            control,
        )
        .ok()?;
        let (bindings, functions) = acquire::run_query(
            &rendered.original,
            &advice,
            problem,
            &registry,
            deadline,
            memory,
            cancellation,
            control,
        )?;
        drop(advice);
        let pinned = pins::render(
            &rendered, &bindings, &functions, problem, &registry, control,
        )?;
        if !replay::validate(&pinned, deadline, memory, cancellation, control) {
            return None;
        }
        // Only NOW can canonical original source become base CEX evidence.
        control.bytes(problem.source_smtlib().len())?;
        let source = Arc::from(problem.source_smtlib());
        let base = QuantifiedChcCounterexample {
            source,
            clause_indices: derivation.clause_indices,
            premise_steps: derivation.premise_steps,
            topology_sha256: topology,
            obligation: rendered.original.obligation,
            memory_budget: memory,
        };
        drop((rendered.assertions, rendered.original.bindings, registry));
        control.poll()?;
        Some(Self {
            base,
            bindings,
            functions,
            pinned_obligation: pinned,
        })
    }
}

impl QuantifiedChcCounterexample {
    /// Acquire one accepted assignment and retain complete native array DATA.
    /// All original assertions and pins are rechecked under ONE global lexical
    /// environment; no lambda text is independently reparsed per occurrence.
    /// The old literal trace/artifact APIs are unchanged. No MODEL_CHECKER_CONSUMER adoption
    /// or complete original-input interpreter playback is implied.
    pub fn complete_trace(
        &self,
        problem: &QuantifiedChcProblem,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> Option<QuantifiedChcCompleteTrace> {
        attempt(
            self,
            time_budget,
            cancellation,
            |deadline, memory, token, control| {
                let rendered = bound(self, problem, control)?;
                let registry = registry(problem, control)?;
                let (bindings, functions) = acquire::run(
                    &rendered.original,
                    problem,
                    &registry,
                    deadline,
                    memory,
                    token,
                    control,
                )?;
                let pinned = pins::render(
                    &rendered, &bindings, &functions, problem, &registry, control,
                )?;
                if !replay::validate(&pinned, deadline, memory, token, control) {
                    return None;
                }
                let base = copy_base(self, rendered.original.obligation, memory, control)?;
                drop(registry);
                control.poll()?;
                Some(QuantifiedChcCompleteTrace {
                    base,
                    bindings,
                    functions,
                    pinned_obligation: pinned,
                })
            },
        )
    }
}

fn bound<'a>(
    base: &QuantifiedChcCounterexample,
    problem: &'a QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<render::CompleteRendered<'a>> {
    // Reuse the full canonical source/topology/fingerprint authority checks.
    let legacy = bound_render(base, problem, control)?;
    let result =
        render::render_complete(problem, &base.clause_indices, &base.premise_steps, control)
            .ok()?;
    control.bytes(result.original.obligation.len())?;
    if result.original.obligation != legacy.obligation {
        return None;
    }
    drop(legacy);
    control.poll()?;
    Some(result)
}

fn attempt<T>(
    base: &QuantifiedChcCounterexample,
    time: Duration,
    cancellation: &CancellationToken,
    work: impl FnOnce(Instant, Option<usize>, &CancellationToken, &SourceControl<'_>) -> Option<T>,
) -> Option<T> {
    solve::checked_attempt(time, cancellation, |deadline, token| {
        let context = SmtContext::new();
        let memory = solve::tighter_budget(context.term_memory_budget, base.memory_budget);
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
