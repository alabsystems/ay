// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded exact-source joins for already construction-sealed concrete traces.

use super::*;
use crate::quantified::{QuantifiedChcClauseView, QuantifiedChcSourceView};

/// Borrowed playback of an existing trace against its exact typed source.
///
/// Construction checks source, topology, complete bindings and retained pin
/// identity, but does not call a solver or renew the trace's SAT authority.
/// Use [`QuantifiedChcTrace::recheck`] for fresh same-assignment validation.
/// This is neither an artifact decoder nor an aggregate-query proof conversion.
/// Accessors borrow unchanged values and expressions without allocating.
///
/// Neither owner can be dropped while the view is retained:
///
/// ```compile_fail
/// use ay_chc::{CancellationToken, quantified::{QuantifiedChcProblem,
///     QuantifiedChcTrace, QuantifiedChcTraceView}};
/// use std::time::Duration;
/// fn escape<'t>(trace: &'t QuantifiedChcTrace, source: QuantifiedChcProblem,
///     token: &CancellationToken) -> QuantifiedChcTraceView<'t, 'static> {
///     trace.view_for(&source, Duration::from_secs(1), token).unwrap()
/// }
/// ```
///
/// ```compile_fail
/// use ay_chc::{CancellationToken, quantified::{QuantifiedChcProblem,
///     QuantifiedChcTrace, QuantifiedChcTraceView}};
/// use std::time::Duration;
/// fn escape<'s>(trace: QuantifiedChcTrace, source: &'s QuantifiedChcProblem,
///     token: &CancellationToken) -> QuantifiedChcTraceView<'static, 's> {
///     trace.view_for(source, Duration::from_secs(1), token).unwrap()
/// }
/// ```
#[derive(Debug, Clone, Copy)]
pub struct QuantifiedChcTraceView<'trace, 'source> {
    trace: &'trace QuantifiedChcTrace,
    source: QuantifiedChcSourceView<'source>,
}

/// One independently scoped occurrence, joined to its complete source clause.
///
/// Clause indices are local to the supplied source, including when it is a
/// query slice. They are not aggregate indices or original Rust/MIR locations.
/// Universal binders stay in the clause premises and never become bindings.
/// There is no unchecked public constructor or mutable value access.
///
/// ```compile_fail
/// use ay_chc::quantified::QuantifiedChcTraceStepView;
/// let fabricated = QuantifiedChcTraceStepView {};
/// ```
#[derive(Debug, Clone, Copy)]
pub struct QuantifiedChcTraceStepView<'trace, 'source> {
    occurrence: usize,
    clause: QuantifiedChcClauseView<'source>,
    premise_steps: &'trace [usize],
    bindings: &'trace [QuantifiedChcTraceBinding],
}

impl QuantifiedChcTrace {
    /// Join this trace to the exact complete typed source without solving.
    ///
    /// Source, topology, manifest or pin mismatch returns `None`, as do resource
    /// exhaustion and observed cancellation. The original term allowance and
    /// tighter enclosing limits apply. Temporary rendering is bounded; no
    /// values, source expressions or function models are cloned into the view.
    /// This checks membership of existing sealed evidence, not fresh SAT.
    pub fn view_for<'trace, 'source>(
        &'trace self,
        problem: &'source QuantifiedChcProblem,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> Option<QuantifiedChcTraceView<'trace, 'source>> {
        solve::checked_attempt(time_budget, cancellation, |deadline, attempt| {
            let context = SmtContext::new();
            let memory = solve::tighter_budget(context.term_memory_budget, self.base.memory_budget);
            if memory == Some(0) {
                return None;
            }
            let _memory = SmtContext::scoped_thread_term_memory_budget(memory);
            let _deadline = ScopedSmtDeadline::install_until(deadline);
            let control = SourceControl::new(deadline, attempt);
            authenticate(self, problem, &control)?;
            Some(QuantifiedChcTraceView {
                trace: self,
                source: problem.source_view(),
            })
        })
    }
}

impl<'trace, 'source> QuantifiedChcTraceView<'trace, 'source> {
    /// All declarations and clauses, including unused entries and full premises.
    pub fn source(&self) -> QuantifiedChcSourceView<'source> {
        self.source
    }

    /// Complete shared function interpretations, not per-occurrence samples.
    pub fn function_models(&self) -> &'trace [ScalarFunctionModel] {
        self.trace.function_models()
    }

    /// Borrow one occurrence, or `None` for an out-of-range occurrence index.
    pub fn step(&self, occurrence: usize) -> Option<QuantifiedChcTraceStepView<'trace, 'source>> {
        let index = *self.trace.clause_indices().get(occurrence)?;
        let bindings = self.trace.bindings();
        let start = bindings.partition_point(|binding| binding.occurrence < occurrence);
        let end = bindings.partition_point(|binding| binding.occurrence <= occurrence);
        Some(QuantifiedChcTraceStepView {
            occurrence,
            clause: self.source.clause(index)?,
            premise_steps: self.trace.premise_steps().get(occurrence)?,
            bindings: bindings.get(start..end)?,
        })
    }

    /// All occurrences in checked topological order. Repeated source clauses
    /// remain separate steps, each with its own contiguous binding slice.
    pub fn steps(
        &self,
    ) -> impl DoubleEndedIterator<Item = QuantifiedChcTraceStepView<'trace, 'source>> + Clone + '_
    {
        (0..self.trace.clause_indices().len()).filter_map(|occurrence| self.step(occurrence))
    }
}

impl<'trace, 'source> QuantifiedChcTraceStepView<'trace, 'source> {
    /// Position in the trace, not a source clause or aggregate query index.
    pub fn occurrence(&self) -> usize {
        self.occurrence
    }

    /// Source-local clause index. Repeated occurrences can have the same index.
    pub fn clause_index(&self) -> usize {
        self.clause.index()
    }

    /// Complete antecedent and head, with every original universal premise.
    pub fn clause(&self) -> QuantifiedChcClauseView<'source> {
        self.clause
    }

    /// Predecessor occurrences in this clause's body-predicate order.
    pub fn premise_steps(&self) -> &'trace [usize] {
        self.premise_steps
    }

    /// All canonical-source locals in lexical name order, including locals
    /// occurring only in premise matrices. No bound variable is synthesized.
    pub fn bindings(&self) -> &'trace [QuantifiedChcTraceBinding] {
        self.bindings
    }

    /// Exact complete value for a canonical-source local, or `None` if absent.
    pub fn source_binding(&self, name: &str) -> Option<&'trace SmtValue> {
        let index = self
            .bindings
            .binary_search_by(|binding| binding.variable.name.as_str().cmp(name))
            .ok()?;
        Some(self.bindings[index].value())
    }
}

fn authenticate(
    trace: &QuantifiedChcTrace,
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<()> {
    let rendered = bound_render(&trace.base, problem, control)?;
    let registry = registry(problem, control)?;
    let pinned = pins::render(
        &rendered,
        &trace.bindings,
        &trace.functions,
        problem,
        &registry,
        control,
    )?;
    control.bytes(pinned.len())?;
    let identical = pinned == trace.pinned_obligation;
    drop((pinned, rendered, registry));
    control.poll()?;
    identical.then_some(())
}

#[cfg(test)]
mod tests;
