// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Concrete occurrence values admitted only by fresh full-source pinned SAT.

use super::{derivation, render, replay, solve, values};
use super::{QuantifiedChcCounterexample, QuantifiedChcProblem, SourceControl};
use crate::quantified::records::{registry_bytes, sort_bytes, Registry};
use crate::smt::{ScopedSmtDeadline, SmtContext, SmtValue};
use crate::{CancellationToken, ChcVar};
use ay_core::time::Instant;
use ay_dpll::api::ScalarFunctionModel;
use std::sync::Arc;
use std::time::Duration;

mod artifact;
mod complete;
pub use complete::{
    QuantifiedChcCompleteTrace, QuantifiedChcCompleteTraceBinding, QuantifiedChcCompleteValue,
    QuantifiedChcValidatedCompleteTraceArtifact,
};
mod lift;
mod pins;
mod view;
pub use artifact::{QuantifiedChcTraceArtifactError, QuantifiedChcValidatedTraceArtifact};
pub use lift::QuantifiedChcTraceLiftError;
pub use view::{QuantifiedChcTraceStepView, QuantifiedChcTraceView};
#[cfg(test)]
mod tests;

const MAX_BINDINGS: usize = 4096;

/// One independently scoped source variable's complete concrete value.
///
/// Universal premise binders are not clause locals and never occur here. An
/// array value includes its default and every ordered override; a record value
/// includes every constructor field, not just observed selectors or cells.
#[derive(Debug)]
pub struct QuantifiedChcTraceBinding {
    occurrence: usize,
    variable: ChcVar,
    value: SmtValue,
}

impl QuantifiedChcTraceBinding {
    /// Index into the trace's topologically ordered clause occurrences.
    pub fn occurrence(&self) -> usize {
        self.occurrence
    }

    /// Original canonical-source variable, including its authenticated sort.
    pub fn variable(&self) -> &ChcVar {
        &self.variable
    }

    /// Complete typed value from the assignment checked by pinned replay.
    pub fn value(&self) -> &SmtValue {
        &self.value
    }
}

/// Construction-sealed concrete witness for an original quantified derivation.
///
/// Admission fixes every occurrence-local value and complete ordinary function
/// interpretation, then freshly validates the full original conjunction,
/// including all universal premises. This is not an
/// ordinary quantifier-free GroundDerivation or portable kernel proof. The
/// versioned artifact API requires fresh native replay at both boundaries;
/// it does not implement MODEL_CHECKER_CONSUMER adoption or source-interpreter playback.
/// There is no unchecked public constructor.
#[derive(Debug)]
pub struct QuantifiedChcTrace {
    base: QuantifiedChcCounterexample,
    bindings: Vec<QuantifiedChcTraceBinding>,
    functions: Vec<ScalarFunctionModel>,
    pinned_obligation: String,
}

impl QuantifiedChcTrace {
    /// Complete canonical source, including unused clauses.
    pub fn source_smtlib(&self) -> &str {
        self.base.source_smtlib()
    }

    /// Original indices in topological occurrence order; repetitions are fresh.
    pub fn clause_indices(&self) -> &[usize] {
        self.base.clause_indices()
    }

    /// All ordered body-predicate edges, exactly as in the checked source tree.
    pub fn premise_steps(&self) -> &[Vec<usize>] {
        self.base.premise_steps()
    }

    /// Complete local assignment in occurrence/lexical-variable order.
    pub fn bindings(&self) -> &[QuantifiedChcTraceBinding] {
        &self.bindings
    }

    /// Complete global interpretations in original declaration order.
    ///
    /// Functions are shared across every occurrence, including functions used
    /// only by universal premises or unused by this selected derivation.
    pub fn function_models(&self) -> &[ScalarFunctionModel] {
        &self.functions
    }

    /// Full original obligation with every local and total function fixed.
    pub fn replay_obligation(&self) -> &str {
        &self.pinned_obligation
    }

    /// Rebuild all pins and freshly check this same concrete assignment.
    ///
    /// No unpinned fallback is allowed. Source, topology, manifest, sort or value
    /// changes refuse; cancellation, exhausted budgets and incomplete SAT also
    /// refuse. The original term budget and any tighter parent budget apply.
    pub fn recheck(
        &self,
        problem: &QuantifiedChcProblem,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> bool {
        solve::checked_attempt(time_budget, cancellation, |deadline, attempt| {
            let context = SmtContext::new();
            let memory = solve::tighter_budget(context.term_memory_budget, self.base.memory_budget);
            let _memory = SmtContext::scoped_thread_term_memory_budget(memory);
            let _deadline = ScopedSmtDeadline::install_until(deadline);
            let control = SourceControl::new(deadline, attempt);
            let rendered = bound_render(&self.base, problem, &control)?;
            let registry = registry(problem, &control)?;
            let pinned = pins::render(
                &rendered,
                &self.bindings,
                &self.functions,
                problem,
                &registry,
                &control,
            )?;
            control.bytes(pinned.len())?;
            if pinned != self.pinned_obligation {
                return None;
            }
            let accepted = replay::validate(&pinned, deadline, memory, attempt, &control);
            drop((pinned, rendered, registry));
            control.poll()?;
            accepted.then_some(())
        })
        .is_some()
    }
}

impl QuantifiedChcCounterexample {
    /// Materialize a complete typed assignment and independently replay it.
    ///
    /// Fresh model acquisition uses at most half the remaining wall; full pinned
    /// replay uses the rest. All occurrence locals must decode exactly (at most
    /// 4096). Unsupported or opaque models return `None`, without invalidating
    /// this separate existential counterexample. Values may differ from the
    /// unretained model used when the original counterexample was discovered;
    /// the returned trace and all its rechecks fix one newly acquired assignment.
    /// Every ordinary source function must also have a supported complete
    /// scalar interpretation from that same acquisition. Missing or opaque
    /// functions refuse, even when unused; finite call observations are not a
    /// substitute for a total interpretation.
    pub fn concrete_trace(
        &self,
        problem: &QuantifiedChcProblem,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> Option<QuantifiedChcTrace> {
        solve::checked_attempt(time_budget, cancellation, |deadline, attempt| {
            let context = SmtContext::new();
            let memory = solve::tighter_budget(context.term_memory_budget, self.memory_budget);
            let _memory = SmtContext::scoped_thread_term_memory_budget(memory);
            let _deadline = ScopedSmtDeadline::install_until(deadline);
            let control = SourceControl::new(deadline, attempt);
            let rendered = bound_render(self, problem, &control)?;
            let registry = registry(problem, &control)?;
            let (bindings, functions) = acquire(
                &rendered, problem, &registry, deadline, memory, attempt, &control,
            )?;
            let pinned_obligation = pins::render(
                &rendered, &bindings, &functions, problem, &registry, &control,
            )?;
            if !replay::validate(&pinned_obligation, deadline, memory, attempt, &control) {
                return None;
            }
            let base = copy_base(self, rendered.obligation, memory, &control)?;
            drop((rendered.bindings, registry));
            control.poll()?;
            Some(QuantifiedChcTrace {
                base,
                bindings,
                functions,
                pinned_obligation,
            })
        })
    }
}

fn bound_render<'a>(
    evidence: &QuantifiedChcCounterexample,
    problem: &'a QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<render::Rendered<'a>> {
    control.poll()?;
    control.bytes(problem.source_smtlib().len())?;
    if evidence.source.as_ref() != problem.source_smtlib()
        || derivation::fingerprint(&evidence.clause_indices, &evidence.premise_steps, control)?
            != evidence.topology_sha256
    {
        return None;
    }
    let rendered = render::render_with_bindings(
        problem,
        &evidence.clause_indices,
        &evidence.premise_steps,
        control,
    )
    .ok()?;
    control.bytes(rendered.obligation.len())?;
    if rendered.bindings.len() > MAX_BINDINGS || rendered.obligation != evidence.obligation {
        return None;
    }
    control.poll()?;
    Some(rendered)
}

fn registry(problem: &QuantifiedChcProblem, control: &SourceControl<'_>) -> Option<Registry> {
    control.bytes(registry_bytes(problem.source_problem())?)?;
    let registry = Registry::new(problem.source_problem()).ok()?;
    control.poll()?;
    Some(registry)
}

fn acquire(
    rendered: &render::Rendered<'_>,
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Option<(Vec<QuantifiedChcTraceBinding>, Vec<ScalarFunctionModel>)> {
    let count = rendered.bindings.len();
    if count > MAX_BINDINGS {
        return None;
    }
    control.bytes(count.checked_mul(std::mem::size_of::<&str>())?)?;
    let mut names = Vec::new();
    names.try_reserve_exact(count).ok()?;
    for binding in &rendered.bindings {
        control.charge(1)?;
        names.push(binding.symbol.as_str());
    }
    let functions = problem.function_declarations();
    control.bytes(functions.len().checked_mul(std::mem::size_of::<&str>())?)?;
    let mut function_names = Vec::new();
    function_names.try_reserve_exact(functions.len()).ok()?;
    for function in functions {
        control.charge(1)?;
        function_names.push(function.name());
    }
    let now = Instant::now();
    let query_deadline = now.checked_add(deadline.saturating_duration_since(now) / 2)?;
    let (model, functions) = replay::extract(
        &rendered.obligation,
        &names,
        &function_names,
        query_deadline,
        memory,
        cancellation,
        control,
    )?;
    drop((names, function_names));
    if model.len() != count {
        return None;
    }
    authenticate_functions(problem, &functions, control)?;
    control.bytes(count.checked_mul(std::mem::size_of::<QuantifiedChcTraceBinding>())?)?;
    let mut bindings = Vec::new();
    bindings.try_reserve_exact(count).ok()?;
    for (binding, value) in rendered.bindings.iter().zip(&model) {
        let value = values::decode(value, &binding.variable.sort, registry, control)?;
        control.bytes(
            binding
                .variable
                .name
                .len()
                .checked_add(sort_bytes(&binding.variable.sort)?)?,
        )?;
        bindings.push(QuantifiedChcTraceBinding {
            occurrence: binding.occurrence,
            variable: binding.variable.clone(),
            value,
        });
    }
    drop(model);
    control.poll()?;
    Some((bindings, functions))
}

fn authenticate_functions(
    problem: &QuantifiedChcProblem,
    functions: &[ScalarFunctionModel],
    control: &SourceControl<'_>,
) -> Option<()> {
    control.poll()?;
    let declarations = problem.function_declarations();
    if functions.len() != declarations.len() {
        return None;
    }
    // Cached source work bounds complete name/signature comparisons without
    // cloning schemas. Native models own their authenticated scalar metadata.
    control.charge(problem.functions.work())?;
    for (declaration, model) in declarations.iter().zip(functions) {
        authenticate_function(
            declaration,
            model.name(),
            model.arg_sorts(),
            model.result_sort(),
            control,
        )?;
    }
    control.poll()
}

fn authenticate_function(
    declaration: &crate::quantified::QuantifiedChcFunction,
    name: &str,
    args: &[ay_core::Sort],
    result: &ay_core::Sort,
    control: &SourceControl<'_>,
) -> Option<()> {
    control.charge(1)?;
    if declaration.name() != name
        || declaration.arg_sorts().len() != args.len()
        || !same_scalar_sort(declaration.result_sort(), result)
    {
        return None;
    }
    for (expected, actual) in declaration.arg_sorts().iter().zip(args) {
        control.charge(1)?;
        if !same_scalar_sort(expected, actual) {
            return None;
        }
    }
    control.poll()
}

fn same_scalar_sort(expected: &crate::ChcSort, actual: &ay_core::Sort) -> bool {
    match (expected, actual) {
        (crate::ChcSort::Bool, ay_core::Sort::Bool) => true,
        (crate::ChcSort::BitVec(expected), ay_core::Sort::BitVec(actual)) => {
            (1..=crate::MAX_BITVECTOR_WIDTH).contains(expected) && *expected == actual.width
        }
        _ => false,
    }
}

fn copy_base(
    base: &QuantifiedChcCounterexample,
    obligation: String,
    memory_budget: Option<usize>,
    control: &SourceControl<'_>,
) -> Option<QuantifiedChcCounterexample> {
    // Structural admission already authenticated every occurrence and edge.
    // Charge the complete dynamic copy before cloning either array.
    control.bytes(
        base.clause_indices
            .len()
            .checked_mul(std::mem::size_of::<usize>())?,
    )?;
    control.bytes(
        base.premise_steps
            .len()
            .checked_mul(std::mem::size_of::<Vec<usize>>())?,
    )?;
    for edges in &base.premise_steps {
        control.bytes(edges.len().checked_mul(std::mem::size_of::<usize>())?)?;
    }
    let result = QuantifiedChcCounterexample {
        source: Arc::clone(&base.source),
        clause_indices: base.clause_indices.clone(),
        premise_steps: base.premise_steps.clone(),
        topology_sha256: base.topology_sha256,
        obligation,
        memory_budget,
    };
    control.poll()?;
    Some(result)
}
