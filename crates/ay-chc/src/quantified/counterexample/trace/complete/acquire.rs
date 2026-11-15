// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete locals/functions from exactly one accepted immutable native model.

use super::*;
use ay_dpll::api::CompleteModelValue;

pub(super) fn run(
    rendered: &render::Rendered<'_>,
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Option<(
    Vec<QuantifiedChcCompleteTraceBinding>,
    Vec<ScalarFunctionModel>,
)> {
    run_query(
        rendered,
        &rendered.obligation,
        problem,
        registry,
        deadline,
        memory,
        cancellation,
        control,
    )
}

/// Candidate DATA may be acquired from equivalent search advice, but canonical
/// inventory and full original pinned native replay remain mandatory.
pub(super) fn run_query(
    rendered: &render::Rendered<'_>,
    query: &str,
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Option<(
    Vec<QuantifiedChcCompleteTraceBinding>,
    Vec<ScalarFunctionModel>,
)> {
    let (names, function_names) = requests(rendered, problem, control)?;
    // Preserve the old acquisition-vs-full-replay wall split, not a new limit.
    let now = Instant::now();
    let query_end = now.checked_add(deadline.checked_duration_since(now)? / 2)?;
    let (model, functions) = replay::extract_complete(
        query,
        &names,
        &function_names,
        query_end,
        memory,
        cancellation,
        control,
    )?;
    drop((names, function_names));
    if model.len() != rendered.bindings.len() {
        return None;
    }
    authenticate_functions(problem, &functions, control)?;
    let bindings = complete_bindings(rendered, model, registry, control)?;
    control.poll()?;
    Some((bindings, functions))
}

fn requests<'a>(
    rendered: &'a render::Rendered<'_>,
    problem: &'a QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<(Vec<&'a str>, Vec<&'a str>)> {
    let originals = &rendered.bindings;
    if originals.len() > MAX_BINDINGS {
        return None;
    }
    control.charge(originals.len())?;
    control.bytes(originals.len().checked_mul(std::mem::size_of::<&str>())?)?;
    let mut names = Vec::new();
    names.try_reserve_exact(originals.len()).ok()?;
    names.extend(originals.iter().map(|entry| entry.symbol.as_str()));
    let declarations = problem.function_declarations();
    control.charge(declarations.len())?;
    control.bytes(
        declarations
            .len()
            .checked_mul(std::mem::size_of::<&str>())?,
    )?;
    let mut functions = Vec::new();
    functions.try_reserve_exact(declarations.len()).ok()?;
    functions.extend(declarations.iter().map(|entry| entry.name()));
    Some((names, functions))
}

fn complete_bindings(
    rendered: &render::Rendered<'_>,
    model: Vec<CompleteModelValue>,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<Vec<QuantifiedChcCompleteTraceBinding>> {
    let originals = &rendered.bindings;
    control.bytes(
        originals
            .len()
            .checked_mul(std::mem::size_of::<QuantifiedChcCompleteTraceBinding>())?,
    )?;
    let mut bindings = Vec::new();
    bindings.try_reserve_exact(originals.len()).ok()?;
    for (original, value) in originals.iter().zip(model) {
        control.charge(1)?;
        let value = match value {
            CompleteModelValue::Literal(value) => QuantifiedChcCompleteValue::Literal(
                values::decode(&value, &original.variable.sort, registry, control)?,
            ),
            CompleteModelValue::FunctionalArray(value) => {
                if !snapshot_sort(&original.variable.sort, value.sort()) {
                    return None;
                }
                QuantifiedChcCompleteValue::FunctionalArray(value)
            }
        };
        control.bytes(
            original
                .variable
                .name
                .len()
                .checked_add(sort_bytes(&original.variable.sort)?)?,
        )?;
        bindings.push(QuantifiedChcCompleteTraceBinding {
            occurrence: original.occurrence,
            variable: original.variable.clone(),
            value,
        });
    }
    Some(bindings)
}

pub(super) fn snapshot_sort(expected: &crate::ChcSort, actual: &ay_core::Sort) -> bool {
    match (expected, actual) {
        (crate::ChcSort::Array(key, cell), ay_core::Sort::Array(array)) => {
            matches!(key.as_ref(), crate::ChcSort::BitVec(64))
                && matches!(&array.index_sort, ay_core::Sort::BitVec(width) if width.width == 64)
                && match (cell.as_ref(), &array.element_sort) {
                    (crate::ChcSort::Bool, ay_core::Sort::Bool) => true,
                    (crate::ChcSort::BitVec(width), ay_core::Sort::BitVec(actual)) => {
                        (1..=128).contains(width) && *width == actual.width
                    }
                    _ => false,
                }
        }
        _ => false,
    }
}

#[cfg(test)]
#[path = "acquire/stages.rs"]
mod stages;
