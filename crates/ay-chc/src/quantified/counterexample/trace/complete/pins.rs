// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! ONE lexical array environment and ONE conjunction of every original body.

use super::*;

const MAX_OUTPUT: usize = 8 * 1024 * 1024;

pub(super) fn render(
    rendered: &render::CompleteRendered<'_>,
    bindings: &[QuantifiedChcCompleteTraceBinding],
    functions: &[ScalarFunctionModel],
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<String> {
    let result = run(rendered, bindings, functions, problem, registry, control);
    if result.is_none() {
        control.stop();
    }
    result
}

fn run(
    rendered: &render::CompleteRendered<'_>,
    bindings: &[QuantifiedChcCompleteTraceBinding],
    functions: &[ScalarFunctionModel],
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<String> {
    control.poll()?;
    if bindings.len() > MAX_BINDINGS || bindings.len() != rendered.original.bindings.len() {
        return None;
    }
    authenticate_functions(problem, functions, control)?;
    let environment = snapshots::build(&rendered.original, bindings, problem, control)?;
    let mut text = String::new();
    header(&mut text, rendered, functions, control)?;
    push(&mut text, "(assert ", control)?;
    // Nested single-binding lets implement topological dependencies. A single
    // parallel let would resolve sibling references against the wrong scope.
    for definition in &environment.definitions {
        for piece in [
            "(let ((",
            definition.name.as_str(),
            " ",
            definition.body.as_str(),
            ")) ",
        ] {
            push(&mut text, piece, control)?;
        }
    }
    push(&mut text, "(and", control)?;
    for payload in &rendered.assertions {
        push(&mut text, " ", control)?;
        push(
            &mut text,
            rendered.original.obligation.get(payload.clone())?,
            control,
        )?;
    }
    pins(
        &mut text,
        rendered,
        bindings,
        &environment,
        registry,
        control,
    )?;
    push(&mut text, ")", control)?;
    for _ in &environment.definitions {
        push(&mut text, ")", control)?;
    }
    push(&mut text, ")\n(check-sat)\n", control)?;
    drop(environment);
    control.poll()?;
    Some(text)
}

fn header(
    text: &mut String,
    rendered: &render::CompleteRendered<'_>,
    models: &[ScalarFunctionModel],
    control: &SourceControl<'_>,
) -> Option<()> {
    let original = &rendered.original;
    let segment = &original.function_declarations;
    if segment.end > rendered.prefix_end {
        return None;
    }
    push(text, original.obligation.get(..segment.start)?, control)?;
    for model in models {
        push(text, model.definition_smtlib(), control)?;
        push(text, "\n", control)?;
    }
    push(
        text,
        original.obligation.get(segment.end..rendered.prefix_end)?,
        control,
    )
}

fn pins(
    text: &mut String,
    rendered: &render::CompleteRendered<'_>,
    bindings: &[QuantifiedChcCompleteTraceBinding],
    environment: &snapshots::Environment,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<()> {
    if environment.bindings.len() != bindings.len() {
        return None;
    }
    for ((original, binding), root) in rendered
        .original
        .bindings
        .iter()
        .zip(bindings)
        .zip(&environment.bindings)
    {
        control.charge(1)?;
        control.bytes(
            binding
                .variable
                .name
                .len()
                .checked_add(sort_bytes(&binding.variable.sort)?)?,
        )?;
        if original.occurrence != binding.occurrence || original.variable != &binding.variable {
            return None;
        }
        let literal;
        let value = match (&binding.value, root) {
            (QuantifiedChcCompleteValue::Literal(value), None) => {
                literal = values::literal(value, &binding.variable.sort, registry, control)?;
                literal.as_str()
            }
            (QuantifiedChcCompleteValue::FunctionalArray(value), Some(root))
                if acquire::snapshot_sort(&binding.variable.sort, value.sort()) =>
            {
                environment.name(*root)?
            }
            _ => return None,
        };
        for piece in [" (= ", original.symbol.as_str(), " ", value, ")"] {
            push(text, piece, control)?;
        }
    }
    control.poll()
}

fn push(text: &mut String, piece: &str, control: &SourceControl<'_>) -> Option<()> {
    control.debit(piece.len().checked_add(1)?, piece.len().checked_mul(2)?)?;
    if text.len().checked_add(piece.len())? > MAX_OUTPUT {
        return None;
    }
    text.try_reserve(piece.len()).ok()?;
    text.push_str(piece);
    Some(())
}
