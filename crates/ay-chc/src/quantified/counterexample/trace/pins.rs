// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact local pins and closed total-function definitions, never a projection
//! of the source premises or a finite set of sampled function applications.

use super::*;
use ay_dpll::api::ScalarFunctionModel;

const MAX_OUTPUT: usize = 8 * 1024 * 1024;

pub(super) fn render(
    rendered: &render::Rendered<'_>,
    bindings: &[QuantifiedChcTraceBinding],
    function_models: &[ScalarFunctionModel],
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<String> {
    if bindings.len() > MAX_BINDINGS || bindings.len() != rendered.bindings.len() {
        return None;
    }
    let body = rendered.obligation.strip_suffix("(check-sat)\n")?;
    let mut text = String::new();
    let segment = &rendered.function_declarations;
    body.get(segment.clone())?;
    push(&mut text, body.get(..segment.start)?, control)?;
    definitions(&mut text, function_models, problem, control)?;
    push(&mut text, body.get(segment.end..)?, control)?;
    for (original, binding) in rendered.bindings.iter().zip(bindings) {
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
        let literal = values::literal(&binding.value, &binding.variable.sort, registry, control)?;
        push(&mut text, "(assert (= ", control)?;
        // Fresh names come only from the source-censused renderer, never the
        // retained value/model or a caller-supplied symbol string.
        push(&mut text, &original.symbol, control)?;
        push(&mut text, " ", control)?;
        push(&mut text, &literal, control)?;
        push(&mut text, "))\n", control)?;
    }
    push(&mut text, "(check-sat)\n", control)?;
    control.poll()?;
    Some(text)
}

fn definitions(
    text: &mut String,
    models: &[ScalarFunctionModel],
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<()> {
    authenticate_functions(problem, models, control)?;
    for model in models {
        control.charge(1)?;
        // The DPLL type is construction-sealed: its decoder checked the exact
        // signature and a closed, well-typed total body. Never substitute a raw
        // caller string, ground observation list or invented default here.
        push(text, model.definition_smtlib(), control)?;
        push(text, "\n", control)?;
    }
    control.poll()
}

fn push(text: &mut String, piece: &str, control: &SourceControl<'_>) -> Option<()> {
    control.charge(1)?;
    if text.len().checked_add(piece.len())? > MAX_OUTPUT {
        return None;
    }
    control.bytes(piece.len().checked_mul(2)?)?;
    text.try_reserve(piece.len()).ok()?;
    text.push_str(piece);
    Some(())
}
