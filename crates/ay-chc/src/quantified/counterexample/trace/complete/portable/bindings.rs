// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original occurrence/name/sort manifest, never the wire, supplies authority.

use super::*;
use crate::term_bridge::sort::chc_sort_to_core;
use ay_dpll::api::ModelValue;

pub(super) fn export<'a>(
    trace: &'a QuantifiedChcCompleteTrace,
    registry: &Registry,
    catalog: &mut arrays::Catalog<'a>,
    control: &SourceControl<'_>,
) -> Option<Vec<wire::Step>> {
    let count = trace.clause_indices().len();
    if count == 0
        || count > wire::MAX_NODES
        || count != trace.premise_steps().len()
        || trace.bindings.len() > MAX_BINDINGS
    {
        return None;
    }
    let mut steps = Vec::new();
    arrays::reserve(&mut steps, count, control)?;
    let mut cursor = 0;
    for (occurrence, (&clause_index, premises)) in trace
        .clause_indices()
        .iter()
        .zip(trace.premise_steps())
        .enumerate()
    {
        let start = cursor;
        while trace
            .bindings
            .get(cursor)
            .is_some_and(|entry| entry.occurrence == occurrence)
        {
            control.debit(1, 0)?;
            cursor += 1;
        }
        let mut bindings = Vec::new();
        arrays::reserve(&mut bindings, cursor.checked_sub(start)?, control)?;
        for binding in &trace.bindings[start..cursor] {
            let value = match &binding.value {
                QuantifiedChcCompleteValue::Literal(value) => wire::Value::Literal {
                    value: values::literal(value, &binding.variable.sort, registry, control)?,
                },
                QuantifiedChcCompleteValue::FunctionalArray(array) => {
                    catalog.value(array, &binding.variable.sort, control)?
                }
            };
            control.bytes(binding.variable.name.len())?;
            bindings.push(wire::Local {
                name: binding.variable.name.clone(),
                value,
            });
        }
        control.bytes(premises.len().checked_mul(std::mem::size_of::<usize>())?)?;
        steps.push(wire::Step {
            clause_index,
            premises: premises.clone(),
            bindings,
        });
    }
    control.poll()?;
    (cursor == trace.bindings.len()).then_some(steps)
}

pub(super) fn import(
    wire: &wire::Wire,
    rendered: &render::CompleteRendered<'_>,
    registry: &Registry,
    graphs: &[Arc<ArraySnapshot>],
    control: &SourceControl<'_>,
) -> Option<Vec<QuantifiedChcCompleteTraceBinding>> {
    let count = rendered.original.bindings.len();
    if count > MAX_BINDINGS {
        return None;
    }
    let locals = manifest(wire, &rendered.original, control)?;
    let decoded = literals(&locals, &rendered.original, registry, control)?;
    materialize(&locals, rendered, graphs, decoded, registry, control)
}

fn manifest<'a>(
    wire: &'a wire::Wire,
    rendered: &render::Rendered<'_>,
    control: &SourceControl<'_>,
) -> Option<Vec<&'a wire::Local>> {
    let count = rendered.bindings.len();
    let mut locals = Vec::new();
    arrays::reserve(&mut locals, count, control)?;
    for (occurrence, step) in wire.steps.iter().enumerate() {
        for local in &step.bindings {
            control.debit(local.name.len().checked_add(1)?, 0)?;
            let original = rendered.bindings.get(locals.len())?;
            if original.occurrence != occurrence || original.variable.name != local.name {
                return None;
            }
            locals.push(local);
        }
    }
    if locals.len() != count {
        return None;
    }
    control.poll()?;
    Some(locals)
}

fn materialize(
    locals: &[&wire::Local],
    rendered: &render::CompleteRendered<'_>,
    graphs: &[Arc<ArraySnapshot>],
    decoded: Vec<ModelValue>,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<Vec<QuantifiedChcCompleteTraceBinding>> {
    let mut decoded = decoded.into_iter();
    let mut used = Vec::new();
    arrays::reserve(&mut used, graphs.len(), control)?;
    used.resize(graphs.len(), false);
    let mut bindings = Vec::new();
    arrays::reserve(&mut bindings, locals.len(), control)?;
    for (local, original) in locals.iter().zip(&rendered.original.bindings) {
        let value = match &local.value {
            wire::Value::Literal { .. } => QuantifiedChcCompleteValue::Literal(values::decode(
                &decoded.next()?,
                &original.variable.sort,
                registry,
                control,
            )?),
            wire::Value::Functional { graph } => {
                let array = graphs.get(*graph)?;
                if !acquire::snapshot_sort(&original.variable.sort, array.sort()) {
                    return None;
                }
                *used.get_mut(*graph)? = true;
                QuantifiedChcCompleteValue::FunctionalArray(Arc::clone(array))
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
    control.debit(used.len().checked_add(1)?, 0)?;
    if decoded.next().is_some() || used.iter().any(|entry| !entry) {
        return None;
    }
    drop((decoded, used));
    control.poll()?;
    Some(bindings)
}

fn literals(
    locals: &[&wire::Local],
    rendered: &render::Rendered<'_>,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<Vec<ModelValue>> {
    let mut sorts = Vec::new();
    let mut texts = Vec::new();
    arrays::reserve(&mut sorts, locals.len(), control)?;
    arrays::reserve(&mut texts, locals.len(), control)?;
    for (local, original) in locals.iter().zip(&rendered.bindings) {
        control.debit(1, 0)?;
        if let wire::Value::Literal { value } = &local.value {
            let bytes = sort_bytes(&original.variable.sort)?;
            control.debit(bytes.checked_add(value.len())?, bytes.checked_mul(4)?)?;
            registry.validate_sort(&original.variable.sort).ok()?;
            sorts.push(chc_sort_to_core(&original.variable.sort));
            texts.push(value.as_str());
        }
    }
    if texts.is_empty() {
        return Some(Vec::new());
    }
    let mut requests = Vec::new();
    arrays::reserve(&mut requests, texts.len(), control)?;
    for (text, sort) in texts.iter().zip(&sorts) {
        requests.push((*text, sort));
    }
    // The same bounded typed decoder and whole-batch reservation as the
    // literal artifact. No new allowance is granted per local or occurrence.
    control.bytes(16 * 1024 * 1024)?;
    control.poll()?;
    let decoded = ModelValue::decode_typed_literals(&requests).ok()?;
    drop(requests);
    drop(texts);
    drop(sorts);
    control.poll()?;
    Some(decoded)
}
