// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Manifest-aligned closed literals. Wire sort annotations never supply types.

use super::*;
use crate::term_bridge::sort::chc_sort_to_core;
use ay_dpll::api::ModelValue;

pub(super) fn export(
    bindings: &[QuantifiedChcTraceBinding],
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<Vec<wire::Local>> {
    control.bytes(
        bindings
            .len()
            .checked_mul(std::mem::size_of::<wire::Local>())?,
    )?;
    let mut locals = Vec::new();
    locals.try_reserve_exact(bindings.len()).ok()?;
    for binding in bindings {
        control.charge(1)?;
        let value = values::literal(&binding.value, &binding.variable.sort, registry, control)?;
        control.bytes(binding.variable.name.len())?;
        locals.push(wire::Local {
            name: binding.variable.name.clone(),
            value,
        });
    }
    control.poll()?;
    Some(locals)
}

pub(super) fn import(
    steps: &[wire::Step],
    rendered: &render::Rendered<'_>,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<Vec<QuantifiedChcTraceBinding>> {
    let count = rendered.bindings.len();
    if count > MAX_BINDINGS {
        return None;
    }
    control.bytes(count.checked_mul(std::mem::size_of::<&wire::Local>())?)?;
    let mut locals = Vec::new();
    locals.try_reserve_exact(count).ok()?;
    for (occurrence, step) in steps.iter().enumerate() {
        control.charge(1)?;
        for local in &step.bindings {
            let original = rendered.bindings.get(locals.len())?;
            control.bytes(local.name.len())?;
            if original.occurrence != occurrence || original.variable.name != local.name {
                return None;
            }
            locals.push(local);
        }
    }
    if locals.len() != count {
        return None;
    }
    if count == 0 {
        control.poll()?;
        return Some(Vec::new());
    }
    let sorts = source_sorts(rendered, registry, control)?;
    control.bytes(count.checked_mul(std::mem::size_of::<(&str, &ay_core::Sort)>())?)?;
    let mut input = Vec::new();
    input.try_reserve_exact(count).ok()?;
    for (local, sort) in locals.iter().zip(&sorts) {
        control.charge(1)?;
        input.push((local.value.as_str(), sort));
    }
    // One data-only decoder covers the entire batch. Earmark its full shared
    // copy/AST/value allowance, never reset that allowance per occurrence.
    // Numeric-library scratch and opaque bounded decoding intervals are not
    // exact heap accounting or interrupt-latency guarantees.
    control.bytes(16 * 1024 * 1024)?;
    let decoded = ModelValue::decode_typed_literals(&input).ok()?;
    control.poll()?;
    drop(input);
    drop(sorts);
    drop(locals);
    materialize(decoded, rendered, registry, control)
}

fn source_sorts(
    rendered: &render::Rendered<'_>,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<Vec<ay_core::Sort>> {
    control.bytes(
        rendered
            .bindings
            .len()
            .checked_mul(std::mem::size_of::<ay_core::Sort>())?,
    )?;
    // Admit every borrowed metadata tree before the first converted sort is
    // allocated. Record names/copies and traversal scratch have a conservative
    // multiplier; registry validation forbids recursive/opaque fallbacks.
    for binding in &rendered.bindings {
        let bytes = sort_bytes(&binding.variable.sort)?;
        control.charge(bytes.div_ceil(64))?;
        control.bytes(bytes.checked_mul(4)?)?;
        registry.validate_sort(&binding.variable.sort).ok()?;
    }
    let mut sorts = Vec::new();
    sorts.try_reserve_exact(rendered.bindings.len()).ok()?;
    for binding in &rendered.bindings {
        control.charge(1)?;
        sorts.push(chc_sort_to_core(&binding.variable.sort));
    }
    control.poll()?;
    Some(sorts)
}

fn materialize(
    decoded: Vec<ModelValue>,
    rendered: &render::Rendered<'_>,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<Vec<QuantifiedChcTraceBinding>> {
    if decoded.len() != rendered.bindings.len() {
        return None;
    }
    control.bytes(
        decoded
            .len()
            .checked_mul(std::mem::size_of::<QuantifiedChcTraceBinding>())?,
    )?;
    let mut bindings = Vec::new();
    bindings.try_reserve_exact(decoded.len()).ok()?;
    for (model, original) in decoded.iter().zip(&rendered.bindings) {
        control.charge(1)?;
        let value = values::decode(model, &original.variable.sort, registry, control)?;
        control.bytes(
            original
                .variable
                .name
                .len()
                .checked_add(sort_bytes(&original.variable.sort)?)?,
        )?;
        bindings.push(QuantifiedChcTraceBinding {
            occurrence: original.occurrence,
            variable: original.variable.clone(),
            value,
        });
    }
    drop(decoded);
    control.poll()?;
    Some(bindings)
}
