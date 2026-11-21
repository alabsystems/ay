// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Refuse needed source bindings that the v1 native history cannot represent.
//! Text assertions are supported when their dependencies are already recorded;
//! this is a dependency check, not a blanket text-origin ban or header inference.

use ay_core::{Sort, Symbol, TermData, TermId};
use ay_frontend::DeclarationKind;

use super::super::{final_check_sat_assumptions, NativeReplayEventKind};
use super::meter::{self, Meter, Result};
use super::plan::Plan;
use crate::api::NativeReplayExportError as Error;

fn equal(left: &str, right: &str, meter: &mut Meter<'_>) -> Result<bool> {
    meter.charge(left.len().saturating_add(right.len()).saturating_add(1), 0)?;
    Ok(left == right)
}

fn recorded(
    plan: &Plan<'_>,
    core: &str,
    variable: Option<TermId>,
    meter: &mut Meter<'_>,
) -> Result<bool> {
    for identity in &plan.identities {
        if equal(identity.core, core, meter)?
            && variable.is_none_or(|term| identity.info.term == Some(term))
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn carrier_recorded(plan: &Plan<'_>, core: &str, meter: &mut Meter<'_>) -> Result<bool> {
    for &carrier in &plan.datatype_carriers {
        if equal(carrier, core, meter)? {
            return Ok(true);
        }
    }
    for declaration in &plan.sort_declarations {
        if equal(declaration.core, core, meter)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn binding(
    plan: &Plan<'_>,
    core: &str,
    variable: Option<TermId>,
    meter: &mut Meter<'_>,
) -> Result<()> {
    if recorded(plan, core, variable, meter)? {
        return Ok(());
    }
    let context = plan.solver.executor.context();
    meter.charge(
        context
            .native_input_symbol_storage_capacity()
            .saturating_mul(2),
        0,
    )?;
    for (surface, info) in context.native_input_symbol_storage_iter() {
        let identity = context.symbol_identity_name(surface, info);
        if !equal(identity, core, meter)? {
            continue;
        }
        // A lexical/free variable with a distinct TermId is not a use of a
        // coincidentally named global declaration. Bound variables are filtered
        // by the scope walk before this point.
        if variable.is_some_and(|term| info.term != Some(term)) {
            continue;
        }
        if info.declaration_kind() != DeclarationKind::Theory {
            return meter.fail(Error::UnsupportedSource {
                shape: "needed source binding absent from native v1 history",
            });
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum Flavor {
    Api,
    Engine,
}

fn sorts(plan: &Plan<'_>, root: &Sort, flavor: Flavor, meter: &mut Meter<'_>) -> Result<()> {
    let context = plan.solver.executor.context();
    let mut pending = Vec::new();
    meter.push(&mut pending, (root, 1usize))?;
    while let Some((sort, depth)) = pending.pop() {
        meter.depth(depth)?;
        match sort {
            Sort::Uninterpreted(name) => {
                meter::sort_lookup(context, name, meter)?;
                let recorded = carrier_recorded(plan, name, meter)?;
                if context.datatype_constructors(name).is_some() && !recorded {
                    return meter.fail(Error::UnsupportedSource {
                        shape: "needed datatype carrier absent from native v1 history",
                    });
                }
                match flavor {
                    Flavor::Engine => {
                        if !recorded && !equal(context.sort_surface_name(name), name, meter)? {
                            return meter.fail(Error::UnsupportedSource {
                                shape: "needed nominal sort binding absent from native v1 history",
                            });
                        }
                    }
                    Flavor::Api => {
                        if let Some(definition) = context.sort_definition(name) {
                            let identity =
                                matches!(definition, Sort::Uninterpreted(core) if core == name);
                            let native_datatype = if let Sort::Uninterpreted(core) = definition {
                                carrier_recorded(plan, core, meter)?
                            } else {
                                false
                            };
                            if !identity && !native_datatype {
                                return meter.fail(Error::UnsupportedSource {
                                    shape: "needed sort definition absent from native v1 history",
                                });
                            }
                        }
                    }
                }
            }
            Sort::Datatype(datatype) => {
                let mut present = false;
                for event in &plan.solver.native_replay_events {
                    meter.poll()?;
                    for original in event.kind.datatypes() {
                        if equal(&datatype.name, &original.name, meter)? {
                            present = true;
                            break;
                        }
                    }
                }
                if !present {
                    return meter.fail(Error::UnsupportedSource {
                        shape: "needed datatype declaration absent from native v1 history",
                    });
                }
                for constructor in &datatype.constructors {
                    for field in &constructor.fields {
                        meter.push(&mut pending, (&field.sort, depth.saturating_add(1)))?;
                    }
                }
            }
            Sort::Array(array) => {
                meter.push(&mut pending, (&array.index_sort, depth.saturating_add(1)))?;
                meter.push(&mut pending, (&array.element_sort, depth.saturating_add(1)))?;
            }
            Sort::Seq(element) => {
                meter.push(&mut pending, (element.as_ref(), depth.saturating_add(1)))?
            }
            _ => {} // Raw admission has already refused future v1 sort variants.
        }
    }
    Ok(())
}

enum Task<'a> {
    Visit(TermId, usize),
    LetBody(&'a [(String, TermId)], TermId, usize),
    EndScope(usize),
}

fn seen_name<'a>(names: &mut Vec<&'a str>, name: &'a str, meter: &mut Meter<'_>) -> Result<bool> {
    for &prior in names.iter() {
        if equal(prior, name, meter)? {
            return Ok(true);
        }
    }
    meter.push(names, name)?;
    Ok(false)
}

pub(super) fn source(plan: &Plan<'_>, meter: &mut Meter<'_>) -> Result<()> {
    // API-side source aliases may have been lowered away in the engine DAG.
    // Without a corresponding native declaration the v1 reader cannot recover
    // those definitions, even when the engine sort is a simple scalar.
    for declaration in &plan.declarations {
        sorts(plan, declaration.sort, Flavor::Api, meter)?;
    }
    for function in &plan.functions {
        for sort in function.domain {
            sorts(plan, sort, Flavor::Api, meter)?;
        }
        sorts(plan, function.range, Flavor::Api, meter)?;
    }
    for event in &plan.solver.native_replay_events {
        for datatype in event.kind.datatypes() {
            for constructor in &datatype.constructors {
                for field in &constructor.fields {
                    sorts(plan, &field.sort, Flavor::Api, meter)?;
                }
            }
        }
    }

    let terms = plan.solver.terms();
    let mut pending = Vec::new();
    let mut bound = Vec::<&str>::new();
    let mut names = Vec::<&str>::new();
    let mut free_variables = Vec::<TermId>::new();
    let mut checked_sorts = Vec::<TermId>::new();
    let roots = plan
        .assertions
        .iter()
        .map(|assertion| assertion.term)
        .chain(
            final_check_sat_assumptions(&plan.solver.native_replay_events)
                .into_iter()
                .flatten()
                .copied(),
        );
    for root in roots {
        meter.push(&mut pending, Task::Visit(root, 1))?;
        while let Some(task) = pending.pop() {
            meter.poll()?;
            match task {
                Task::EndScope(length) => bound.truncate(length),
                Task::LetBody(bindings, body, depth) => {
                    let before = bound.len();
                    for (name, _) in bindings {
                        meter.push(&mut bound, name.as_str())?;
                    }
                    meter.push(&mut pending, Task::EndScope(before))?;
                    meter.push(&mut pending, Task::Visit(body, depth.saturating_add(1)))?;
                }
                Task::Visit(term, depth) => {
                    meter.depth(depth)?;
                    meter.charge(checked_sorts.len(), 0)?;
                    if !checked_sorts.contains(&term) {
                        sorts(plan, terms.sort(term), Flavor::Engine, meter)?;
                        meter.push(&mut checked_sorts, term)?;
                    }
                    match terms.get(term) {
                        TermData::Var(name, _) => {
                            let mut local = false;
                            for &binder in bound.iter().rev() {
                                if equal(binder, name, meter)? {
                                    local = true;
                                    break;
                                }
                            }
                            meter.charge(free_variables.len(), 0)?;
                            if !local && !free_variables.contains(&term) {
                                binding(plan, name, Some(term), meter)?;
                                meter.push(&mut free_variables, term)?;
                            }
                        }
                        TermData::App(symbol, arguments) => {
                            if let Symbol::Named(name) = symbol {
                                if !seen_name(&mut names, name.as_str(), meter)? {
                                    binding(plan, name, None, meter)?;
                                }
                            }
                            for dependency in [
                                terms.get_as_array_func(term),
                                terms.get_array_map(term).map(|(name, _)| name),
                            ]
                            .into_iter()
                            .flatten()
                            {
                                if !seen_name(&mut names, dependency, meter)? {
                                    binding(plan, dependency, None, meter)?;
                                }
                            }
                            for &argument in arguments.iter().rev() {
                                meter.push(
                                    &mut pending,
                                    Task::Visit(argument, depth.saturating_add(1)),
                                )?;
                            }
                        }
                        TermData::Let(bindings, body) => {
                            meter.push(&mut pending, Task::LetBody(bindings, *body, depth))?;
                            // Simultaneous let RHSs are outside the new scope.
                            for (_, value) in bindings.iter().rev() {
                                meter.push(
                                    &mut pending,
                                    Task::Visit(*value, depth.saturating_add(1)),
                                )?;
                            }
                        }
                        TermData::Forall(variables, body, triggers)
                        | TermData::Exists(variables, body, triggers) => {
                            let before = bound.len();
                            for (name, sort) in variables {
                                sorts(plan, sort, Flavor::Engine, meter)?;
                                meter.push(&mut bound, name.as_str())?;
                            }
                            meter.push(&mut pending, Task::EndScope(before))?;
                            for trigger in triggers.iter().rev() {
                                for &term in trigger.iter().rev() {
                                    meter.push(
                                        &mut pending,
                                        Task::Visit(term, depth.saturating_add(1)),
                                    )?;
                                }
                            }
                            meter
                                .push(&mut pending, Task::Visit(*body, depth.saturating_add(1)))?;
                        }
                        TermData::Not(inner) => meter
                            .push(&mut pending, Task::Visit(*inner, depth.saturating_add(1)))?,
                        TermData::Ite(condition, yes, no) => {
                            for term in [*no, *yes, *condition] {
                                meter.push(
                                    &mut pending,
                                    Task::Visit(term, depth.saturating_add(1)),
                                )?;
                            }
                        }
                        _ => {} // Raw admission has already inspected all leaf kinds.
                    }
                }
            }
        }
    }
    Ok(())
}
