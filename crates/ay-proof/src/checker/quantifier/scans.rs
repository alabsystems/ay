// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Metered source/argument DAG walks. Duplicate edges are charged before push.

use super::progress::QuantifierMeter;
use super::*;

pub(super) fn push_children(
    data: &TermData,
    stack: &mut Vec<TermId>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    match data {
        TermData::App(_, args) => {
            for &arg in args {
                meter.push(stack, arg)?;
            }
        }
        TermData::Not(inner) => meter.push(stack, *inner)?,
        TermData::Ite(c, t, e) => {
            for id in [*c, *t, *e] {
                meter.push(stack, id)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                meter.push(stack, *value)?;
            }
            meter.push(stack, *body)?;
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            meter.push(stack, *body)?;
            for group in triggers {
                meter.charge(1, 0)?;
                for &trigger in group {
                    meter.push(stack, trigger)?;
                }
            }
        }
        TermData::Var(..) | TermData::Const(..) => {}
        _ => return Err(ProofCheckError::ResourceLimit),
    }
    Ok(())
}

pub(super) fn term_contains(
    terms: &TermStore,
    root: TermId,
    needle: TermId,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    let mut visited = HashSet::default();
    let mut stack = Vec::new();
    meter.push(&mut stack, root)?;
    while let Some(term) = stack.pop() {
        let data = meter.term(terms, term)?;
        if term == needle {
            return Ok(true);
        }
        if meter.seen(&mut visited, term)? {
            continue;
        }
        meter.visit()?;
        push_children(data, &mut stack, meter)?;
    }
    Ok(false)
}

pub(super) fn nested_binder_names(
    terms: &TermStore,
    root: TermId,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<Option<HashSet<String>>, ProofCheckError> {
    let mut names = HashSet::default();
    let mut seen = HashSet::default();
    let mut stack = Vec::new();
    meter.push(&mut stack, root)?;
    while let Some(term) = stack.pop() {
        let data = meter.term(terms, term)?;
        if meter.seen(&mut seen, term)? {
            continue;
        }
        meter.visit()?;
        match data {
            TermData::Forall(bindings, _, _) | TermData::Exists(bindings, _, _) => {
                for (name, _) in bindings {
                    meter.insert_name(&mut names, name)?;
                }
            }
            TermData::Let(..) => return Ok(None),
            TermData::App(..)
            | TermData::Not(..)
            | TermData::Ite(..)
            | TermData::Var(..)
            | TermData::Const(..) => {}
            _ => return Ok(None),
        }
        push_children(data, &mut stack, meter)?;
    }
    Ok(Some(names))
}

pub(super) fn argument_is_ground_for(
    terms: &TermStore,
    root: TermId,
    capturing_binders: &HashSet<&str>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    let mut visited = HashSet::default();
    let mut stack = Vec::new();
    meter.push(&mut stack, root)?;
    while let Some(term) = stack.pop() {
        let data = meter.term(terms, term)?;
        if meter.seen(&mut visited, term)? {
            continue;
        }
        meter.visit()?;
        match data {
            TermData::Var(name, _) => {
                meter.lookup(name, capturing_binders.len())?;
                if capturing_binders.contains(name.as_str()) {
                    return Ok(false);
                }
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return Ok(false),
            TermData::App(..) | TermData::Not(..) | TermData::Ite(..) | TermData::Const(..) => {}
            _ => return Ok(false),
        }
        push_children(data, &mut stack, meter)?;
    }
    Ok(true)
}

pub(super) fn argument_has_free_name_in(
    terms: &TermStore,
    root: TermId,
    forbidden: &HashSet<String>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    let mut seen = HashSet::default();
    let mut stack = Vec::new();
    meter.push(&mut stack, root)?;
    while let Some(term) = stack.pop() {
        let data = meter.term(terms, term)?;
        if meter.seen(&mut seen, term)? {
            continue;
        }
        meter.visit()?;
        match data {
            TermData::Var(name, _) => {
                meter.lookup(name, forbidden.len())?;
                if forbidden.contains(name) {
                    return Ok(true);
                }
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return Ok(true),
            _ => {}
        }
        push_children(data, &mut stack, meter)?;
    }
    Ok(false)
}
