// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validate recorded entry shapes without granting their sources proof authority.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use crate::executor::proof_propagated_rewrite::PLAN_NODE_BUDGET;
use crate::preprocess::{PropagateValues, PropagatedEntrySource};

// Equality replay is recursive even though this admission walk is iterative.
const MAX_SCALAR_REPLACEMENT_DEPTH: usize = 128;

pub(super) fn checked_pair(
    terms: &TermStore,
    entry: &PropagatedEntrySource,
) -> Option<(TermId, TermId)> {
    // Validate IDs before any get/sort, including the unchanged legacy route.
    terms.entry_stamp(entry.expr)?;
    terms.entry_stamp(entry.value)?;
    terms.entry_stamp(entry.source_assertion)?;
    if matches!(terms.get(entry.expr), TermData::Var(_, _)) {
        return variable_pair(terms, entry);
    }
    // Preserve the original PropagateValues harvest classifier verbatim.
    let pair = PropagateValues::extract_value_equality(terms, entry.source_assertion)?;
    (pair == (entry.expr, entry.value)).then_some(pair)
}

fn variable_pair(terms: &TermStore, entry: &PropagatedEntrySource) -> Option<(TermId, TermId)> {
    // RecordedVariableSubstitution also writes this ledger. An exact defining
    // equality licenses substitution for any admitted carrier, not just scalars.
    // This is not datatype-constructor or selector authority: parsed datatypes
    // use core Uninterpreted identities, and any theory step still needs the
    // independently checked declaration context at replay.
    if !same_variable_sort(terms.sort(entry.expr), terms.sort(entry.value))
        || !matches!(terms.sort(entry.source_assertion), Sort::Bool)
    {
        return None;
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(entry.source_assertion) else {
        return None;
    };
    if name != "="
        || !(args.as_slice() == [entry.expr, entry.value]
            || args.as_slice() == [entry.value, entry.expr])
        || !bounded_replacement(terms, entry.expr, entry.value)
    {
        return None;
    }
    // This authenticates only the exact license's shape. The existing planner
    // must still DERIVE source_assertion from the current authored roots, and
    // the strict checker independently validates every emitted equality step.
    Some((entry.expr, entry.value))
}

fn same_variable_sort(left: &Sort, right: &Sort) -> bool {
    let mut remaining = PLAN_NODE_BUDGET;
    let mut pending = vec![(left, right, 0)];
    while let Some((left, right, depth)) = pending.pop() {
        if remaining == 0 || depth > MAX_SCALAR_REPLACEMENT_DEPTH {
            return false;
        }
        remaining -= 1;
        match (left, right) {
            (Sort::Bool, Sort::Bool) | (Sort::Int, Sort::Int) | (Sort::Real, Sort::Real) => {}
            (Sort::BitVec(left), Sort::BitVec(right))
                if left.width != 0 && left.width == right.width => {}
            (Sort::Uninterpreted(left), Sort::Uninterpreted(right)) => {
                let Some(cost) = left.len().checked_add(right.len()) else {
                    return false;
                };
                let Some(next) = remaining.checked_sub(cost) else {
                    return false;
                };
                remaining = next;
                if left != right {
                    return false;
                }
            }
            (Sort::Array(left), Sort::Array(right)) => {
                if remaining.saturating_sub(pending.len()) < 2 {
                    return false;
                }
                pending.push((&left.element_sort, &right.element_sort, depth + 1));
                pending.push((&left.index_sort, &right.index_sort, depth + 1));
            }
            // Do not recurse through rich datatype metadata or introduce other
            // carrier support merely because two derived Sort values compare equal.
            _ => return false,
        }
    }
    true
}

fn bounded_replacement(terms: &TermStore, variable: TermId, value: TermId) -> bool {
    let mut remaining = PLAN_NODE_BUDGET;
    let mut pending = vec![(value, 0)];
    let mut seen = HashSet::default();
    while let Some((term, depth)) = pending.pop() {
        if remaining == 0
            || depth > MAX_SCALAR_REPLACEMENT_DEPTH
            || term == variable
            || terms.entry_stamp(term).is_none()
        {
            return false;
        }
        remaining -= 1;
        // Revisiting a shared node at a greater depth must still examine its
        // descendants, or a shallow first visit could hide an over-deep path.
        if !seen.insert((term, depth)) {
            continue;
        }
        let children: &[TermId] = match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => &[],
            TermData::App(_, args) => args,
            TermData::Not(child) => std::slice::from_ref(child),
            TermData::Ite(c, t, e) => {
                if remaining.saturating_sub(pending.len()) < 3 {
                    return false;
                }
                pending.extend([(*e, depth + 1), (*t, depth + 1), (*c, depth + 1)]);
                continue;
            }
            // The recording producer refuses binding-aware replacements too.
            _ => return false,
        };
        if children.len() > remaining.saturating_sub(pending.len()) {
            return false;
        }
        pending.extend(children.iter().map(|&child| (child, depth + 1)));
    }
    true
}

#[cfg(test)]
mod tests;
