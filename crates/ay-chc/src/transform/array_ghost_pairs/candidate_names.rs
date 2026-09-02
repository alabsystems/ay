// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Collision-free canonical binders for raw ghost interpretations.

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;

use crate::smt::executor_adapter::collect_uninterpreted_function_declarations_for_problem;
use crate::{CancellationToken, ChcProblem, ChcVar, PredicateId};

use super::certify::exact_clause_vars;
use super::GhostPairSpec;

pub(super) fn canonical_raw_variables(
    original: &ChcProblem,
    raw_ghost: &ChcProblem,
    spec: &GhostPairSpec,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Option<FxHashMap<PredicateId, Vec<ChcVar>>> {
    if original.predicates().len() != raw_ghost.predicates().len() {
        return None;
    }

    let mut used = FxHashSet::default();
    for clause in raw_ghost.clauses() {
        if stopped(cancellation, deadline) {
            return None;
        }
        used.extend(exact_clause_vars(clause)?.into_iter().map(|var| var.name));
    }
    let declarations = collect_uninterpreted_function_declarations_for_problem(raw_ghost).ok()?;
    used.extend(declarations.into_iter().map(|declaration| declaration.name));
    for predicate in raw_ghost.predicates() {
        used.insert(predicate.name.clone());
    }
    for (datatype, constructors) in raw_ghost.datatype_defs() {
        used.insert(datatype.clone());
        for (constructor, selectors) in constructors {
            used.insert(constructor.clone());
            used.extend(selectors.iter().map(|(selector, _)| selector.clone()));
        }
    }
    if stopped(cancellation, deadline) {
        return None;
    }

    let mut canonical = FxHashMap::default();
    for original_predicate in original.predicates() {
        let raw_predicate = raw_ghost.get_predicate(original_predicate.id)?;
        let expected = spec.extended_sorts(original_predicate.id, &original_predicate.arg_sorts)?;
        if raw_predicate.arg_sorts != expected {
            return None;
        }
        let mut vars = Vec::with_capacity(expected.len());
        for (position, sort) in expected.into_iter().enumerate() {
            if stopped(cancellation, deadline) {
                return None;
            }
            let base = format!("__ay_gqh_p{}_a{position}", original_predicate.id.index());
            vars.push(ChcVar::new(
                reserve_fresh_name(base, &mut used, cancellation, deadline)?,
                sort,
            ));
        }
        canonical.insert(original_predicate.id, vars);
    }
    Some(canonical)
}

fn reserve_fresh_name(
    base: String,
    used: &mut FxHashSet<String>,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Option<String> {
    if stopped(cancellation, deadline) {
        return None;
    }
    if used.insert(base.clone()) {
        return Some(base);
    }
    let attempts = used.len().checked_add(1)?;
    for suffix in 1..=attempts {
        if stopped(cancellation, deadline) {
            return None;
        }
        let candidate = format!("{base}_{suffix}");
        if used.insert(candidate.clone()) {
            return Some(candidate);
        }
    }
    None
}

fn stopped(cancellation: &CancellationToken, deadline: Instant) -> bool {
    cancellation.is_cancelled()
        || Instant::now() >= deadline
        || ay_core::TermStore::global_memory_exceeded()
}
