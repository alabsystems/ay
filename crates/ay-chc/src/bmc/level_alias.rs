// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conservative shared-ancestry check for level-flat safety admission.
//!
//! Each body premise owns its entire reachable predicate cone. If two owners
//! reach one predicate, separate derivation instances may need different
//! values for the same `(predicate, level)` tuple. Unioning alternative rules
//! and ignoring relative depths can reject harmless sharing; it cannot admit
//! an alias merely because the shared ancestor is hidden behind another rule.
//! This checks aliasing only, not every completeness condition of an encoding.

use crate::{ChcProblem, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::DetHashMap;

pub(super) fn has_shared_ancestry(
    problem: &ChcProblem,
    keep_going: &mut dyn FnMut() -> bool,
) -> Option<bool> {
    if !keep_going() {
        return None;
    }
    // The inner scope drops all indexing/frontier scratch before admission.
    // An interrupted scan returns immediately, without a new post-error poll.
    let overlap = scan(problem, keep_going)?;
    keep_going().then_some(overlap)
}

fn scan(problem: &ChcProblem, keep_going: &mut dyn FnMut() -> bool) -> Option<bool> {
    let mut definitions: DetHashMap<PredicateId, Vec<&HornClause>> = DetHashMap::default();
    let mut branching = Vec::new();
    for clause in problem.clauses() {
        if !keep_going() {
            return None;
        }
        if let ClauseHead::Predicate(predicate, _) = &clause.head {
            definitions.entry(*predicate).or_default().push(clause);
        }
        if clause.body.predicates.len() > 1 {
            branching.push(clause);
        }
    }

    let mut owners = DetHashMap::default();
    let mut pending = Vec::new();
    for clause in branching {
        if !keep_going() {
            return None;
        }
        owners.clear();
        for (owner, (predicate, _)) in clause.body.predicates.iter().enumerate() {
            if !keep_going() {
                return None;
            }
            if !claim(*predicate, owner, &mut owners, &mut pending) {
                return Some(true);
            }
            while let Some(predicate) = pending.pop() {
                if !keep_going() {
                    return None;
                }
                for definition in definitions.get(&predicate).into_iter().flatten() {
                    if !keep_going() {
                        return None;
                    }
                    for (dependency, _) in &definition.body.predicates {
                        if !keep_going() {
                            return None;
                        }
                        if !claim(*dependency, owner, &mut owners, &mut pending) {
                            return Some(true);
                        }
                    }
                }
            }
        }
    }
    Some(false)
}

fn claim(
    predicate: PredicateId,
    owner: usize,
    owners: &mut DetHashMap<PredicateId, usize>,
    pending: &mut Vec<PredicateId>,
) -> bool {
    if let Some(previous) = owners.get(&predicate) {
        return *previous == owner;
    }
    owners.insert(predicate, owner);
    // Enqueue-time dedup bounds the frontier even for a wide repeated edge
    // list, and guarantees termination of same-owner cycles without recursion.
    pending.push(predicate);
    true
}

#[cfg(test)]
mod tests;
