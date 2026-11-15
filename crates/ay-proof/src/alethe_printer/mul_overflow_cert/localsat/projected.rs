// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Projected AllSAT by DPLL splitting, without a growing blocking database.
//!
//! Split only an unassigned projected atom in the outer tree. Once every
//! projected atom is fixed, the ordinary local search asks whether there is
//! one existential extension; its private branches never escape that leaf.
//! Thus every projected valuation is visited at most once and no completed
//! sibling prefix is searched again after a model. This is enumeration advice,
//! never a derivation: Chain still proves every selected invariant with CDCL.
//!
//! The original clause/index pair is immutable for this whole traversal.
//! Only actual completed propagation states can seed monotone children. The
//! caller's assignment, database, remaining allowance and owner are borrowed;
//! neither a model nor a fixed point survives this call.

use super::*;
use ay_core::kani_compat::DetHashSet as HashSet;

#[cfg(test)]
mod tests;

/// Exact projections of all models of the unchanged database extending fixed.
/// Empty projections still need a satisfying extension; duplicate projected
/// atoms retain their positions and necessarily have the same value.
pub(in crate::alethe_printer::mul_overflow_cert) fn project(
    db: &[Clause],
    fixed: &HashMap<T, bool>,
    projection: &[T],
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<HashSet<Vec<bool>>> {
    progress.poll().then_some(())?;
    let found = {
        let index = Occurrences::new(db, budget, progress)?;
        let mut stack = Vec::new();
        reserve(&mut stack, 1, budget, progress)?;
        stack.push(Pending::Fresh(copy_assignment(fixed, budget, progress)?));
        let mut found = HashSet::default();
        while let Some(pending) = stack.pop() {
            charge(budget, 1, progress)?;
            let Some(parent) = propagate(db, &index, pending, budget, progress)? else {
                continue;
            };
            if let Some(atom) = next_projection(&parent, projection, budget, progress)? {
                let other = FixedPoint {
                    assignment: copy_assignment(&parent.assignment, budget, progress)?,
                    index: parent.index,
                };
                reserve(&mut stack, 2, budget, progress)?;
                stack.push(Pending::Child {
                    parent: other,
                    decision: (atom, false),
                });
                stack.push(Pending::Child {
                    parent,
                    decision: (atom, true),
                });
            } else if let Some(model) =
                solve_pending(db, &index, Pending::Ready(parent), budget, progress)?
            {
                record(&mut found, &model, projection, budget, progress)?;
            }
        }
        // Search state and its index are destroyed before the last owner fence.
        found
    };
    progress.poll().then_some(())?;
    Some(found)
}

fn next_projection(
    parent: &FixedPoint<'_>,
    projection: &[T],
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<Option<T>> {
    for &atom in projection {
        charge(budget, 1, progress)?;
        if !parent.assignment.contains_key(&atom) {
            return Some(Some(atom));
        }
    }
    progress.poll().then_some(())?;
    Some(None)
}

/// Admit logical slots, table traversal, copies and eventual scratch retirement
/// before the new map is used. Like the existing propagation allowance, these
/// are logical units, not allocator-internal or hash-probe instruction counts.
fn copy_assignment(
    source: &HashMap<T, bool>,
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<HashMap<T, bool>> {
    charge(budget, source.capacity(), progress)?;
    charge(budget, source.len(), progress)?;
    let mut copy = HashMap::default();
    if copy.try_reserve(source.len()).is_err() {
        return exhausted(budget);
    }
    for (&atom, &value) in source {
        charge(budget, 2, progress)?;
        copy.insert(atom, value);
    }
    progress.poll().then_some(())?;
    Some(copy)
}

fn record(
    found: &mut HashSet<Vec<bool>>,
    model: &HashMap<T, bool>,
    projection: &[T],
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<()> {
    let mut state = Vec::new();
    reserve(&mut state, projection.len(), budget, progress)?;
    for atom in projection {
        charge(budget, 2, progress)?;
        // Every projected atom was assigned before the existential search.
        // Missing data is a refusal, never an invented default assignment.
        state.push(*model.get(atom)?);
    }
    charge(budget, 1, progress)?;
    if found.len() == found.capacity() {
        charge(budget, found.capacity(), progress)?;
        let Some(rehash) = found.len().checked_mul(projection.len()) else {
            return exhausted(budget);
        };
        charge(budget, rehash, progress)?;
        if found.try_reserve(1).is_err() {
            return exhausted(budget);
        }
    }
    charge(budget, projection.len(), progress)?;
    found.insert(state);
    progress.poll().then_some(())
}
