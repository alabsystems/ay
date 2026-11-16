// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn apply(
    solver: &ArraySolver<'_>,
    model: &mut ArrayModel,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    owned::scan_table::<(TermId, (TermId, TermId, TermId))>(
        solver.store_cache.allocation_size(),
        work,
    )?;
    let mut parents: Vec<(TermId, Option<String>)> =
        owned::reserve_vec(solver.store_cache.len(), work)?;
    for (&store, &(base, _, _)) in &solver.store_cache {
        let value =
            scan::lookup(&model.array_values, store, work)?.and_then(|v| v.default.as_deref());
        let Some(value) = value else {
            continue;
        };
        if scan::lookup(&model.array_values, base, work)?.is_none_or(|v| v.default.is_some()) {
            continue;
        }
        let value = owned::text(value, work)?;
        let visits = owned::checked(
            parents
                .len()
                .checked_mul(16)
                .and_then(|n| n.checked_add(16)),
            work,
        )?;
        work.charge(visits)?;
        if let Some((_, agreed)) = parents.iter_mut().find(|(key, _)| *key == base) {
            // Once conflicting, None remains conflicting, even on a later
            // parent carrying the first value again. Exactly legacy and_modify.
            let equal = match agreed {
                Some(prior) => storage::equal(prior, &value, work)?,
                None => false,
            };
            if !equal {
                work.charge(16)?;
                *agreed = None;
            }
            work.charge(16)?;
            drop(value);
        } else {
            parents.push((base, Some(value)));
        }
    }
    let mut changed = false;
    // Distinct bases assign independently after the COMPLETE aggregation.
    // Thus first-seen vector order equals the map iteration's DATA outcome.
    for (base, value) in &parents {
        work.charge(16)?;
        if let Some(value) = value {
            changed |= assign(model, *base, value, work)?;
        }
    }
    work.charge(parents.len() + 1)?;
    drop(parents);
    work.charge(0)?;
    Ok(changed)
}
