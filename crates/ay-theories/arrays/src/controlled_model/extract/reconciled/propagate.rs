// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn apply(
    plan: &classes::Plan,
    solver: &ArraySolver<'_>,
    state: &mut storage::State,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let mut begin = 0;
    for &end in &plan.ends {
        work.charge(16)?;
        let class = plan
            .members
            .get(begin..end)
            .ok_or_else(|| work.refuse_exhaustion())?;
        let mut best: Option<(TermId, (usize, usize))> = None;
        for &term in class {
            if let Some(value) = scan::lookup(&state.model.array_values, term, work)? {
                work.charge(16)?;
                let rank = (usize::from(value.default.is_some()), value.stores.len());
                if best.is_none_or(|(_, prior)| rank >= prior) {
                    best = Some((term, rank));
                }
            }
        }
        if let Some((best, _)) = best {
            for &member in class {
                if storage::contains(&state.model.array_values, member, work)?
                    || scan::lookup(&solver.array_vars, member, work)?.is_none()
                {
                    continue;
                }
                let source = scan::lookup(&state.model.array_values, best, work)?
                    .ok_or_else(|| work.refuse_exhaustion())?;
                let value = owned::interpretation(source, work)?;
                storage::insert(state, member, value, work)?;
            }
        }
        begin = end;
    }
    if begin != plan.members.len() {
        return Err(work.refuse_exhaustion());
    }
    work.charge(0)
}
