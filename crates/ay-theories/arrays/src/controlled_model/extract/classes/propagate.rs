// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn apply(
    plan: &Plan,
    solver: &ArraySolver<'_>,
    output: &mut ArrayModel,
    buckets: usize,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let mut begin = 0;
    for &end in &plan.ends {
        work.charge(1)?;
        let class = plan
            .members
            .get(begin..end)
            .ok_or_else(|| work.refuse_exhaustion())?;
        if let Some(best) = choose(class, output, work)? {
            for &member in class {
                owned::table_insert(buckets, work)?;
                if output.array_values.contains_key(&member)
                    || scan::lookup(&solver.array_vars, member, work)?.is_none()
                {
                    continue;
                }
                let source = scan::lookup(&output.array_values, best, work)?
                    .ok_or_else(|| work.refuse_exhaustion())?;
                let copy = owned::interpretation(source, work)?;
                owned::table_insert(buckets, work)?;
                output.array_values.insert(member, copy);
            }
        }
        begin = end;
    }
    if begin != plan.members.len() {
        return Err(work.refuse_exhaustion());
    }
    // No store chains and no class mixes present/absent defaults. Legacy
    // reconciliation and both default fixpoints cannot change this DATA.
    // Existing read_conflicted flags are deliberately NOT propagated.
    work.charge(0)
}

fn choose(
    class: &[TermId],
    output: &ArrayModel,
    work: &mut WorkBudget<'_>,
) -> Result<Option<TermId>, QueryError> {
    let mut best: Option<(TermId, (usize, usize))> = None;
    let mut some = false;
    let mut none = false;
    for &member in class {
        let Some(value) = scan::lookup(&output.array_values, member, work)? else {
            continue;
        };
        work.charge(1)?;
        some |= value.default.is_some();
        none |= value.default.is_none();
        let rank = (usize::from(value.default.is_some()), value.stores.len());
        // max_by_key retains the LAST equal-rank member, not the first.
        if best.is_none_or(|(_, previous)| rank >= previous) {
            best = Some((member, rank));
        }
    }
    if some && none {
        return Err(work.refuse_exhaustion());
    }
    Ok(best.map(|(member, _)| member))
}
