// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn prepare(
    solver: &ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<Plan, QueryError> {
    owned::scan_table::<(TermId, Vec<(TermId, TermId)>)>(solver.eq_adj.allocation_size(), work)?;
    let count = solver.terms.len();
    let mut labels = owned::reserve_vec::<usize>(count, work)?;
    labels.resize(count, 0);
    let result = if solver.equiv_class_cache_version == Some(solver.eq_adj_version) {
        cached(solver, &mut labels, work)
    } else {
        rebuild(solver, &mut labels, work)
    };
    work.charge(count)?;
    drop(labels);
    work.charge(0)?;
    result
}

fn cached(
    solver: &ArraySolver<'_>,
    labels: &mut [usize],
    work: &mut WorkBudget<'_>,
) -> Result<Plan, QueryError> {
    work.charge(solver.equiv_classes.len())?;
    let total = solver.equiv_classes.iter().try_fold(0usize, |sum, class| {
        owned::checked(sum.checked_add(class.len()), work)
    })?;
    if total > labels.len() || solver.equiv_classes.len() > solver.eq_adj.len() {
        return Err(work.refuse_exhaustion());
    }
    let mut plan = Plan {
        members: owned::reserve_vec(total, work)?,
        ends: owned::reserve_vec(solver.equiv_classes.len(), work)?,
    };
    for (index, class) in solver.equiv_classes.iter().enumerate() {
        let Some(&first) = class.first() else {
            return Err(work.refuse_exhaustion());
        };
        let expected = signature(solver, first, work)?;
        for &member in class {
            if signature(solver, member, work)? != expected {
                return Err(work.refuse_exhaustion());
            }
            let slot = labels
                .get_mut(member.0 as usize)
                .ok_or_else(|| work.refuse_exhaustion())?;
            if *slot != 0 {
                return Err(work.refuse_exhaustion());
            }
            *slot = owned::checked(index.checked_add(1), work)?;
            plan.members.push(member);
        }
        plan.ends.push(plan.members.len());
    }
    verify_edges(solver, labels, work)?;
    Ok(plan)
}

fn verify_edges(
    solver: &ArraySolver<'_>,
    labels: &[usize],
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    for (&term, neighbors) in &solver.eq_adj {
        signature(solver, term, work)?;
        let label = labels[term.0 as usize];
        if label == 0 {
            return Err(work.refuse_exhaustion());
        }
        for index in 0..neighbors.len() {
            work.charge(1)?;
            let &(other, _) = neighbors
                .get(index)
                .ok_or_else(|| work.refuse_exhaustion())?;
            signature(solver, other, work)?;
            if labels[other.0 as usize] != label {
                return Err(work.refuse_exhaustion());
            }
        }
    }
    Ok(())
}

fn rebuild(
    solver: &ArraySolver<'_>,
    labels: &mut [usize],
    work: &mut WorkBudget<'_>,
) -> Result<Plan, QueryError> {
    let edges = solver.eq_adj.values().try_fold(0usize, |sum, neighbors| {
        owned::checked(sum.checked_add(neighbors.len()), work)
    })?;
    let queued = owned::checked(edges.checked_add(solver.eq_adj.len()), work)?;
    let mut queue = owned::reserve_vec(queued, work)?;
    let mut plan = Plan {
        members: owned::reserve_vec(labels.len(), work)?,
        ends: owned::reserve_vec(solver.eq_adj.len(), work)?,
    };
    for &start in solver.eq_adj.keys() {
        let expected = signature(solver, start, work)?;
        if labels[start.0 as usize] != 0 {
            continue;
        }
        let label = owned::checked(plan.ends.len().checked_add(1), work)?;
        queue.push(start);
        while let Some(term) = queue.pop() {
            work.charge(1)?;
            if signature(solver, term, work)? != expected {
                return Err(work.refuse_exhaustion());
            }
            let slot = &mut labels[term.0 as usize];
            if *slot != 0 {
                continue;
            }
            *slot = label;
            plan.members.push(term);
            if let Some(neighbors) = scan::lookup(&solver.eq_adj, term, work)? {
                for index in 0..neighbors.len() {
                    work.charge(1)?;
                    let &(other, _) = neighbors
                        .get(index)
                        .ok_or_else(|| work.refuse_exhaustion())?;
                    signature(solver, other, work)?;
                    if labels[other.0 as usize] == 0 {
                        // Every push is one edge visit or component start;
                        // reserve(edges + keys) covers duplicate queue entries.
                        queue.push(other);
                    }
                }
            }
        }
        plan.ends.push(plan.members.len());
    }
    work.charge(queued)?;
    drop(queue);
    work.charge(0)?;
    Ok(plan)
}
