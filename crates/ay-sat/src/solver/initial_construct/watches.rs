// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::watched::ExactWatchPlan;

pub(super) fn initialize(solver: &mut Solver, owner: &CountedAdmission) -> Result<()> {
    let mut plan = ExactWatchPlan::try_new_counted(solver.watches.num_lists(), owner)?;
    let mut position = 0;
    loop {
        owner.admit(4, 0)?;
        let Some((offset, next)) = solver.arena.walk_step(position) else {
            break;
        };
        position = next;
        if solver.arena.len_of(offset) < 2 {
            continue;
        }
        plan.count_watch_counted(solver.arena.literal(offset, 0), owner)?;
        plan.count_watch_counted(solver.arena.literal(offset, 1), owner)?;
    }
    solver.watches.apply_exact_layout_counted(&plan, owner)?;
    drop(plan);
    position = 0;
    loop {
        owner.admit(4, 0)?;
        let Some((offset, next)) = solver.arena.walk_step(position) else {
            break;
        };
        position = next;
        let len = solver.arena.len_of(offset);
        if len < 2 {
            continue;
        }
        let first = solver.arena.literal(offset, 0);
        let second = solver.arena.literal(offset, 1);
        // The presized engine reproduces the normal insertion schedule's
        // binary/long ordering, including possible long-suffix copies.
        let copies = if len == 2 {
            solver
                .watches
                .len_of(first)
                .checked_add(solver.watches.len_of(second))
                .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?
        } else {
            0
        };
        owner.admit(copies.saturating_add(32), 0)?;
        solver.attach_clause_watches_presized(ClauseRef(offset as u32), first, second, len == 2);
    }
    owner.check()
}
