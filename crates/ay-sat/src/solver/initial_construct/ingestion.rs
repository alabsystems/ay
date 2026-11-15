// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::watched::counted::reserve_vec;

pub(super) fn propagate(
    solver: &mut Solver,
    empty: Option<(usize, u64)>,
    owner: &CountedAdmission,
) -> Result<InitialConflict> {
    if let Some((source_row, clause_id)) = empty {
        owner.check()?;
        return Ok(InitialConflict::OriginalEmpty {
            source_row,
            clause_id,
        });
    }
    let mut position = 0;
    loop {
        owner.admit(1, 0)?;
        let Some((offset, next)) = solver.arena.walk_step(position) else {
            break;
        };
        position = next;
        owner.admit(2, 0)?;
        if solver.arena.len_of(offset) != 1 {
            continue;
        }
        let literal = solver.arena.literal(offset, 0);
        match solver.lit_val(literal) {
            -1 => {
                owner.check()?;
                return Ok(InitialConflict::Clause(ClauseRef(offset as u32)));
            }
            0 => enqueue_unit(solver, literal, offset, owner)?,
            _ => {}
        }
    }
    match solver.search_propagate_counted() {
        Ok(found) => {
            owner.check()?;
            Ok(found.map_or(InitialConflict::None, InitialConflict::Clause))
        }
        Err(_) => {
            owner.check()?;
            Err(invalid(
                owner,
                "counted BCP stopped without original refusal",
            ))
        }
    }
}

fn enqueue_unit(
    solver: &mut Solver,
    literal: Literal,
    offset: usize,
    owner: &CountedAdmission,
) -> Result<()> {
    let needed = solver.trail.len() + 1;
    reserve_vec(&mut solver.trail, needed, owner)?;
    // enqueue's periodic debug consistency scan is real work too.
    let debug_scan = if cfg!(debug_assertions) && needed & 0x3ff == 0 {
        solver.num_vars
    } else {
        0
    };
    owner.admit(debug_scan.saturating_add(128), 0)?;
    let id = solver.cold.clause_ids[offset];
    solver.record_unit_proof_id_for_lit(literal, id);
    // Original units have no antecedents and must never become ordinary
    // conflict-analysis reason clauses (the existing #6257 invariant).
    solver.enqueue(literal, None);
    let variable = literal.variable().index();
    if !solver.var_lifecycle.is_inactive(variable) {
        solver.fixed_count += 1;
        solver.var_lifecycle.mark_fixed(variable);
        solver.l0_gc_dirty[variable] = true;
    }
    owner.check()
}
