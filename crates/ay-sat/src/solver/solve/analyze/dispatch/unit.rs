// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission for the existing global-unit installer. It keeps original arena
//! identity, retained theory proof IDs and pinned LRAT retry ordering.

use super::*;
use crate::counted_storage::{try_reserve, Result as AdmissionResult};
use crate::decision_trace::counted_decision::invalid;
use ay_core::original_query::CountedAdmission;

pub(super) fn install(
    s: &mut Solver,
    reference: ClauseRef,
    owner: &CountedAdmission,
) -> AdmissionResult<bool> {
    owner.admit(48, 0)?;
    let lit = s.arena.literal(reference.index(), 0);
    let var = lit.variable().index();
    if s.decision_level != 0 || var >= s.num_vars {
        return Err(invalid(
            owner,
            "global-unit installation requires actual root state",
        ));
    }
    if s.lit_val(lit) < 0 {
        return Ok(false);
    }
    let unassigned = !s.var_is_assigned(var);
    if unassigned {
        if s.trail.len() >= s.num_vars {
            return Err(invalid(owner, "global-unit trail is full"));
        }
        try_reserve(owner, &mut s.trail, 1)?;
        #[cfg(debug_assertions)]
        if (s.trail.len() + 1) & 0x3ff == 0 {
            owner.admit(s.num_vars, 0)?;
        }
    } else if s.var_data[var].level != 0 {
        return Err(invalid(owner, "true global unit has a nonroot assignment"));
    }
    let id = retained_id(s, reference, lit, owner)?;
    if id != 0 && var < s.unit_proof_id.len() {
        if var >= s.unit_proof_sign.len() {
            return Err(invalid(
                owner,
                "global-unit proof sign storage is incomplete",
            ));
        }
        prepare_pin(s, var, unassigned, owner)?;
    }
    // The actual installer may enqueue, set the original unit ID, remove one
    // pending-ID slot and insert one retry slot. All are prepaid before any
    // publication, with no callback between those effects.
    owner.check()?;
    let installed = s.install_theory_unit_at_root(reference);
    owner.check()?;
    Ok(installed)
}

fn retained_id(
    s: &Solver,
    reference: ClauseRef,
    lit: Literal,
    owner: &CountedAdmission,
) -> AdmissionResult<u64> {
    for &(pending, id) in &s.pending_theory_unit_proof_ids {
        owner.admit(2, 0)?; // this inspection plus the actual installer's scan
        if pending == reference {
            return Ok(id);
        }
    }
    let var = lit.variable().index();
    let old_id = s.unit_proof_id.get(var).copied().unwrap_or(0);
    let old_sign = s.unit_proof_sign.get(var).copied().unwrap_or(0);
    Ok(if old_id != 0 && old_sign == lit.sign_i8() {
        old_id
    } else {
        s.clause_id(reference)
    })
}

fn prepare_pin(
    s: &mut Solver,
    var: usize,
    unassigned: bool,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    if !s.cold.lrat_enabled {
        return Ok(());
    }
    let slot = if unassigned {
        s.trail.len()
    } else {
        s.var_data[var].trail_pos as usize
    };
    let end = s.trail.len() + usize::from(unassigned);
    if slot >= end || slot >= s.cold.lrat_level0_unit_materialize_cursor {
        return Ok(());
    }
    let pinned = &mut s.cold.lrat_level0_unit_materialize_pinned;
    // Both this search and the unchanged installer's partition_point, including
    // empty-list termination; reserve only when its exact insertion is needed.
    let depth = (usize::BITS - pinned.len().leading_zeros()) as usize + 1;
    owner.admit(depth * 2, 0)?;
    let index = pinned.partition_point(|&entry| entry < slot);
    if pinned.get(index) != Some(&slot) {
        owner.admit(pinned.len() - index + 1, 0)?;
        try_reserve(owner, pinned, 1)?;
    }
    Ok(())
}
