// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Same-owner admission before the actual clause-use/streaming operations.

use super::*;

pub(super) fn prepare_bump(
    s: &mut Solver,
    reference: ClauseRef,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    owner.admit(1, 0)?;
    let offset = reference.0 as usize;
    if !s.arena.is_active(offset) {
        return Err(invalid(
            owner,
            "counted ordinary analysis cannot bump an inactive clause",
        ));
    }
    validate_streaming(s, reference, owner)?;
    if s.arena.is_learned(offset) {
        for &lit in s.arena.literals(offset) {
            owner.admit(1, 0)?;
            let Some(data) = s.var_data.get(lit.variable().index()) else {
                return Err(invalid(owner, "counted glue literal is outside VarData"));
            };
            if lit.0 as usize >= s.vals.len()
                || !s.var_is_assigned(lit.variable().index())
                || data.level as usize > s.num_vars
            {
                return Err(invalid(owner, "counted glue has no bounded assigned level"));
            }
        }
    }
    // Exact selected glue early-exits, wrap, individual growth, two-stage
    // scoring and the promoted histogram bucket share the ordinary kernel.
    s.bump_clause_admitted(reference, &finalize::Counted(owner))
}

fn validate_streaming(
    s: &Solver,
    reference: ClauseRef,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    owner.admit(3, 0)?;
    let id = s.clause_id(reference);
    if id > 0 && id <= s.cold.streaming_core_num_originals && s.is_original_clause_id(id) {
        if s.cold
            .streaming_core
            .as_ref()
            .is_some_and(|bits| id as usize > bits.len())
        {
            return Err(invalid(
                owner,
                "counted original streaming marker is outside its bitmap",
            ));
        }
    }
    Ok(())
}
