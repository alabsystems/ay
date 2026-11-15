// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Debug model invariants without unadmitted panic formatting or diagnostics.
#![cfg(debug_assertions)]

use super::*;
use crate::reconstruct::{replay::clause_satisfied_admitted, ReconstructionStep};

pub(super) fn before(s: &Solver, model: &[bool], owner: &CountedAdmission) -> AdmissionResult<()> {
    let policy = Counted(owner);
    // The complete-assignment declaration checks all non-garbage clauses,
    // including empty/pending clauses, before ordinary model finalization.
    policy.work(s.arena.len())?; // bounded header skips inside ArenaIter::next
    for index in s.arena.indices() {
        policy.work(1)?;
        if !s.arena.is_garbage(index)
            && !clause_satisfied_admitted(s.arena.literals(index), model, &policy)?
        {
            return Err(model_invalid(owner));
        }
    }
    for step in s.inproc.reconstruction.steps_ref() {
        policy.work(1)?;
        match step {
            ReconstructionStep::Witness(witness) => {
                if witness.witness.is_empty() || witness.clause.is_empty() {
                    return Err(model_invalid(owner));
                }
                for lit in witness.witness.iter().chain(witness.clause.iter()) {
                    validate_lit(s, *lit, owner)?;
                }
                let mut overlap = false;
                for w in &witness.witness {
                    policy.work(1)?;
                    for c in &witness.clause {
                        policy.work(1)?;
                        if c.variable() == w.variable() {
                            overlap = true;
                            break;
                        }
                    }
                    if overlap {
                        break;
                    }
                }
                if !overlap {
                    return Err(model_invalid(owner));
                }
            }
            ReconstructionStep::Sweep { num_vars, lit_map } => {
                if *num_vars > s.cold.e2i.len()
                    || num_vars.checked_mul(2).is_none_or(|n| n > lit_map.len())
                {
                    return Err(model_invalid(owner));
                }
                for lit in lit_map {
                    validate_lit(s, *lit, owner)?;
                }
                for var in 0..*num_vars {
                    policy.work(1)?;
                    let mapped = lit_map[2 * var].variable().index();
                    if mapped != var
                        && 2 * mapped < lit_map.len()
                        && lit_map[2 * mapped].variable().index() != mapped
                    {
                        return Err(model_invalid(owner));
                    }
                }
            }
        }
    }
    Ok(())
}

fn validate_lit(s: &Solver, lit: Literal, owner: &CountedAdmission) -> AdmissionResult<()> {
    owner.admit(1, 0)?;
    let ext = lit.variable().index();
    let Some(&internal) = s.cold.e2i.get(ext) else {
        return Err(model_invalid(owner));
    };
    if internal != compact::UNMAPPED
        && s.cold.i2e.get(internal as usize).copied() != Some(ext as u32)
    {
        return Err(model_invalid(owner));
    }
    Ok(())
}

pub(super) fn after(
    s: &Solver,
    external: &[bool],
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    let policy = Counted(owner);
    for step in s.inproc.reconstruction.steps_ref() {
        policy.work(1)?;
        if let ReconstructionStep::Sweep { num_vars, lit_map } = step {
            for var in 0..*num_vars {
                policy.work(1)?;
                if 2 * var >= lit_map.len() || var >= external.len() {
                    continue;
                }
                let mapped = lit_map[2 * var];
                let representative = mapped.variable().index();
                if representative != var && representative < external.len() {
                    let value = external[representative] == mapped.is_positive();
                    if external[var] != value {
                        return Err(model_invalid(owner));
                    }
                }
            }
        }
    }
    for clause in &s.cold.root_satisfied_saved {
        policy.work(1)?;
        if !clause_satisfied_admitted(clause, external, &policy)? {
            return Err(model_invalid(owner));
        }
    }
    Ok(())
}
