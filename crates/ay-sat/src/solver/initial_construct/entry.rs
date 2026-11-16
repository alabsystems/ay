// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::original_clause_ids::counted::{self, InstalledOriginals};
use super::*;

struct Prepared {
    installed: InstalledOriginals,
    assumptions: Vec<Literal>,
    conflict: InitialConflict,
}

pub(super) fn construct(
    input: CountedInitialCnf,
    assumptions: Option<&[Literal]>,
) -> Result<CountedInitialSolver> {
    let owner = input.owner().clone();
    // Neither callback-bearing input nor the partly built solver is owned by
    // the operation closure or with_work's entry/payload-drop catch boundary.
    let mut input = Some(input);
    let mut scratch = Scratch(None);
    let mut output = None;
    let build = cleanup::caught(&owner, || {
        owner.with_work(|_| {
            Ok(match input.as_ref() {
                Some(input) => prepare(input, assumptions, &owner, &mut scratch),
                None => Err(invalid(&owner, "missing original input")),
            })
        })?
    });
    let built = match build {
        Ok(parts) => match (scratch.0.take(), input.take()) {
            (Some(solver), Some(input)) => {
                output = Some(CountedInitialSolver {
                    solver,
                    input,
                    initial_conflict: parts.conflict,
                    source_ids: parts.installed.ids,
                    assumptions: parts.assumptions,
                });
                Ok(())
            }
            _ => Err(invalid(&owner, "missing admitted SAT state")),
        },
        Err(error) => Err(error),
    };
    let retired = cleanup::caught(&owner, || {
        drop(scratch);
        Ok(())
    });
    let input_retired = cleanup::caught(&owner, || {
        drop(input.take());
        Ok(())
    });
    let checked = cleanup::caught(&owner, || owner.check());
    let result = match checked.and(built).and(retired).and(input_retired) {
        Ok(()) => output
            .take()
            .ok_or_else(|| invalid(&owner, "missing completed SAT bootstrap")),
        Err(error) => {
            let _ = cleanup::caught(&owner, || {
                drop(output.take());
                Ok(())
            });
            Err(owner.refuse(error))
        }
    };
    cleanup::release(owner, result)
}

fn prepare(
    input: &CountedInitialCnf,
    premises: Option<&[Literal]>,
    owner: &CountedAdmission,
    scratch: &mut Scratch,
) -> Result<Prepared> {
    owner.admit(size_of::<CountedInitialSolver>(), 0)?;
    preflight(input, owner)?;
    let assumptions = traced::copy_assumptions(input.num_vars(), premises.unwrap_or(&[]), owner)?;
    scratch.0 = Some(Solver::build_with_hint(
        input.num_vars(),
        None,
        Some(input.len()),
        &construction::Counted(owner),
    )?);
    let solver = scratch
        .0
        .as_mut()
        .ok_or_else(|| invalid(owner, "missing admitted SAT construction"))?;
    owner.admit(1, 0)?;
    solver.cold.counted_admission = Some(owner.clone());
    if premises.is_some() {
        traced::arm(solver, owner)?;
    }
    let installed = counted::install(solver, input, owner)?;
    watches::initialize(solver, owner)?;
    let conflict = ingestion::propagate(solver, installed.empty, owner)?;
    Ok(Prepared {
        installed,
        assumptions,
        conflict,
    })
}
