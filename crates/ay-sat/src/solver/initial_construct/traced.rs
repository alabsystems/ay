// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[cfg(test)]
mod tests;

pub(super) fn copy_assumptions(
    num_vars: usize,
    input: &[Literal],
    owner: &CountedAdmission,
) -> Result<Vec<Literal>> {
    let mut assumptions = crate::counted_storage::try_reserved_exact(owner, input.len())?;
    for &literal in input {
        owner.admit(2, 0)?;
        if literal.variable().index() >= num_vars {
            return Err(invalid(
                owner,
                "initial assumption literal outside original namespace",
            ));
        }
        assumptions.push(literal);
    }
    owner.check()?;
    Ok(assumptions)
}

pub(super) fn arm(solver: &mut Solver, owner: &CountedAdmission) -> Result<()> {
    // Fixed copies and pass-table checks in the shared proof override kernel;
    // InprocessingControls contains only fixed-size TechniqueControl values.
    owner.admit(
        size_of::<inproc_control::InprocessingControls>()
            .saturating_mul(8)
            .saturating_add(128),
        0,
    )?;
    if !solver.arena.is_empty()
        || !solver.cold.original_ledger.is_empty()
        || solver.has_empty_clause
        || solver.cold.clause_trace.is_some()
        || solver.proof_manager.is_some()
        || solver.cold.internal_lrat_enabled
        || solver.consuming_trace_pending()
        || !solver.cold.scope_selectors.is_empty()
        || !solver
            .cold
            .counted_admission
            .as_ref()
            .is_some_and(|a| a.shares_ledger_with(owner))
    {
        return Err(invalid(
            owner,
            "counted trace arming requires fresh original ownership",
        ));
    }
    solver.assert_can_enable_clause_trace();
    let capacity = solver.num_vars.saturating_mul(4).min(100_000);
    let trace = ClauseTrace::with_capacity_counted(capacity, owner)?;
    owner.check()?;
    solver.install_clause_trace(trace);
    // Exact choices of SmtContext::build_check_sat_cnf, not defaults disabled
    // to force a counted success. retain_unsat_certificate is NOT changed.
    solver.set_unsat_certificate_enabled(false);
    solver.set_preprocess_enabled(false);
    // Resolve the ordinary fixed-size writer/flag selection while this fresh
    // trace-only state is owned. This does not disable a selected consumer;
    // it prevents later root emission from lazily initializing that cache.
    owner.admit(32, 0)?;
    if solver.veripb_hints_active() {
        return Err(invalid(
            owner,
            "selected fresh proof hints are not admitted",
        ));
    }
    owner.check()
}
