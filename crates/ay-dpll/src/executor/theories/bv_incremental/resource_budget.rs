// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conflict-budget arming for the persistent incremental BV SAT solver.

use ay_sat::Solver as SatSolver;

/// Set one absolute budget relative to conflicts accrued across the session.
/// `None` clears a budget left by a preceding `:rlimit`-bearing check-sat.
pub(super) fn arm_persistent_sat_conflict_budget(solver: &mut SatSolver, allowance: Option<u64>) {
    let target = allowance.map(|limit| solver.num_conflicts().saturating_add(limit));
    solver.set_conflict_budget(target);
}
