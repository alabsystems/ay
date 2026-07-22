// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver-start wiring for the SAT whole-loop external code generation guard artifact.
//!
//! The artifact is telemetry-only: it validates the static formula profile at
//! runtime and never contributes SAT/UNSAT decisions, propagation, proof
//! production, or watch-list mutation.

use super::*;

impl Solver {
    #[inline]
    pub(super) fn install_and_apply_sat_whole_loop_guard_at_solver_start(&mut self) {}
}
