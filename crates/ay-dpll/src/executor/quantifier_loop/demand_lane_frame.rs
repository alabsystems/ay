// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The demand lane lives for one quantifier solve.
//!
//! The lane (frontier, gated families, parked instances) is state on the
//! quantifier manager. Outside incremental mode that manager outlives the
//! check-sat, and only E-matching resets the lane, so a solve that runs no
//! E-matching would read the lane an earlier solve left behind. A parked
//! instance is a fact only for the problem whose E-matching parked it: under
//! another query's assumptions the universal it instantiates may not hold, and
//! flushing it there refutes a satisfiable query.

use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

use crate::executor::Executor;
use crate::quantifier_manager::QuantifierManager;

impl Executor {
    /// Run one quantifier-support solve with a demand lane of its own.
    ///
    /// The lane is set aside on entry, so the solve starts inert and only its
    /// own E-matching can arm it, and put back on every exit, a panic
    /// included. A nested solve therefore leaves the enclosing solve's lane as
    /// it found it, and after the outermost solve the lane is inert again: no
    /// later check-sat, plain or with assumptions, can flush or be blocked by
    /// an instance this one parked.
    pub(in crate::executor) fn with_demand_lane_frame<T>(
        &mut self,
        solve: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let outer = self
            .quantifier_manager
            .as_mut()
            .map(QuantifierManager::demand_take);
        let result = catch_unwind(AssertUnwindSafe(|| solve(self)));
        if let Some(manager) = self.quantifier_manager.as_mut() {
            manager.demand_restore(outer.unwrap_or_default());
        }
        result.unwrap_or_else(|payload| resume_unwind(payload))
    }
}

#[cfg(test)]
#[path = "demand_lane_frame_tests.rs"]
mod tests;
