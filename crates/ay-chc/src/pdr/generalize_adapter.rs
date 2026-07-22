// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adapter connecting PDR solver to the generalization framework.
//!
//! This module provides `PdrGeneralizerAdapter` which implements
//! `TransitionSystemRef` for use with the generalization pipeline.
//!
//! # Design
//!
//! See the development design notes for full design.
//!
//! # References
//!
//! - Z3 Spacer: `reference/z3/src/muz/spacer/spacer_generalizers.cpp`
//! - Issue #775

use crate::expr::ChcExpr;
use crate::generalize::{InitBounds, TransitionSystemRef};
use crate::PredicateId;

use super::solver::PdrSolver;
use ay_core::kani_compat::DetHashMap as HashMap;

/// Adapter connecting PDR solver to the generalization framework.
///
/// This adapter allows using `UnsatCoreGeneralizer`, `DropLiteralGeneralizer`,
/// and other generalizers with PDR's internal representation.
///
/// # Lifetime
///
/// The adapter borrows the solver mutably because inductiveness checks
/// require mutable access to the SMT context.
pub(super) struct PdrGeneralizerAdapter<'a> {
    /// Reference to the PDR solver
    solver: &'a mut PdrSolver,
    /// The predicate for which we're generalizing
    predicate: PredicateId,
}

impl<'a> PdrGeneralizerAdapter<'a> {
    /// Create a new adapter for the given predicate.
    ///
    /// The frame level is passed to each method call by the generalizer
    /// framework, so it's not stored in the adapter.
    pub(super) fn new(solver: &'a mut PdrSolver, predicate: PredicateId) -> Self {
        Self { solver, predicate }
    }
}

impl TransitionSystemRef for PdrGeneralizerAdapter<'_> {
    fn check_inductive(&mut self, formula: &ChcExpr, level: u32) -> bool {
        self.solver
            .is_inductive_blocking(formula, self.predicate, level as usize)
    }

    fn check_inductive_with_core(
        &mut self,
        conjuncts: &[ChcExpr],
        level: u32,
    ) -> Option<Vec<ChcExpr>> {
        self.solver.try_shrink_blocking_conjuncts_with_iuc(
            conjuncts,
            self.predicate,
            level as usize,
        )
    }

    fn init_bounds(&self) -> HashMap<String, InitBounds> {
        // Get initial value bounds for this predicate's variables.
        // PDR stores these in get_init_values() as InitIntBounds.
        // We convert to generalize::InitBounds.
        let init_values = self.solver.get_init_values(self.predicate);
        let mut bounds = HashMap::default();

        for (var_name, pdr_bounds) in init_values {
            // i128-lockstep: generalize::InitBounds is i64-based; skip vars
            // whose init bounds don't fit i64 (absent entry = no init info,
            // which only weakens generalization). This also skips the
            // unbounded i128::MIN/MAX sentinel, which carries no information.
            if let (Ok(min), Ok(max)) =
                (i64::try_from(pdr_bounds.min), i64::try_from(pdr_bounds.max))
            {
                bounds.insert(var_name, InitBounds::range(min, max));
            }
        }

        bounds
    }
}
