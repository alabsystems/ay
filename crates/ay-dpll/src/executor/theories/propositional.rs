// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Propositional (pure SAT) solving.

use crate::executor_types::Result;
use crate::executor_types::SolveResult;
use crate::PropositionalTheory;

use super::super::Executor;

impl Executor {
    /// Solve using propositional theory (pure SAT).
    ///
    /// PropositionalTheory is a no-op theory (check always returns Sat), so
    /// this is effectively a pure SAT solve. Proof tracking is handled
    /// natively by `solve_incremental_theory_pipeline!` (#6705).
    pub(in crate::executor) fn solve_propositional(&mut self) -> Result<SolveResult> {
        solve_incremental_theory_pipeline!(self,
            tag: "SAT",
            create_theory: PropositionalTheory,
            extract_models: |_theory| TheoryModels::default(),
            track_theory_stats: false,
            set_unknown_on_error: false
        )
    }
}

#[cfg(test)]
#[path = "propositional_tests.rs"]
mod tests;
