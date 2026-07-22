// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Non-linear Real Arithmetic (NRA) solving.
//!
//! Uses model-based incremental linearization, delegating to the LRA simplex
//! solver for the linear relaxation. Sign lemmas and tangent plane lemmas
//! refine the linear model until the nonlinear constraints are satisfied.

use ay_nra::NraSolver;

use super::super::Executor;
use crate::executor_types::Result;
use crate::executor_types::SolveResult;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

impl Executor {
    pub(in crate::executor) fn solve_nra(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        solve_incremental_theory_pipeline!(self,
            tag: "NRA",
            create_theory: NraSolver::new(&self.ctx.terms),
            extract_models: |theory| TheoryModels {
                lra: Some(theory.extract_model()),
                // Propagate the exact ALGEBRAIC witnesses from the Sturm/IVT
                // irrational-root certificate (e.g. `x*x = 2` ⇒ x = √2 as a
                // `root-obj`). Model storage keeps them in the executor model,
                // where variable lookup, polynomial evaluation, get-value/
                // get-model printing and FULL model validation handle them
                // exactly. See TheoryModels::nra_algebraic.
                nra_algebraic: theory.algebraic_model().to_vec(),
                ..TheoryModels::default()
            },
            track_theory_stats: true,
            set_unknown_on_error: true
        )
    }
}
