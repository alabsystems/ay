// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Isolated rewritten Real solves and their complete model merge.

use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermId, TseitinResult};
use ay_fp::FpModel;
use ay_lra::LraModel;

use crate::executor::model::Model;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};
use crate::features::StaticFeatures;

use super::super::stop::FpStop;
use super::super::to_real::{
    build_lra_model_from_fp_to_real, pin_undefined_fp_to_real, MixedSubproblemResult,
};
use super::FpRealPhase;

#[cfg(test)]
#[path = "mixed/tests.rs"]
mod tests;

fn without_models(result: SolveResult) -> MixedSubproblemResult {
    MixedSubproblemResult {
        result,
        lra_model: None,
        euf_model: None,
        materialized_scalar_functions: HashMap::default(),
    }
}

impl Executor {
    /// Solve temporary FP-free roots without committing their incremental state.
    /// A child resource refusal belongs to the enclosing FP attempt, even when
    /// the child was rejected before its isolated proof window could open.
    pub(super) fn solve_rewritten_mixed_subproblem(
        &mut self,
        rewritten_assertions: &[TermId],
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> Result<MixedSubproblemResult> {
        if let Err(origin) = self.fp_real_checkpoint(stop, observe, FpRealPhase::MixedCheckpoint) {
            return Ok(without_models(self.fp_stopped(origin)));
        }
        // Allocate before taking outer state. The unwind boundary below covers
        // feature collection, logic borrowing, child work and child observers.
        let replacement = rewritten_assertions.to_vec();
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, replacement);
        let saved_model = self.last_model.take();
        let saved_result = self.last_result.take();
        let saved_unknown = self.last_unknown_reason.take();
        let saved_origin = self.last_unknown_origin.take();
        let saved_validated = self.last_model_validated;
        let mut logic_borrow = None;
        let attempt = catch_unwind(AssertUnwindSafe(|| {
            let features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
            let inferred_logic = features.infer_logic().to_string();
            // Keep the existing borrowed-logic protocol: a real source change
            // inside the child must not be hidden by a fabricated fresh stamp.
            logic_borrow = Some(self.ctx.begin_internal_logic_borrow(inferred_logic));
            let result = self.with_isolated_incremental_state(None, |this| {
                if let Err(origin) = this.fp_real_checkpoint(stop, observe, FpRealPhase::MixedChild)
                {
                    stop.refuse(origin);
                    return Ok(SolveResult::Unknown);
                }
                this.check_sat_internal()
            });
            // Read the child's reason before reinstating the outer one. This
            // includes checkpoint admission, which returns Unknown without
            // running the closure or setting a public last_result.
            if !matches!(&result, Ok(SolveResult::Sat)) && self.fp_recorded_resource_stop() {
                if let Some(reason) = self.last_unknown_reason {
                    stop.refuse(reason.origin());
                }
            }
            let (lra_model, euf_model, materialized_scalar_functions) =
                if matches!(&result, Ok(SolveResult::Sat)) {
                    let lra = self
                        .last_model
                        .as_mut()
                        .and_then(|model| model.lra_model.take());
                    let euf = self
                        .last_model
                        .as_mut()
                        .and_then(|model| model.euf_model.take());
                    let materialized = self
                        .last_model
                        .as_mut()
                        .map(|model| std::mem::take(&mut model.materialized_scalar_functions))
                        .unwrap_or_default();
                    (lra, euf, materialized)
                } else {
                    (None, None, HashMap::default())
                };
            result.map(|result| MixedSubproblemResult {
                result,
                lra_model,
                euf_model,
                materialized_scalar_functions,
            })
        }));
        self.ctx.assertions = saved_assertions;
        if let Some(borrow) = logic_borrow {
            self.ctx.end_internal_logic_borrow(borrow);
        }
        self.last_model = saved_model;
        self.last_result = saved_result;
        self.last_unknown_reason = saved_unknown;
        self.last_unknown_origin = saved_origin;
        self.last_model_validated = saved_validated;
        let result = match attempt {
            Ok(result) => result,
            Err(payload) => resume_unwind(payload),
        };
        // Recheck live controls and the now-grown term store AFTER restoration.
        // Canonical refusal must be the final writer of model/result authority.
        if let Err(origin) = self.fp_real_checkpoint(stop, observe, FpRealPhase::MixedRestored) {
            return Ok(without_models(self.fp_stopped(origin)));
        }
        result
    }

    /// Merge the completed mixed witness exactly as before. The enclosing owner
    /// checks its resource envelope before and after this model-building window.
    pub(super) fn build_merged_fp_real_model(
        &mut self,
        fp_model: &FpModel,
        mixed: MixedSubproblemResult,
        mixed_assertions: &[TermId],
        sat_model: &[bool],
        tseitin_result: &TseitinResult,
        undef_vars: &HashMap<String, TermId>,
    ) {
        let mut lra_model = mixed.lra_model.unwrap_or_else(|| LraModel {
            values: HashMap::default(),
        });
        let fp_to_real_vals =
            build_lra_model_from_fp_to_real(&self.ctx.terms, fp_model, mixed_assertions);
        for (k, v) in fp_to_real_vals.values {
            lra_model.values.entry(k).or_insert(v);
        }
        // Unspecified-but-total applications retain the exact value chosen by
        // the mixed solver, including congruent NaN/infinity operands.
        let roots: Vec<TermId> = self.ctx.assertions.clone();
        pin_undefined_fp_to_real(
            &self.ctx.terms,
            fp_model,
            undef_vars,
            &roots,
            &mut lra_model.values,
        );
        let term_to_var: HashMap<TermId, u32> = tseitin_result
            .term_to_var
            .iter()
            .map(|(&t, &v)| (t, v - 1))
            .collect();
        let mut model = Model::empty();
        model.sat_model = sat_model.to_vec();
        model.term_to_var = term_to_var;
        model.euf_model = mixed.euf_model;
        model.materialized_scalar_functions = mixed.materialized_scalar_functions;
        model.lra_model = if lra_model.values.is_empty() {
            None
        } else {
            Some(lra_model)
        };
        model.fp_model = Some(fp_model.clone());
        self.last_model = Some(model);
        self.last_model_validated = false;
        self.last_result = Some(SolveResult::Sat);
    }
}
