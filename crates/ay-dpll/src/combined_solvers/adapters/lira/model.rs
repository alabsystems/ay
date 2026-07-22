// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction and `to_int` value patching for the LIRA combined solver.
//!
//! After extracting LIA and LRA models independently, patches the LIA model
//! so that `to_int(x)` values agree with `floor(x)` from the LRA model.
//! Without this, LIA treats `to_int(x)` as a free integer variable (#5944).

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_lia::LiaModel;
use ay_lra::LraModel;

use crate::combined_solvers::models::reconcile_lia_lra_values;

use super::LiraSolver;

impl LiraSolver<'_> {
    /// Extract both models for model generation.
    ///
    /// After extracting, patches LIA model values for `to_int(x)` terms
    /// so that the LIA model agrees with `floor(x)` from the LRA model.
    /// Without this, the LIA and LRA models may disagree on `to_int` values
    /// because LIA treats `to_int(x)` as a free integer variable (#5944).
    pub(crate) fn extract_models(&mut self) -> (Option<LiaModel>, LraModel) {
        let mut lia_model = self.lia.extract_model();
        let mut lra_model = self.lra.extract_model();

        // Patch to_int values: use floor(arg_value) from LRA model
        if let Some(ref mut lia) = lia_model {
            for &(to_int_var, inner_arg_term) in self.lra.to_int_terms() {
                if let Some(to_int_term) = self.lra.var_term_id(to_int_var) {
                    if let Some(arg_val) = lra_model.values.get(&inner_arg_term) {
                        let floored = arg_val.floor().to_integer();
                        lia.values.insert(to_int_term, floored);
                    }
                }
            }

            // Reconcile Int-sorted shared variables (#6227):
            // When z = to_real(y) and y = to_int(x), the LRA model may have
            // y's value as the raw simplex value (not floor(x)). Copy LIA's
            // patched integer values into the LRA model only when the LRA value
            // is non-integral. If LRA found an integral value through tighter
            // `to_real(y)` constraints, keep it and update LIA instead.
            let patched_lra_terms = reconcile_lia_lra_values(
                &mut lia_model,
                &mut lra_model,
                &self.lia.shared_equality_terms(),
            );
            if !patched_lra_terms.is_empty() {
                let patched_var_ids: HashSet<u32> = patched_lra_terms
                    .iter()
                    .filter_map(|t| self.lra.term_to_var().get(t).copied())
                    .collect();
                self.lra
                    .propagate_model_equalities(&mut lra_model, &patched_var_ids);
            }
        }

        (lia_model, lra_model)
    }
}
