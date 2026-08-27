// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recovery of variables eliminated by LIA/NIA preprocessing.

use super::*;

impl Executor {
    pub(super) fn recover_preprocessed_lia_model(&mut self, var_subst: &VariableSubstitution) {
        if let Some(model) = self
            .last_model
            .as_mut()
            .and_then(|model| model.lia_model.as_mut())
        {
            recover_substituted_lia_values(&self.ctx.terms, var_subst, model);
            recover_lia_equalities_from_assertions(&self.ctx.terms, &self.ctx.assertions, model);
        }

        // Bool variables eliminated by VariableSubstitution are absent from the
        // SAT model. Re-evaluate their replacement terms under the recovered LIA
        // values before validation of the original assertions.
        if let Some(ref full_model) = self.last_model {
            let lia_values = full_model
                .lia_model
                .as_ref()
                .map(|model| &model.values)
                .cloned()
                .unwrap_or_default();
            let bool_overrides =
                recover_substituted_bool_values(&self.ctx.terms, var_subst, &lia_values);
            if !bool_overrides.is_empty() {
                if let Some(ref mut full_model) = self.last_model {
                    full_model.bool_overrides.extend(bool_overrides);
                }
            }
        }
    }
}
