// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::{Arc, Mutex};

use ay_core::TermId;

use crate::preprocess::{Preprocessor, VariableSubstitution};

use super::Executor;

impl Executor {
    pub(super) fn preprocess_pure_bv_assertions(
        &mut self,
    ) -> (
        Arc<Mutex<VariableSubstitution>>,
        Vec<TermId>,
        Vec<Vec<TermId>>,
    ) {
        let mut preprocessed = self.ctx.assertions.clone();
        let mut source_sets: Vec<Vec<TermId>> = preprocessed
            .iter()
            .map(|&assertion| vec![assertion])
            .collect();
        let (mut preprocessor, var_subst, propagate_values) =
            Preprocessor::new_with_subst_and_propagation();
        preprocessor.preprocess_with_sources(
            &mut self.ctx.terms,
            &mut preprocessed,
            &mut source_sets,
        );
        // Drain once after the final preprocessing run at this pure-BV site.
        self.extend_propagated_value_provenance(&propagate_values);
        (var_subst, preprocessed, source_sets)
    }
}
