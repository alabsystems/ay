// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Demand-gated model-output refinement.

use super::Executor;

impl Executor {
    pub(super) fn maybe_aggressively_minimize_model_for_output(&mut self) {
        // Additional BV/LIA/LRA passes specifically target pinning values to
        // 0/1, giving inter-variable constraints more opportunity to converge
        // to a globally minimal counterexample (#8297).
        if self.aggressive_model_minimize
            && self.model_output_is_demanded()
            && self.last_assumptions.is_none()
            && !self.defer_counterexample_minimization
        {
            self.aggressive_minimize_model();
        }
    }
}
