// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{Proof, ProofId, ProofStep};

impl Proof {
    /// Get a step by ID
    #[must_use]
    pub fn get_step(&self, id: ProofId) -> Option<&ProofStep> {
        self.steps.get(id.0 as usize)
    }

    /// Get the number of steps
    #[must_use]
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Check if the proof is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}
