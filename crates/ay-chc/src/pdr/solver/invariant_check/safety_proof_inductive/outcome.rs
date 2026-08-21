// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::InvariantModel;

/// Result of the inductive-subset model search.
pub(in crate::pdr::solver::invariant_check) enum InductiveSubsetOutcome {
    /// Found a verified model that blocks all errors.
    Proven(InvariantModel),
    /// No result from inductive subset; returns the model for cascade.
    Cascade(InvariantModel),
}
