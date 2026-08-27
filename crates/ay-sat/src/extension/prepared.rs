// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extension state prepared during SAT preprocessing.

use crate::Variable;

/// Extension instance prepared during the SAT solver's preprocessing phase.
///
/// A downstream crate can inspect the irredundant clause snapshot, transfer
/// exact clauses to a theory-specific extractor, and freeze every shared
/// variable before destructive SAT preprocessing continues.
pub struct PreparedExtension<E> {
    /// The extension to activate once SAT preprocessing finishes.
    pub extension: E,
    /// Positions in the builder's clause snapshot owned by the extension.
    pub consumed_clause_positions: Vec<usize>,
    /// Variables frozen before destructive SAT preprocessing continues.
    pub frozen_variables: Vec<Variable>,
}

impl<E> PreparedExtension<E> {
    /// Create a prepared extension and canonicalize its metadata.
    pub fn new(
        extension: E,
        mut consumed_clause_positions: Vec<usize>,
        mut frozen_variables: Vec<Variable>,
    ) -> Self {
        consumed_clause_positions.sort_unstable();
        consumed_clause_positions.dedup();
        frozen_variables.sort_unstable_by_key(|var| var.index());
        frozen_variables.dedup_by_key(|var| var.index());
        Self {
            extension,
            consumed_clause_positions,
            frozen_variables,
        }
    }
}
