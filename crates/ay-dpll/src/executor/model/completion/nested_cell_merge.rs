// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The array-valued cells of an array of arrays in
//! `merge_array_completion_candidate`.
//!
//! Such a cell is the rendered text of an inner array, and one inner array has
//! many spellings, so a text comparison made every second spelling a conflict
//! that tainted the array. The cells merge as arrays instead
//! (`executor_format/array_cell.rs`), under the outer default policy at every
//! level: the reads-derived pass (`Preserve`) keeps the extracted inner
//! else-value as it keeps the outer one; a target with a semantic
//! `(default ..)` value (`Require`) needs the two inner else-values to agree,
//! so a definition whose inner else-value the extracted cell contradicts still
//! takes the strict conflict -> taint path; any other defined target
//! (`Ignore`) inherits the definition's inner else-value, as it inherits the
//! outer one. Stored cells are observations under every policy: one index
//! with two different values is a conflict.

use super::ExistingArrayDefaultPolicy;
use crate::executor::Executor;
use crate::executor_format::array_cell::{merge_array_cells, CellDefaultPolicy};

impl Executor {
    /// The merge of an extracted array-valued cell and a completion
    /// candidate's cell at one index under the outer `policy`; `None` is a
    /// conflict.
    pub(super) fn merge_nested_cell(
        existing: &str,
        candidate: &str,
        policy: ExistingArrayDefaultPolicy,
    ) -> Option<String> {
        let policy = match policy {
            ExistingArrayDefaultPolicy::Preserve => CellDefaultPolicy::Preserve,
            ExistingArrayDefaultPolicy::Require => CellDefaultPolicy::Require,
            ExistingArrayDefaultPolicy::Ignore => CellDefaultPolicy::Ignore,
        };
        merge_array_cells(existing, candidate, policy)
    }
}

#[cfg(test)]
#[path = "nested_cell_merge_tests.rs"]
mod tests;
