// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-only diagnostics and trace-processability checks.

use super::*;

impl SatProofManager<'_> {
    /// Return the minimum and maximum SAT-variable indexes absent from the
    /// term map, together with the number of mapped variables.
    pub(crate) fn unmapped_var_range(&self) -> (Option<u32>, Option<u32>, usize) {
        (
            self.unmapped_var_min,
            self.unmapped_var_max,
            self.var_to_term.len(),
        )
    }

    /// Return the number of trace entries dropped because they could not be
    /// translated to SMT terms.
    pub(crate) fn untranslatable_entries(&self) -> u32 {
        self.untranslatable_entries
    }

    /// Return the number of learned clauses whose hint reconstruction fell
    /// back to `AletheRule::Trust`.
    pub(crate) fn trust_fallback_count(&self) -> u32 {
        self.trust_fallback_count
    }

    /// Check if the trace has at least one clause with all variables mapped.
    ///
    /// This method inspects the variable map without modifying the term store.
    pub(crate) fn can_process(&self, trace: &ClauseTrace) -> bool {
        if trace.is_empty() {
            return trace.has_empty_clause();
        }

        trace.entries().iter().any(|entry| {
            entry.clause.iter().all(|lit| {
                let var_idx = lit.variable().index() as u32;
                self.var_to_term.contains_key(&var_idx)
                    || self.is_scope_assumption_variable(var_idx)
            })
        })
    }
}
