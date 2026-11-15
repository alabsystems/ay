// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reset every owner of the discarded FP CNF namespace together.

use super::FpSolver;

impl FpSolver<'_> {
    pub(super) fn reset_encoding_state(&mut self) {
        self.term_to_fp.clear();
        self.bv_term_bits.clear();
        self.clauses.clear();
        self.bool_input_lits.clear();
        self.to_bv_unspec_sites.clear();
        self.ieee_nan_encodings.clear();
        self.rm_terms.clear();
        self.pending_condition_links.clear();
        self.cached_false = None;
        self.cached_true = None;
        self.has_encoding_gap = false;
        self.next_var = 1;

        // Preserve the existing release-on-reset policy for every owned cache.
        self.term_to_fp.shrink_to_fit();
        self.bv_term_bits.shrink_to_fit();
        self.clauses.shrink_to_fit();
        self.bool_input_lits.shrink_to_fit();
        self.to_bv_unspec_sites.shrink_to_fit();
        self.ieee_nan_encodings.shrink_to_fit();
        self.rm_terms.shrink_to_fit();
        self.pending_condition_links.shrink_to_fit();

        // `terms` and `term_to_cnf` are the unchanged source and external
        // Tseitin namespace supplied at construction. Only the FP proxy side
        // of a condition link is invalidated; a fresh link must still name the
        // same external variable. Runtime statistics and debug settings also
        // retain their existing lifetime across reset.
    }
}

#[cfg(test)]
mod tests;
