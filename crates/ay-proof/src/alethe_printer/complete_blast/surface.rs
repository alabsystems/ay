// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bind every bit-blasted node to the term the consumer actually parses.

use super::super::surface_literal::same_printed_term;
use super::*;

impl AlethePrinter<'_> {
    /// Children are checked first by the bounded DAG traversal. An override
    /// must retain this node's constructor and its checked child spellings;
    /// constants and variables must retain their own canonical spelling.
    /// Checking every node also catches a parent override hiding a changed
    /// descendant. Propositional replay cannot validate these word premises.
    pub(super) fn complete_blast_surface_agrees(&self, term: TermId) -> Option<()> {
        self.charge(1);
        if self.work_budget_exhausted() {
            return None;
        }
        let overridden = self
            .term_overrides
            .is_some_and(|overrides| overrides.contains_key(&term))
            || self.skolem_overrides.borrow().contains_key(&term)
            || self.let_bridge_renderings.borrow().contains_key(&term);
        if !overridden {
            return Some(());
        }
        let actual = self.format_term(term);
        let expected = self.format_term_data(self.terms.get(term));
        // A bit-vector literal re-spelled (`#x00` for `#b00000000`) is ONE
        // term to the consumer's parser, so it binds the same node.
        let agrees = same_printed_term(&actual, &expected);
        if !agrees && ay_core::misc_cli_flags().debug_cert {
            let shared = actual
                .chars()
                .zip(expected.chars())
                .take_while(|(left, right)| left == right)
                .count();
            let actual_tail: String = actual.chars().skip(shared).take(192).collect();
            let expected_tail: String = expected.chars().skip(shared).take(192).collect();
            ay_core::safe_eprintln!(
                "c !! complete-blast surface mismatch: actual_bytes={} structural_bytes={} shared_chars={} actual={actual_tail:?} structural={expected_tail:?}",
                actual.len(), expected.len(), shared,
            );
        }
        (agrees && !self.work_budget_exhausted()).then_some(())
    }
}
