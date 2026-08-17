// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface admissibility for Alethe `eq_transitive` steps.

use ay_core::{ProofId, TermId, TheoryLemmaKind, UNPROVED_STEP_RULE};

use super::AlethePrinter;

impl AlethePrinter<'_> {
    /// Resugar supported aliases or decline an unrenderable step to `hole`.
    pub(super) fn format_eq_transitive_or_hole(
        &self,
        id: ProofId,
        clause: &[TermId],
        kind: &TheoryLemmaKind,
    ) -> Option<String> {
        if kind.alethe_rule() != "eq_transitive" {
            return None;
        }
        if let Some(text) = self.resugar_eq_transitive(id, clause) {
            return Some(text);
        }
        (!self.eq_transitive_prints_spec_valid(clause)).then(|| {
            format!(
                "(step {id} {} :rule {UNPROVED_STEP_RULE})",
                self.format_clause(clause)
            )
        })
    }

    /// Whether the active surface is accepted by Alethe `eq_transitive`.
    ///
    /// The rule needs one positive-equality conclusion and at least two
    /// `(not (= ...))` hypotheses. In particular, a boolean-equality alias such
    /// as `(= (= a b) false)` is not an admissible hypothesis.
    fn eq_transitive_prints_spec_valid(&self, clause: &[TermId]) -> bool {
        if clause.len() < 3 {
            return false;
        }
        let mut conclusions = 0usize;
        let mut hypotheses = 0usize;
        for literal in clause.iter().map(|&literal| self.format_term(literal)) {
            if literal.starts_with("(not (= ") {
                hypotheses += 1;
            } else if literal.starts_with("(= ") {
                conclusions += 1;
            } else {
                return false;
            }
        }
        conclusions == 1 && hypotheses >= 2
    }
}
