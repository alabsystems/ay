// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked lowering for promoted integer-linear proof rules.

use ay_core::term::{Symbol, TermData};
use ay_core::{FarkasAnnotation, ProofId, TermId, TheoryLit};

use super::{format_rational64, AlethePrinter};

impl AlethePrinter<'_> {
    /// Render an independently evaluated ground LIA unit through the exact
    /// rules implemented by the pinned external checker.
    pub(super) fn format_lia_ground_evaluate(
        &self,
        id: ProofId,
        clause: &[TermId],
        clause_str: &str,
    ) -> Option<String> {
        if clause_str != AlethePrinter::new(self.terms).format_clause(clause) {
            return None;
        }
        if crate::checker::validate_ground_evaluate_for_printer(self.terms, id, clause, 0, &[])
            .is_ok()
        {
            return Some(format!("(step {id} {clause_str} :rule evaluate)"));
        }

        let [literal] = clause else {
            return None;
        };
        let TermData::Not(equality) = self.terms.get(*literal) else {
            return None;
        };
        let TermData::App(Symbol::Named(operator), operands) = self.terms.get(*equality) else {
            return None;
        };
        if operator != "="
            || operands.len() != 2
            || !crate::checker::recognize_ground_evaluate(self.terms, *literal)
        {
            return None;
        }

        let equality = self.format_term(*equality);
        let literal = self.format_term(*literal);
        Some(format!(
            "(step {id}.ev (cl (= {equality} false)) :rule evaluate)\n\
             (step {id}.q (cl {literal} false) :rule equiv1 :premises ({id}.ev))\n\
             (step {id}.f (cl (not false)) :rule false)\n\
             (step {id} {clause_str} :rule resolution :premises ({id}.q {id}.f))"
        ))
    }

    /// Render a promoted ground-evaluation step, if that is the selected rule.
    ///
    /// The publication wire-gap gate and printer share the complete-step
    /// decision. Unexpected disagreement with the ground formatter remains an
    /// honest `hole`, never an unchecked rule claim.
    pub(super) fn format_promoted_lia_evaluation(
        &self,
        id: ProofId,
        clause: &[TermId],
        clause_str: &str,
        wire_rule: &str,
    ) -> Option<String> {
        (wire_rule == "evaluate").then(|| {
            self.format_lia_ground_evaluate(id, clause, clause_str)
                .unwrap_or_else(|| {
                    format!(
                        "(step {id} {clause_str} :rule {})",
                        ay_core::UNPROVED_STEP_RULE
                    )
                })
        })
    }

    /// Format a Farkas-annotated theory lemma using its selected wire rule.
    pub(super) fn format_farkas_theory_lemma(
        &self,
        id: ProofId,
        clause: &[TermId],
        clause_str: &str,
        rule: &str,
        farkas: &FarkasAnnotation,
    ) -> String {
        if rule == ay_core::UNPROVED_STEP_RULE {
            return format!("(step {id} {clause_str} :rule {rule})");
        }
        let printed_coefficients = if rule == "la_generic" {
            self.printed_farkas_coefficients(clause, farkas)
        } else {
            farkas.coefficients.clone()
        };
        let coefficients: Vec<String> =
            printed_coefficients.iter().map(format_rational64).collect();
        format!(
            "(step {} {} :rule {} :args ({}))",
            id,
            clause_str,
            rule,
            coefficients.join(" ")
        )
    }

    fn printed_farkas_coefficients(
        &self,
        clause: &[TermId],
        farkas: &FarkasAnnotation,
    ) -> Vec<num_rational::Rational64> {
        let conflict: Vec<TheoryLit> = clause
            .iter()
            .map(|&literal| match self.terms.get(literal) {
                TermData::Not(inner) => TheoryLit {
                    term: *inner,
                    value: true,
                },
                _ => TheoryLit {
                    term: literal,
                    value: false,
                },
            })
            .collect();
        let existing = ay_core::proof_validation::resolve_equality_coefficient_signs(
            self.terms, &conflict, farkas,
        )
        .unwrap_or_else(|| farkas.coefficients.clone());
        let printed_atoms: Vec<(String, bool)> = conflict
            .iter()
            .map(|literal| (self.format_term(literal.term), literal.value))
            .collect();
        crate::la_generic_signs::resolve_printed_la_generic_coefficients(
            &printed_atoms,
            &existing,
            &farkas.coefficients,
        )
    }
}
