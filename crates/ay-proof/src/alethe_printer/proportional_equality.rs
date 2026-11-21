// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Re-prove a proportional affine equality through two checked rational
//! bounds and the ordinary equality/disequality split. Producer hints are
//! neither trusted nor consumed, and the original literal order is retained.

use super::*;

#[must_use]
pub fn arith_proportional_equality_lowering_supported(
    terms: &TermStore,
    kind: &ay_core::TheoryLemmaKind,
    clause: &[TermId],
    overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    if !matches!(kind, ay_core::TheoryLemmaKind::ArithClauseTautology)
        || ay_core::proof_validation::arith_proportional_equality_witness(terms, clause).is_none()
    {
        return false;
    }
    let printer =
        AlethePrinter::new_with_overrides_and_budget(terms, overrides, Some(4 * 1024 * 1024));
    // The generated derivation binds all its own premises. Keep publication's
    // printed-premise checks active rather than treating this as a raw step.
    printer.printed_clause_ledger_active.set(true);
    let step = ProofStep::TheoryLemma {
        theory: "arith".into(),
        clause: clause.to_vec(),
        farkas: None,
        kind: *kind,
        lia: None,
    };
    // The actual format_step chokepoints judge every printed la_generic,
    // la_disequality and Boolean surface step, just as publication does.
    printer
        .format_step(&step, ProofId(0))
        .is_ok_and(|text| text.contains(":rule la_disequality") && !text.contains(":rule hole"))
}

impl AlethePrinter<'_> {
    pub(super) fn format_arith_proportional_equality(
        &self,
        id: ProofId,
        kind: &ay_core::TheoryLemmaKind,
        clause: &[TermId],
    ) -> Option<String> {
        if !matches!(kind, ay_core::TheoryLemmaKind::ArithClauseTautology) {
            return None;
        }
        let witness =
            ay_core::proof_validation::arith_proportional_equality_witness(self.terms, clause)?;
        let [premise, conclusion] = witness.ordered;
        let TermData::Not(source) = self.terms.get(premise) else {
            return None;
        };
        let TermData::App(_, source_args) = self.terms.get(*source) else {
            return None;
        };
        let TermData::App(_, target_args) = self.terms.get(conclusion) else {
            return None;
        };
        let [pl, pr] = source_args.as_slice() else {
            return None;
        };
        let [ql, qr] = target_args.as_slice() else {
            return None;
        };
        // Keep this first capability on the native operands' own typed
        // spelling. Whole equalities may reverse orientation below, but an
        // interior override cannot introduce an ill-sorted arithmetic atom
        // that the external row judge (which does not infer sorts) overlooks.
        let canonical =
            AlethePrinter::new_with_overrides_and_budget(self.terms, None, Some(4 * 1024 * 1024));
        for operand in [*pl, *pr, *ql, *qr] {
            if self.format_term(operand) != canonical.format_term(operand) {
                return None;
            }
        }
        if canonical.work_budget_exhausted() {
            return None;
        }
        let literal = |term| {
            let mut text = String::new();
            self.write_derived_literal_into(&mut text, term);
            text
        };
        let premise_text = literal(premise);
        let conclusion_text = literal(conclusion);
        let pl = self.format_term(*pl);
        let pr = self.format_term(*pr);
        let ql = self.format_term(*ql);
        let qr = self.format_term(*qr);
        let (source_reversed, source_text) = if premise_text == format!("(not (= {pl} {pr}))") {
            (false, format!("(= {pl} {pr})"))
        } else if premise_text == format!("(not (= {pr} {pl}))") {
            (true, format!("(= {pr} {pl})"))
        } else {
            return None;
        };
        let (left, right, target_reversed) = if conclusion_text == format!("(= {ql} {qr})") {
            (ql, qr, false)
        } else if conclusion_text == format!("(= {qr} {ql})") {
            (qr, ql, true)
        } else {
            return None;
        };
        // The exact negative literal, not format_term(inner), is the source
        // of the two bound clauses. An outer-Not override cannot rewrite it.
        if premise_text != format!("(not {source_text})") {
            return None;
        }
        let mut multiplier = witness.multiplier;
        if source_reversed != target_reversed {
            multiplier = -multiplier;
        }
        let coefficient = |value| {
            Self::format_constant(&Constant::Rational(ay_core::term::RationalWrapper(value)))
        };
        let forward_weight = coefficient(-multiplier.clone());
        let reverse_weight = coefficient(multiplier);
        if self.work_budget_exhausted() || self.emission_progress.refused() {
            return None;
        }
        let forward = format!("(<= {left} {right})");
        let reverse = format!("(<= {right} {left})");
        let finish = if witness.ordered.as_slice() == clause {
            format!("(step {id} (cl {premise_text} {conclusion_text}) :rule reordering :premises ({id}.both))")
        } else {
            format!("(step {id} (cl {conclusion_text} {premise_text}) :rule reordering :premises ({id}.both))")
        };
        Some(format!(
            "(step {id}.split (cl (or {conclusion_text} (not {forward}) (not {reverse}))) :rule la_disequality)\n\
             (step {id}.flat (cl {conclusion_text} (not {forward}) (not {reverse})) :rule or :premises ({id}.split))\n\
             (step {id}.lo (cl {forward} {premise_text}) :rule la_generic :args (1 {forward_weight}))\n\
             (step {id}.hi (cl {reverse} {premise_text}) :rule la_generic :args (1 {reverse_weight}))\n\
             (step {id}.mid (cl {conclusion_text} (not {reverse}) {premise_text}) :rule resolution :premises ({id}.flat {id}.lo))\n\
             (step {id}.both (cl {conclusion_text} {premise_text}) :rule resolution :premises ({id}.mid {id}.hi))\n\
             {finish}"
        ))
    }
}

#[cfg(test)]
mod tests;
