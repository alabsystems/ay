// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lower a two-literal clause that states ONE atom under two authored
//! spellings.
//!
//! WHY THE SHAPE EXISTS. The authored-surface channel keeps one spelling per
//! `TermId` and, where elaboration folded two authored terms together, the
//! outermost authored spelling (`collect_deep_array_surface_overrides`). A
//! problem file that writes both `(= (seq_offset s) 0)` and
//! `(+ (seq_offset s) 0)` therefore ships two printed atoms for one fact, and
//! the producer bridges them with the two-literal clause `(cl A (not B))`.
//!
//! WHY IT WAS A HOLE. That clause is labelled `LraFarkas`, but carcara's
//! `la_generic` cannot check ANY clause carrying a POSITIVE equality: its
//! `negate_disequality` turns a literal into one linear row, and the negation
//! of an equality is a disjunction of two. `promoted_wire_rule` says so —
//! it answers `UNPROVED_STEP_RULE` for exactly these clauses — so the step
//! shipped as an honest `hole`, and every `--strict-proofs` consumer of a
//! document carrying one lost the verdict.
//!
//! WHAT IS EMITTED. `poly_simp` (or `refl`) per operand, `cong` to
//! `(= B A)`, `equiv_pos2`, and one resolution. Carcara re-derives every
//! step; `printed_poly_simp_holds` — the replay of the pinned checker's own
//! normalizer — must answer `Some(true)` for each operand bridge before any
//! of it is emitted, and the whole lowering is reached ONLY where the wire
//! rule is already the hole, so it can never displace a rule the checker
//! accepts. MEASURED against carcara 1.1.0 (git 9a352ee): both the
//! respelled form `(cl (= s 0) (not (= (+ s 0) 0)))` and the identical form
//! `(cl A (not A))` check `valid`, and perturbing an operand bridge to a
//! different polynomial makes the document `invalid` at that step.

use super::*;

impl AlethePrinter<'_> {
    /// Largest printed operand this lowering will bridge.
    const MAX_RESPELLED_OPERAND: usize = 8192;

    pub(super) fn format_respelled_atom_implication(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        if self.work_budget_exhausted() {
            return None;
        }
        let [first, second] = clause else {
            return None;
        };
        // `(cl A (not B))` in either printed order. A doubly-negated pair is
        // not this shape and must keep its hole.
        let (positive, negated, negative_literal) =
            if let TermData::Not(inner) = self.terms.get(*first) {
                (*second, *inner, *first)
            } else if let TermData::Not(inner) = self.terms.get(*second) {
                (*first, *inner, *second)
            } else {
                return None;
            };
        if matches!(self.terms.get(positive), TermData::Not(_)) {
            return None;
        }
        // EQUALITY only. An order relation is a literal `la_generic` CAN read,
        // so narrowing here keeps this lowering to the clauses the wire rule
        // has already given up on for a reason no bridge changes.
        if !is_binary_equality(self.terms, positive) || !is_binary_equality(self.terms, negated) {
            return None;
        }
        let conclusion = self.format_term(positive);
        let hypothesis = self.format_term(negated);
        let printed_negative = self.format_term(negative_literal);
        if [&conclusion, &hypothesis, &printed_negative]
            .iter()
            .any(|text| text.len() > Self::MAX_RESPELLED_OPERAND)
        {
            return None;
        }
        // An override on the outer `not` node can differ from the independently
        // printed atom. The final resolution only proves `(not hypothesis)`,
        // so it must not conclude a differently spelled literal from the IR
        // clause without a checked bridge for that spelling too.
        if !surface_literal::same_printed_term(&printed_negative, &format!("(not {hypothesis})")) {
            return None;
        }

        let equivalence = format!("(= {hypothesis} {conclusion})");
        let mut steps = String::new();
        if surface_literal::same_printed_term(&hypothesis, &conclusion) {
            let _ = std::fmt::Write::write_fmt(
                &mut steps,
                format_args!("(step {id}.ri.e (cl {equivalence}) :rule refl)\n"),
            );
        } else {
            let hypothesis_args = split_application(&hypothesis, "=")?;
            let conclusion_args = split_application(&conclusion, "=")?;
            let ([from_left, from_right], [to_left, to_right]) = (
                <[String; 2]>::try_from(hypothesis_args).ok()?,
                <[String; 2]>::try_from(conclusion_args).ok()?,
            );
            let mut premises = Vec::with_capacity(2);
            for (position, (from, to)) in [(from_left, to_left), (from_right, to_right)]
                .into_iter()
                .enumerate()
            {
                if from.len() > Self::MAX_RESPELLED_OPERAND
                    || to.len() > Self::MAX_RESPELLED_OPERAND
                {
                    return None;
                }
                let rule = respelled_operand_rule(&from, &to)?;
                let _ = std::fmt::Write::write_fmt(
                    &mut steps,
                    format_args!("(step {id}.ri.{position} (cl (= {from} {to})) :rule {rule})\n"),
                );
                premises.push(format!("{id}.ri.{position}"));
            }
            let _ = std::fmt::Write::write_fmt(
                &mut steps,
                format_args!(
                    "(step {id}.ri.e (cl {equivalence}) :rule cong :premises ({}))\n",
                    premises.join(" ")
                ),
            );
        }
        let _ = std::fmt::Write::write_fmt(
            &mut steps,
            format_args!(
                "(step {id}.ri.q (cl (not {equivalence}) (not {hypothesis}) {conclusion}) :rule equiv_pos2)\n\
                 (step {id} {} :rule resolution :premises ({id}.ri.e {id}.ri.q))",
                self.format_clause(clause)
            ),
        );
        self.charge(steps.len() as u64);
        (!self.work_budget_exhausted()).then_some(steps)
    }
}

/// The COMPLETE wire-rule table of this lowering: the rule that bridges one
/// printed operand to its respelling, or `None` where no checked bridge
/// exists.
///
/// This is the only place `format_respelled_atom_implication` can take a
/// `:rule` name from, and it is spelled as its own function so that the names
/// are a brace-delimited production table the wire-rule coverage test reads
/// field-by-field -- the same way it reads `decode_idempotent_bv_gate`'s arms.
/// A new bridge rule therefore enters the external carcara probe by being
/// written here, with no second hand-maintained list to forget.
///
/// Same conditions, same order, same `Option` result as the local conditional
/// it replaces: the emitted wire bytes are unchanged.
fn respelled_operand_rule(from: &str, to: &str) -> Option<&'static str> {
    if surface_literal::same_printed_term(from, to) {
        Some("refl")
    } else if la_generic_surface::printed_poly_simp_holds(from, to) == Some(true) {
        Some("poly_simp")
    } else {
        None
    }
}

/// `true` for a binary `=` application — the one literal shape carcara's
/// `la_generic` refuses outright when it appears POSITIVELY.
fn is_binary_equality(terms: &TermStore, term: TermId) -> bool {
    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2
    )
}

#[cfg(test)]
mod tests;
