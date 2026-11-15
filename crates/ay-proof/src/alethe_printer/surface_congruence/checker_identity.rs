// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Congruence repairs whose identities pinned Carcara re-derives itself:
//! `refl` up to numeric-constant spelling and `=` order, `poly_simp`,
//! `evaluate` of a closed spelling, and a comparison reversal over respelled
//! literals — at one argument position, or for a whole printed side whose
//! operator the authored spelling changed.

use super::super::la_generic_surface::printed_poly_simp_holds;
use super::*;

impl AlethePrinter<'_> {
    /// A congruence whose printed side no longer has the internal operator:
    /// the authored `(* -1 y)` over the internal `(- y)` (a20, b01) prints
    /// `(= (* -1 y) (- (- 1)))`, and pinned Carcara refuses `cong` between
    /// two operators. Each such side is re-spelled as the printer's canonical
    /// rendering when `poly_simp` relates the two (judged by the pinned
    /// checker's own normalization, `printed_poly_simp_holds`); the ordinary
    /// position repair then bridges the canonical application, and `trans`
    /// joins `printed = canonical`, the `cong` and `canonical = printed`.
    /// `None` when no side needs it or any part has no checked derivation.
    pub(in crate::alethe_printer) fn head_respelled_cong_bridge(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Option<String> {
        let [conclusion] = clause else {
            return None;
        };
        if !args.is_empty() {
            return None;
        }
        let TermData::App(Symbol::Named(equality), sides) = self.terms.get(*conclusion) else {
            return None;
        };
        let [left, right] = sides.as_slice() else {
            return None;
        };
        let (
            TermData::App(left_symbol, left_internal_args),
            TermData::App(right_symbol, right_internal_args),
        ) = (self.terms.get(*left), self.terms.get(*right))
        else {
            return None;
        };
        if equality != "="
            || left_symbol != right_symbol
            || left_internal_args.len() != right_internal_args.len()
        {
            return None;
        }
        let operator = Self::format_symbol(left_symbol);
        let left_printed = self.format_term(*left);
        let right_printed = self.format_term(*right);
        if self.format_clause(clause) != format!("(cl (= {left_printed} {right_printed}))") {
            return None;
        }
        let (left_args, left_canonical) = self.respelled_side(*left, &left_printed, &operator)?;
        let (right_args, right_canonical) =
            self.respelled_side(*right, &right_printed, &operator)?;
        if left_canonical.is_none() && right_canonical.is_none() {
            return None;
        }
        if left_args.len() != left_internal_args.len()
            || right_args.len() != right_internal_args.len()
        {
            return None;
        }
        let application = SurfaceCongruenceApplication {
            left_args,
            right_args,
            left_internal_args: left_internal_args.clone(),
            right_internal_args: right_internal_args.clone(),
        };
        self.respelled_cong_steps(
            id,
            &application,
            premises,
            [&left_printed, &right_printed],
            [left_canonical.as_deref(), right_canonical.as_deref()],
        )
    }

    /// `printed`'s arguments under `operator`, or the canonical rendering's
    /// with that rendering, when `poly_simp` equates the two spellings.
    fn respelled_side(
        &self,
        term: TermId,
        printed: &str,
        operator: &str,
    ) -> Option<(Vec<String>, Option<String>)> {
        if let Some(arguments) = split_application(printed, operator) {
            return Some((arguments, None));
        }
        let canonical = crate::render_term_canonical(self.terms, term);
        let arguments = split_application(&canonical, operator)?;
        (printed_poly_simp_holds(printed, &canonical) == Some(true))
            .then_some((arguments, Some(canonical)))
    }

    /// The repaired `cong` over the respelled application and the `poly_simp`
    /// / `trans` chain back to the printed sides.
    fn respelled_cong_steps(
        &self,
        id: ProofId,
        application: &SurfaceCongruenceApplication,
        premises: &[ProofId],
        [left_printed, right_printed]: [&str; 2],
        [left_canonical, right_canonical]: [Option<&str>; 2],
    ) -> Option<String> {
        let premise_rows = self.surface_congruence_premises(premises).ok()?;
        let cong_id = format!("{id}.hc");
        let (generated, ordered) = [PremiseReading::Positional, PremiseReading::AllowReversed]
            .into_iter()
            .find_map(|reading| {
                self.repair_surface_congruence_positions(
                    &cong_id,
                    application,
                    &premise_rows,
                    reading,
                )
                .ok()
            })?;
        let middle_left = left_canonical.unwrap_or(left_printed);
        let middle_right = right_canonical.unwrap_or(right_printed);
        let mut output = generated;
        output.push(format!(
            "(step {cong_id} (cl (= {middle_left} {middle_right})) :rule cong :premises ({}))",
            ordered.join(" ")
        ));
        let mut chain = Vec::new();
        if let Some(canonical) = left_canonical {
            output.push(format!(
                "(step {id}.hl (cl (= {left_printed} {canonical})) :rule poly_simp)"
            ));
            chain.push(format!("{id}.hl"));
        }
        chain.push(cong_id);
        if let Some(canonical) = right_canonical {
            output.push(format!(
                "(step {id}.hr (cl (= {canonical} {right_printed})) :rule poly_simp)"
            ));
            chain.push(format!("{id}.hr"));
        }
        output.push(format!(
            "(step {id} (cl (= {left_printed} {right_printed})) :rule trans :premises ({}))",
            chain.join(" ")
        ));
        Some(output.join("\n"))
    }

    /// The identities pinned Carcara re-derives itself between two spellings
    /// of the position's internal term, tried after every narrower repair so
    /// a pair that bridged before bridges byte-identically:
    ///
    /// * `refl` up to numeric-constant spelling and `=` operand order
    ///   (`(= -2 x)` / `(= x (- 2))`; `surface_literal::carcara_refl_steps`);
    /// * `poly_simp` between two polynomials, which is how the authored
    ///   `(* -1 y)` meets the canonical `(- y)` (a20, b01) and `(- -2 -3)`
    ///   meets `1` (judged by the pinned checker's own normalization,
    ///   `printed_poly_simp_holds`);
    /// * `evaluate` of a closed `abs`/`+`/`-`/`*` spelling to the position's
    ///   constant (`surface_literal::ground_value_steps`);
    /// * a comparison whose bare negative literals are first respelled as the
    ///   printer renders them, then reversed (`(> -2 x)` / `(< x (- 2))`);
    /// * any of these under one `not`, closed by `cong`.
    pub(super) fn checker_identity_pair_steps(
        &self,
        id: &str,
        left: &str,
        right: &str,
        canonical_term: TermId,
    ) -> Option<Vec<String>> {
        if let Some(steps) = surface_literal::carcara_refl_steps(id, left, right) {
            return Some(steps);
        }
        if printed_poly_simp_holds(left, right) == Some(true) {
            return Some(vec![format!(
                "(step {id} (cl (= {left} {right})) :rule poly_simp)"
            )]);
        }
        if let Some(steps) =
            surface_literal::ground_value_steps(self.terms, id, left, right, canonical_term)
        {
            return Some(steps);
        }
        if let Some(steps) = self.respelled_comparison_reversal(id, left, right, canonical_term) {
            return Some(steps);
        }
        let TermData::Not(inner) = self.terms.get(canonical_term) else {
            return None;
        };
        let [left_atom] = <[String; 1]>::try_from(split_application(left, "not")?).ok()?;
        let [right_atom] = <[String; 1]>::try_from(split_application(right, "not")?).ok()?;
        let inner_id = format!("{id}.n");
        let mut steps = self
            .identity_surface_pair_steps(&inner_id, &left_atom, &right_atom, *inner)
            .ok()?;
        if steps.is_empty() {
            return None;
        }
        steps.push(format!(
            "(step {id} (cl (= {left} {right})) :rule cong :premises ({inner_id}))"
        ));
        Some(steps)
    }

    /// `comparison_reversal_pair_steps` once each side's bare negative
    /// literals are spelled as the printer renders them (`-2` -> `(- 2)`),
    /// joined to the authored spellings by `refl`.
    fn respelled_comparison_reversal(
        &self,
        id: &str,
        left: &str,
        right: &str,
        canonical_term: TermId,
    ) -> Option<Vec<String>> {
        let canonical = crate::render_term_canonical(self.terms, canonical_term);
        let left_respelled = surface_literal::canonical_literal_respelling(left);
        let right_respelled = surface_literal::canonical_literal_respelling(right);
        if left_respelled.is_none() && right_respelled.is_none() {
            return None;
        }
        let middle_left = left_respelled.as_deref().unwrap_or(left);
        let middle_right = right_respelled.as_deref().unwrap_or(right);
        let middle_id = format!("{id}.c");
        let mut steps =
            comparison_reversal_pair_steps(&middle_id, middle_left, middle_right, &canonical)?;
        let mut chain = Vec::new();
        if let Some(respelled) = &left_respelled {
            steps.extend(surface_literal::carcara_refl_steps(
                &format!("{id}.l"),
                left,
                respelled,
            )?);
            chain.push(format!("{id}.l"));
        }
        chain.push(middle_id);
        if let Some(respelled) = &right_respelled {
            steps.extend(surface_literal::carcara_refl_steps(
                &format!("{id}.r"),
                respelled,
                right,
            )?);
            chain.push(format!("{id}.r"));
        }
        steps.push(format!(
            "(step {id} (cl (= {left} {right})) :rule trans :premises ({}))",
            chain.join(" ")
        ));
        Some(steps)
    }
}

#[cfg(test)]
#[path = "checker_identity_tests.rs"]
mod tests;
