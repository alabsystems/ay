// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The same-operator `cong` step behind the order-reversal bridge
//! (`AlethePrinter::surface_order_cong_bridge`), with its premises repaired
//! position by position exactly as the multiplication bridge repairs them.
//!
//! THE SHAPE THIS REPAIRS. `(assert (= x1 (* 3 m1)))` interns as
//! `(= x1 (* m1 3))`; the authored-assume planner bridges that `assume` to its
//! canonical rendering, so every later step prints the premise as
//! `(= x1 (* m1 3))`, while the subterm `(* m1 3)` keeps its own override and
//! prints `(* 3 m1)` everywhere else. `(assert (not (> x1 60000)))` leaves the
//! atom `(< 60000 x1)` with the override `(> x1 60000)`. Equality substitution
//! then produces the internal congruence
//!
//! ```text
//! (= (< 60000 x1) (< 60000 (* m1 3)))   premise (= x1 (* m1 3))
//! ```
//!
//! printed as `(= (> x1 60000) (< 60000 (* 3 m1)))`. The order bridge proved
//! the comparison reversal but then demanded the printed premise be exactly
//! `(= x1 (* 3 m1))`; it is `(= x1 (* m1 3))`, so the bridge declined, the
//! different-operator guard refused the step, and `QF_LIA` cascade inputs with
//! that spelling published `unsat` with no document at all (measured at
//! 5fb7fc52a: `(assert (not (> x1 60000)))` and `(assert (not (>= x1 60001)))`
//! refuse, while `(<= x1 60000)`, `(>= 60000 x1)` and `(not (< 60000 x1))` —
//! whose atom has no reversed override — and the same input with
//! `(= x1 (* m1 3))` authored all print carcara-valid documents).
//!
//! The premise is now repaired with the same checked steps the multiplication
//! bridge uses — a premise matched by its INTERNAL endpoints, then `trans`
//! with a certified multiplication-commutation equality on either side — so
//! the `cong` below is an ordinary same-operator instance over the printed
//! operands. A printed premise that already IS the differing pair, in either
//! orientation (`cong` accepts a flipped premise), is cited as is, so every
//! step that rendered before renders byte-identically.

use super::*;

impl AlethePrinter<'_> {
    /// `(step {id} (cl (= {canonical_left} {canonical_right})) :rule cong ..)`
    /// over the internal applications `left` and `right`, preceded by the
    /// checked repair of every premise whose printed endpoints differ from the
    /// printed arguments, or `None` when a differing argument has no premise
    /// over its internal endpoints, a premise is left unused, or a spelling
    /// has no certified repair.
    pub(in crate::alethe_printer) fn canonical_order_cong_steps(
        &self,
        id: &str,
        left: TermId,
        right: TermId,
        canonical: [&str; 2],
        premises: &[ProofId],
    ) -> Option<Vec<String>> {
        let (
            TermData::App(left_symbol, left_internal_args),
            TermData::App(right_symbol, right_internal_args),
        ) = (self.terms.get(left), self.terms.get(right))
        else {
            return None;
        };
        if left_symbol != right_symbol || left_internal_args.len() != right_internal_args.len() {
            return None;
        }
        let operator = Self::format_symbol(left_symbol);
        let [canonical_left, canonical_right] = canonical;
        let left_args = split_application(canonical_left, &operator)?;
        let right_args = split_application(canonical_right, &operator)?;
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
        let premise_rows = self.surface_congruence_premises(premises).ok()?;
        if let Some(premise) = printed_as_differing_pair(&application, &premise_rows) {
            return Some(vec![format!(
                "(step {id} (cl (= {canonical_left} {canonical_right})) :rule cong :premises ({premise}))"
            )]);
        }
        let (mut steps, ordered_premises) = self
            .repair_surface_congruence_positions(
                id,
                &application,
                &premise_rows,
                PremiseReading::Positional,
            )
            .ok()?;
        if ordered_premises.is_empty() {
            return None;
        }
        steps.push(format!(
            "(step {id} (cl (= {canonical_left} {canonical_right})) :rule cong :premises ({}))",
            ordered_premises.join(" ")
        ));
        Some(steps)
    }
}

impl AlethePrinter<'_> {
    /// `cong` between two comparisons whose overrides re-spell EITHER side,
    /// or both, as the argument-reversed comparison.
    ///
    /// THE SHAPE. `surface_order_cong_bridge` repairs exactly one reversed
    /// LEFT side over one premise. Substitution through an `or` produces the
    /// mirror image too: the internal `(= (<= 3 x2) (<= 3 x1))` printed
    /// `(= (<= 3 x2) (>= x1 3))` because the RIGHT atom is the one the author
    /// wrote reversed, or with both atoms authored reversed; and a congruence
    /// over a whole disjunct list carries one premise per changed position.
    /// Measured on the OR-substitution fuzz: those steps refused with
    /// "different order operators" (22 of 1,200 files).
    ///
    /// THE DERIVATION. Each reversed side is related to its canonical
    /// same-operator spelling by `comp_simplify` (the shared
    /// `comparison_reversal_step`, which screens that rule's evaluation quirk),
    /// the canonical spellings are related by the same-operator `cong` that
    /// [`Self::canonical_order_cong_steps`] repairs position by position, and
    /// `trans` composes the chain into the printed conclusion. Fail-closed:
    /// any side that is neither its canonical spelling nor an exact
    /// argument-reversed comparison of it declines, and so does a step with no
    /// reversed side at all (it is not this shape).
    pub(in crate::alethe_printer) fn surface_order_cong_bridge_either_side(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Option<String> {
        let [conclusion] = clause else {
            return None;
        };
        if !args.is_empty() || premises.is_empty() {
            return None;
        }
        let TermData::App(Symbol::Named(equality), sides) = self.terms.get(*conclusion) else {
            return None;
        };
        let [left, right] = sides.as_slice() else {
            return None;
        };
        let (TermData::App(left_symbol, left_args), TermData::App(right_symbol, right_args)) =
            (self.terms.get(*left), self.terms.get(*right))
        else {
            return None;
        };
        if equality != "="
            || left_symbol != right_symbol
            || left_args.len() != 2
            || right_args.len() != 2
        {
            return None;
        }
        let operator = Self::format_symbol(left_symbol);
        if !matches!(operator.as_str(), "<=" | "<" | ">=" | ">") {
            return None;
        }
        let [printed_left, printed_right]: [String; 2] =
            split_application(&self.format_term(*conclusion), "=")?
                .try_into()
                .ok()?;
        // A side printed under the internal operator is its own same-operator
        // spelling; a side printed under the reversed operator is related to
        // the exact argument reversal of its printed text. Operand spellings
        // are left as printed: the positional `cong` repair below relates each
        // to its internal operand.
        let same_operator = |printed: &str| -> Option<(String, bool)> {
            if split_application(printed, &operator).is_some() {
                return Some((printed.to_string(), false));
            }
            let reversed = surface_order_reversal(printed)?;
            split_application(&reversed, &operator).map(|_| (reversed, true))
        };
        let (canonical_left, left_reversed) = same_operator(&printed_left)?;
        let (canonical_right, right_reversed) = same_operator(&printed_right)?;
        if !left_reversed && !right_reversed {
            return None;
        }
        let mut steps = Vec::new();
        let mut chain = Vec::new();
        if left_reversed {
            let norm = format!("{id}.norm_l");
            if !authored_assume::comparison_reversal_step(
                &norm,
                &printed_left,
                &canonical_left,
                authored_assume::EquivalenceDirection::SurfaceToCanonical,
                &mut steps,
            ) {
                return None;
            }
            chain.push(norm);
        }
        steps.extend(self.canonical_order_cong_steps(
            &format!("{id}.cong"),
            *left,
            *right,
            [&canonical_left, &canonical_right],
            premises,
        )?);
        chain.push(format!("{id}.cong"));
        if right_reversed {
            let norm = format!("{id}.norm_r");
            if !authored_assume::comparison_reversal_step(
                &norm,
                &printed_right,
                &canonical_right,
                authored_assume::EquivalenceDirection::CanonicalToSurface,
                &mut steps,
            ) {
                return None;
            }
            chain.push(norm);
        }
        steps.push(format!(
            "(step {id} (cl (= {printed_left} {printed_right})) :rule trans :premises ({}))",
            chain.join(" ")
        ));
        Some(steps.join("\n"))
    }
}

/// The one premise, when it is over the one differing argument pair's
/// INTERNAL endpoints and PRINTS as that printed pair in either orientation.
/// `cong` accepts a flipped premise, and an override may flip an equality's
/// printed orientation against its internal one (`mk_eq` orders arguments by
/// id, the override keeps the authored order), which the positional repair
/// below reads as two mismatched endpoints.
fn printed_as_differing_pair(
    application: &SurfaceCongruenceApplication,
    premise_rows: &[SurfaceCongruencePremise],
) -> Option<ProofId> {
    let [row] = premise_rows else {
        return None;
    };
    let mut differing = (0..application.left_args.len())
        .filter(|&index| application.left_args[index] != application.right_args[index]);
    let (Some(position), None) = (differing.next(), differing.next()) else {
        return None;
    };
    let (left, right) = (
        application.left_internal_args[position],
        application.right_internal_args[position],
    );
    let (left_text, right_text) = (
        &application.left_args[position],
        &application.right_args[position],
    );
    let internal =
        (row.left == left && row.right == right) || (row.left == right && row.right == left);
    let printed = (&row.printed_left == left_text && &row.printed_right == right_text)
        || (&row.printed_left == right_text && &row.printed_right == left_text);
    (internal && printed).then_some(row.id)
}

#[cfg(test)]
#[path = "order_tests.rs"]
mod tests;
