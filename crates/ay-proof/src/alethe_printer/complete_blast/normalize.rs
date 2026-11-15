// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An input clause that prints a literal under more than one `not`, or one
//! literal twice, re-derived ONCE in a form every chain can use in one n-ary
//! `:args` step.
//!
//! ## Why this exists
//!
//! The circuits print doubled negations where the `bitblast_*` rules demand
//! them, and the consumer's `:args` resolution reads a literal by its
//! negation COUNT (see `PrintedClause::count_safe`). A chain with such a
//! premise therefore fell back to binary steps that print every intermediate
//! clause — measured 2026-09-28 on the swept 64-bit divider (`x / 2 = x >> 1`):
//! 470,630 binary steps, 68.6 MB of a 91 MB document, against 49,221 n-ary
//! ones.
//!
//! ## What is printed
//!
//! For each literal `¬ⁿg` with `n ≥ 2`, Alethe's own tautology and one
//! parity-path resolution remove two negations:
//!
//! ```text
//! (step t (cl (not (not (not φ))) φ) :rule not_not)          ; φ = ¬ⁿ⁻²g
//! (step s (cl … φ …) :rule resolution :premises (c t))
//! ```
//!
//! and `contraction` drops a repeated literal. The pivot is the only literal
//! on `g` in the clause (a clause mentioning `g` twice is left alone), so the
//! parity path has exactly one complementary pair to resolve. The chains read
//! the SAME clause as before — only its spelling is normalized.

use super::circuit::SRef;
use super::*;
use std::fmt::Write as _;

impl Blaster<'_, '_> {
    /// Print the steps that re-derive the input clause `lits`, concluded by
    /// `name`, with every literal under at most one `not` and none repeated;
    /// the name of the last step and the literals it prints, in printed
    /// order. `None` leaves the clause as it is: already safe, a tautology, or
    /// a literal whose gate appears twice.
    pub(super) fn print_normalized_premise(
        &self,
        body: &mut String,
        name: &str,
        index: usize,
        lits: &[SRef],
    ) -> Option<(String, Vec<SRef>)> {
        let mut current: Vec<SRef> = lits.to_vec();
        let mut current_name = name.to_string();
        let mut step = 0_usize;
        while let Some(position) = current.iter().position(|literal| literal.nots >= 2) {
            let literal = current[position];
            let other_on_gate = current
                .iter()
                .enumerate()
                .any(|(at, other)| at != position && other.gate == literal.gate);
            if other_on_gate {
                return None;
            }
            let reduced = SRef {
                gate: literal.gate,
                nots: literal.nots - 2,
            };
            let triple = SRef {
                gate: literal.gate,
                nots: literal.nots.checked_add(1)?,
            };
            let tautology = format!("{}.cbbn{index}.{step}t", self.id);
            let _ = writeln!(
                body,
                "(step {tautology} (cl {} {}) :rule not_not)",
                self.circuit.text(triple),
                self.circuit.text(reduced)
            );
            current[position] = reduced;
            let next = format!("{}.cbbn{index}.{step}", self.id);
            let _ = writeln!(
                body,
                "(step {next} {} :rule resolution :premises ({current_name} {tautology}))",
                self.clause_text(&current)
            );
            current_name = next;
            step += 1;
        }
        let mut distinct: Vec<SRef> = Vec::with_capacity(current.len());
        for literal in &current {
            if distinct
                .iter()
                .any(|seen| seen.gate == literal.gate && seen.nots != literal.nots)
            {
                // Both polarities of one gate: a tautology no chain resolves.
                return None;
            }
            if !distinct.contains(literal) {
                distinct.push(*literal);
            }
        }
        if distinct.len() < current.len() {
            let next = format!("{}.cbbn{index}.c", self.id);
            let _ = writeln!(
                body,
                "(step {next} {} :rule contraction :premises ({current_name}))",
                self.clause_text(&distinct)
            );
            current_name = next;
        }
        (current_name != name).then_some((current_name, distinct))
    }
}
