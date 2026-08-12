// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear, surface-safe rendering of flat Boolean `and_pos` steps.

use super::{
    split_alethe_application_bounded, AlethePrintError, AlethePrinter, AletheSurfaceParseError,
};
use ay_core::{AletheRule, ProofId, Sort, Symbol, TermData, TermId};

impl AlethePrinter<'_> {
    /// Render one exact, premise-free Boolean `and_pos` against its effective
    /// flat surface source. Specialized implication/De-Morgan bridges run
    /// before this method; once an ordinary flat AND reaches this boundary it
    /// either emits a spec-valid projection or fails closed.
    pub(super) fn format_flat_surface_and_pos(
        &self,
        id: ProofId,
        rule: &AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<Option<String>, AlethePrintError> {
        let AletheRule::AndPos(internal_index) = rule else {
            return Ok(None);
        };
        if !premises.is_empty() {
            return Err(invalid_and_pos(id, "and_pos requires no premises"));
        }
        let [left, right] = clause else {
            return Err(invalid_and_pos(
                id,
                "and_pos clause must contain exactly the raw gate and indexed conjunct",
            ));
        };
        // Native strict checking uses the first internal argument only when it
        // is an AND source and historically ignores trailing bookkeeping
        // arguments. When it is absent or non-AND, recover the unique exact
        // raw `not(and ..)` gate whose indexed child is the other literal.
        let source = args
            .first()
            .copied()
            .filter(|&source| {
                matches!(
                    self.terms.get(source),
                    TermData::App(Symbol::Named(head), _) if head == "and"
                )
            })
            .or_else(|| infer_raw_and_source(self, [*left, *right], *internal_index))
            .ok_or_else(|| invalid_and_pos(id, "and_pos raw source is not uniquely inferable"))?;
        let (selected, canonical_arity) = {
            let TermData::App(Symbol::Named(head), conjuncts) = self.terms.get(source) else {
                return Err(invalid_and_pos(id, "and_pos source is not an application"));
            };
            if head != "and" || *self.terms.sort(source) != Sort::Bool || conjuncts.len() < 2 {
                return Err(invalid_and_pos(
                    id,
                    "and_pos source is not a flat Boolean and-term",
                ));
            }
            (
                conjuncts
                    .get(*internal_index as usize)
                    .copied()
                    .ok_or_else(|| {
                        invalid_and_pos(id, "and_pos canonical index is out of range")
                    })?,
                conjuncts.len(),
            )
        };
        self.charge(canonical_arity as u64);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        let TermData::App(_, conjuncts) = self.terms.get(source) else {
            return Err(invalid_and_pos(
                id,
                "and_pos source changed during validation",
            ));
        };
        if conjuncts
            .iter()
            .any(|&conjunct| *self.terms.sort(conjunct) != Sort::Bool)
        {
            return Err(invalid_and_pos(
                id,
                "and_pos source contains a non-Boolean conjunct",
            ));
        }
        let left_is_gate =
            matches!(self.terms.get(*left), TermData::Not(inner) if *inner == source);
        let right_is_gate =
            matches!(self.terms.get(*right), TermData::Not(inner) if *inner == source);
        let (gate_position, selected_position) = if left_is_gate && *right == selected {
            (0usize, 1usize)
        } else if right_is_gate && *left == selected {
            (1usize, 0usize)
        } else {
            return Err(invalid_and_pos(
                id,
                "and_pos native clause is not the exact raw gate/indexed-conjunct pair",
            ));
        };

        let source_surface = self.format_term(source);
        let printed = [self.format_term(*left), self.format_term(*right)];
        // One source scan, one comparison against each borrowed immediate
        // operand, and the eventual one-step output are all linear in these
        // already-rendered strings. Charge before the scanner allocates its
        // capped slice vector or `(not source)` is assembled.
        let source_bytes = source_surface.len() as u64;
        let clause_bytes = printed
            .iter()
            .map(|literal| literal.len() as u64)
            .sum::<u64>();
        self.charge(
            source_bytes
                .saturating_mul(3)
                .saturating_add(clause_bytes.saturating_mul(2)),
        );
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }

        let surface_operands = match split_alethe_application_bounded(
            &source_surface,
            "and",
            source_surface.len(),
            source_surface.len(),
        ) {
            Ok(operands) if operands.len() >= 2 => operands,
            Ok(_) | Err(AletheSurfaceParseError::Malformed) => {
                return Err(invalid_and_pos(
                    id,
                    "and_pos effective source is not a flat and-term",
                ));
            }
            Err(AletheSurfaceParseError::BudgetExceeded) => {
                return Err(invalid_and_pos(
                    id,
                    "and_pos effective source exceeds its input-derived scan bound",
                ));
            }
        };
        let expected_gate = format!("(not {source_surface})");
        if printed[gate_position] != expected_gate {
            return Err(invalid_and_pos(
                id,
                "and_pos printed gate is not the exact negation of its effective source",
            ));
        }
        let selected_surface = &printed[selected_position];
        let Some(surface_index) = surface_operands
            .iter()
            .position(|operand| *operand == selected_surface)
        else {
            // The indexed conjunct is not a TOP-LEVEL printed operand. Two
            // certified printed-shape divergences can still be bridged with
            // spec-valid steps over the exact printed spellings; anything
            // else keeps failing closed below.
            //
            // (1) The surface override re-nests AY's flat internal
            //     conjunction (the authored grouping), leaving the conjunct a
            //     DEEPER printed operand: derive the traced clause through
            //     the printed nesting — one genuine `and_pos` per hop plus a
            //     final resolution (shared navigator; declines on flat
            //     prints, missing operands, and budget exhaustion).
            if let Some(text) = self.navigate_and_pos_gate(id, &source_surface, selected_surface) {
                return Ok(Some(text));
            }
            if self.work_budget_exhausted() {
                return Err(self.work_budget_error(id.0));
            }
            // (2) The surface FLATTENS an authored nested conjunct, erasing
            //     the indexed and-term from the top-level operand list:
            //     project each of its printed children off the flat surface
            //     and reassemble the conjunct via `and_neg` + resolution.
            if let Some(text) = self.reassemble_flattened_and_pos_conjunct(
                id,
                &expected_gate,
                selected_surface,
                &surface_operands,
            ) {
                return Ok(Some(text));
            }
            if self.work_budget_exhausted() {
                return Err(self.work_budget_error(id.0));
            }
            return Err(invalid_and_pos(
                id,
                "and_pos indexed conjunct is absent from its effective source",
            ));
        };

        // The ordinary printer is already exact only when both the wire index
        // and literal order agree. Otherwise emit one corrected, spec-shaped
        // tautology under the same proof id; no positional candidate fanout is
        // needed, even when identical operands occur more than once.
        if surface_index == *internal_index as usize && gate_position == 0 && selected_position == 1
        {
            return Ok(None);
        }
        Ok(Some(format!(
            "(step {id} (cl {expected_gate} {selected_surface}) :rule and_pos :args ({surface_index}))"
        )))
    }

    /// Bridge an `and_pos` whose indexed conjunct is an and-term ERASED from
    /// the printed source by surface flattening: internally the source is
    /// `(and A (and B C D))` but the effective surface prints `(and A B C D)`,
    /// so the selected conjunct `(and B C D)` is no printed operand at all.
    ///
    /// Every printed child of the selected conjunct is projected off the flat
    /// surface with a genuine `and_pos`, the conjunct is reassembled with the
    /// spec `and_neg` tautology, and one resolution restores the exact traced
    /// clause (carcara resolves with implicit factoring of the repeated gate
    /// literal — validated externally):
    ///
    /// ```text
    /// (step tK.f0 (cl (not (and A B C D)) B) :rule and_pos :args (1))
    /// (step tK.f1 (cl (not (and A B C D)) C) :rule and_pos :args (2))
    /// (step tK.f2 (cl (not (and A B C D)) D) :rule and_pos :args (3))
    /// (step tK.fa (cl (and B C D) (not B) (not C) (not D)) :rule and_neg)
    /// (step tK (cl (not (and A B C D)) (and B C D))
    ///     :rule resolution :premises (tK.fa tK.f0 tK.f1 tK.f2))
    /// ```
    ///
    /// Declines (`None`, caller fails loud) unless EVERY printed child of the
    /// selected conjunct is byte-identical to a top-level printed operand of
    /// the flat surface — an unbridgeable spelling must never guess.
    fn reassemble_flattened_and_pos_conjunct(
        &self,
        id: ProofId,
        expected_gate: &str,
        selected_surface: &str,
        surface_operands: &[&str],
    ) -> Option<String> {
        // One bounded scan of the selected conjunct plus one search over the
        // already-split surface operands per child; charge before allocating.
        self.charge((selected_surface.len() as u64).saturating_mul(3));
        if self.work_budget_exhausted() {
            return None;
        }
        let children = match split_alethe_application_bounded(
            selected_surface,
            "and",
            selected_surface.len(),
            selected_surface.len(),
        ) {
            Ok(children) if children.len() >= 2 => children,
            Ok(_) | Err(_) => return None,
        };
        let surface_bytes = surface_operands
            .iter()
            .map(|operand| operand.len() as u64)
            .sum::<u64>();
        self.charge(surface_bytes.saturating_mul(children.len() as u64));
        if self.work_budget_exhausted() {
            return None;
        }
        let mut projections = Vec::with_capacity(children.len());
        for child in &children {
            let index = surface_operands
                .iter()
                .position(|operand| operand == child)?;
            projections.push(index);
        }

        let mut out = String::new();
        let mut premises = vec![format!("{id}.fa")];
        for (hop, (child, index)) in children.iter().zip(&projections).enumerate() {
            let child_id = format!("{id}.f{hop}");
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {child_id} (cl {expected_gate} {child}) :rule and_pos :args ({index}))\n"
                ),
            );
            premises.push(child_id);
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!("(step {id}.fa (cl {selected_surface}"),
        );
        for child in &children {
            let _ = std::fmt::Write::write_fmt(&mut out, format_args!(" (not {child})"));
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                ") :rule and_neg)\n(step {id} (cl {expected_gate} {selected_surface}) \
                 :rule resolution :premises ({}))",
                premises.join(" ")
            ),
        );
        Some(out)
    }
}

fn infer_raw_and_source(
    printer: &AlethePrinter<'_>,
    clause: [TermId; 2],
    index: u32,
) -> Option<TermId> {
    // Mirror native `decode_and_source`: without an explicit source, a direct
    // positive AND literal takes precedence over a negated gate. Such a clause
    // is not the exact raw-gate/indexed-child shape this fallback authenticates.
    if clause.iter().any(|&literal| {
        matches!(
            printer.terms.get(literal),
            TermData::App(Symbol::Named(head), _) if head == "and"
        )
    }) {
        return None;
    }
    let mut source = None;
    for gate_position in 0..2 {
        let TermData::Not(candidate) = printer.terms.get(clause[gate_position]) else {
            continue;
        };
        let TermData::App(Symbol::Named(head), conjuncts) = printer.terms.get(*candidate) else {
            continue;
        };
        if head == "and"
            && conjuncts.get(index as usize) == Some(&clause[1 - gate_position])
            && source.replace(*candidate).is_some()
        {
            return None;
        }
    }
    source
}

fn invalid_and_pos(id: ProofId, reason: impl Into<String>) -> AlethePrintError {
    AlethePrintError::InvalidSurfaceStep {
        id,
        reason: reason.into(),
    }
}
