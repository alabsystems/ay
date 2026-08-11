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
