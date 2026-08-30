// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural and printed-surface validation for generic Alethe resolution
//! annotations.

use super::AlethePrinter;
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Constant, ProofId, TermData, TermId, TermStore};

#[cfg(test)]
#[path = "alethe_printer_resolution_args_precedence_tests.rs"]
mod precedence_tests;

pub(super) fn is_generic_resolution(rule: &AletheRule) -> bool {
    matches!(rule, AletheRule::ThResolution | AletheRule::Resolution)
}

pub(super) fn validate_generic_resolution_args(
    terms: &TermStore,
    premise_count: usize,
    args: &[TermId],
) -> Result<(), String> {
    if args.is_empty() {
        return Ok(());
    }
    let Some(link_count) = premise_count.checked_sub(1).filter(|_| premise_count >= 2) else {
        return Err("annotated resolution requires at least two premises".to_string());
    };
    let Some(expected) = link_count.checked_mul(2) else {
        return Err("annotated resolution argument count overflowed".to_string());
    };
    if args.len() != expected {
        return Err(format!(
            "annotated resolution requires {expected} pivot/polarity arguments, found {}",
            args.len()
        ));
    }
    for (link, annotation) in args.chunks_exact(2).enumerate() {
        if !matches!(terms.get(annotation[1]), TermData::Const(Constant::Bool(_))) {
            return Err(format!(
                "annotated resolution polarity for link {link} must be true or false"
            ));
        }
    }
    Ok(())
}

/// Reject an internally valid annotation when surface syntax may change the
/// exact resolution literals or arguments that an external checker sees.
///
/// This runs only after the dedicated `distinct`/equality bridge has declined:
/// that bridge deliberately replaces a shape-changing annotated step with a
/// certified argument-free derivation. Generic annotated resolution has no
/// corresponding repair, so any active rendering override is refused. This
/// intentionally conservative O(1) gate also avoids recursively materializing
/// every canonical premise a second time outside the emission-work budget.
pub(super) fn validate_generic_resolution_surface(
    printer: &AlethePrinter<'_>,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
) -> Result<(), String> {
    if args.is_empty() {
        return Ok(());
    }

    if printer
        .term_overrides
        .is_some_and(|overrides| !overrides.is_empty())
        || !printer.skolem_overrides.borrow().is_empty()
        || !printer.let_bridge_renderings.borrow().is_empty()
    {
        return Err(
            "annotated resolution cannot be certified while effective surface overrides are active"
                .to_string(),
        );
    }

    let premise_clauses = printer.proof_clauses.borrow();
    validate_duplicate_free_directed_fold(printer.terms, clause, premises, args, &premise_clauses)
}

impl AlethePrinter<'_> {
    /// Print a derived literal after any certified `let` bridge. Assumptions
    /// bypass this path and remain source-exact.
    ///
    /// A certified rendering for the outer literal (a Skolem rewrite or its
    /// own direct `let` bridge) keeps `write_term_into`'s normal precedence.
    /// Otherwise, only an explicit `Not(inner)` needs repair: a derived
    /// positive `inner` already follows the ordinary bridge lookup there. A
    /// raw outer term override is intentionally bypassed because it is source
    /// spelling, not an independently certified derived-literal rendering.
    ///
    /// De Morgan and other complement-normalized roots are deliberately not
    /// inferred here. They remain distinct Alethe atoms and must use a
    /// dedicated checked bridge, or the resolution checker rejects them.
    pub(super) fn write_derived_literal_into(&self, out: &mut String, term_id: TermId) {
        if self.work_budget_exhausted() {
            self.write_term_into(out, term_id);
            return;
        }
        let has_certified_outer_rendering = self.skolem_overrides.borrow().contains_key(&term_id)
            || self.let_bridge_renderings.borrow().contains_key(&term_id);
        if has_certified_outer_rendering {
            self.write_term_into(out, term_id);
            return;
        }
        if let TermData::Not(inner) = self.terms.get(term_id) {
            if let Some(eliminated) = self.let_bridge_renderings.borrow().get(inner).cloned() {
                self.charge((eliminated.len() + "(not )".len()) as u64);
                out.push_str("(not ");
                out.push_str(&eliminated);
                out.push(')');
                return;
            }
        }
        self.write_term_into(out, term_id);
    }
}

/// Match the occurrence-sensitive subset accepted by AY's native explicit
/// resolution checker. Carcara consumes one directed pivot occurrence from a
/// raw clause. Silently treating clauses as sets would therefore erase a
/// repeated pivot, a repeated residual literal, or a residual shared by both
/// sides while the emitted resolvent still contains both occurrences.
fn validate_duplicate_free_directed_fold(
    terms: &TermStore,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
    premise_clauses: &DetHashMap<ProofId, Vec<TermId>>,
) -> Result<(), String> {
    let first_id = premises
        .first()
        .ok_or_else(|| "annotated resolution has no first premise".to_string())?;
    let first = premise_clauses
        .get(first_id)
        .ok_or_else(|| "annotated resolution first premise has no printable clause".to_string())?;
    let mut accumulator = unique_exact_clause(terms, first, "first premise")?;

    for (link, (&next_id, annotation)) in premises[1..].iter().zip(args.chunks_exact(2)).enumerate()
    {
        let next = premise_clauses.get(&next_id).ok_or_else(|| {
            format!(
                "annotated resolution next premise {} has no printable clause",
                link + 1
            )
        })?;
        let next = unique_exact_clause(terms, next, &format!("premise {}", link + 1))?;
        let TermData::Const(Constant::Bool(polarity)) = terms.get(annotation[1]) else {
            return Err(format!(
                "annotated resolution polarity for link {link} must be true or false"
            ));
        };
        let pivot = decode_exact_literal(terms, annotation[0])
            .ok_or_else(|| "annotated resolution pivot depth overflowed".to_string())?;
        let negated_pivot = (
            pivot.0,
            pivot
                .1
                .checked_add(1)
                .ok_or_else(|| "annotated resolution pivot depth overflowed".to_string())?,
        );
        let (current_pivot, next_pivot) = if *polarity {
            (pivot, negated_pivot)
        } else {
            (negated_pivot, pivot)
        };
        if accumulator.binary_search(&current_pivot).is_err()
            || next.binary_search(&next_pivot).is_err()
        {
            return Err(format!(
                "annotated resolution pivot for link {link} is absent from a directed premise"
            ));
        }

        let mut resolvent: Vec<(TermId, usize)> = accumulator
            .iter()
            .copied()
            .filter(|literal| *literal != current_pivot)
            .chain(
                next.iter()
                    .copied()
                    .filter(|literal| *literal != next_pivot),
            )
            .collect();
        resolvent.sort_unstable();
        if resolvent.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(format!(
                "annotated resolution residual for link {link} contains a duplicate literal"
            ));
        }
        accumulator = resolvent;
    }

    let conclusion = unique_exact_clause(terms, clause, "conclusion")?;
    if accumulator != conclusion {
        return Err(
            "annotated resolution conclusion is not the exact directed resolvent".to_string(),
        );
    }
    Ok(())
}

fn unique_exact_clause(
    terms: &TermStore,
    clause: &[TermId],
    location: &str,
) -> Result<Vec<(TermId, usize)>, String> {
    let mut literals: Vec<(TermId, usize)> = clause
        .iter()
        .map(|&literal| {
            decode_exact_literal(terms, literal)
                .ok_or_else(|| "annotated resolution literal depth overflowed".to_string())
        })
        .collect::<Result<_, _>>()?;
    literals.sort_unstable();
    if literals.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(format!(
            "annotated resolution {location} contains a duplicate literal"
        ));
    }
    Ok(literals)
}

fn decode_exact_literal(terms: &TermStore, mut literal: TermId) -> Option<(TermId, usize)> {
    let mut negation_depth = 0usize;
    while let TermData::Not(inner) = terms.get(literal) {
        literal = *inner;
        negation_depth = negation_depth.checked_add(1)?;
    }
    Some((literal, negation_depth))
}
