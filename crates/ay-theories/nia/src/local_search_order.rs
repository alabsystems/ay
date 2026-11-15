// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Decide whether exact arithmetic refinement can precede whole-formula SLS.

use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::Sort;

use crate::NiaSolver;

const MAX_SKELETON_WORK: usize = 4_096;

#[derive(Clone, Copy)]
pub(super) enum FirstOffer {
    WholeFormulaSearch,
    RefineUnits,
}

#[derive(Clone, Copy)]
enum Polarity {
    Positive,
    Negative,
}

impl Polarity {
    fn opposite(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

#[derive(Clone, Copy)]
enum Visit {
    Formula(TermId, Polarity),
    Integer(TermId),
}

fn append(
    pending: &mut Vec<Visit>,
    args: &[TermId],
    remaining: usize,
    visit: impl Fn(TermId) -> Visit,
) -> bool {
    if args.len() > remaining.saturating_sub(pending.len()) {
        return false;
    }
    pending.extend(args.iter().rev().copied().map(visit));
    true
}

impl NiaSolver<'_> {
    /// Inspect source syntax before arithmetic purification adds Boolean
    /// alternatives. Only scheduling is retained; SLS still searches and
    /// verifies every working root installed by `set_root_assertions`.
    /// Replacing those roots clears this source-shape preference.
    pub fn set_local_search_source_roots(&mut self, roots: &[TermId]) {
        self.local_search_first_offer = Some(if self.integer_unit_conjunction(roots) {
            FirstOffer::RefineUnits
        } else {
            FirstOffer::WholeFormulaSearch
        });
    }

    /// A completed, bounded syntax check only changes scheduling. It never
    /// supplies a conflict, model, proof premise, or assertion authority.
    pub(crate) fn root_assertions_are_integer_unit_conjunction(&self) -> bool {
        match self.local_search_first_offer {
            Some(FirstOffer::RefineUnits) => true,
            Some(FirstOffer::WholeFormulaSearch) => false,
            None => self.integer_unit_conjunction(&self.root_assertions),
        }
    }

    fn integer_unit_conjunction(&self, roots: &[TermId]) -> bool {
        scan_integer_unit_conjunction(self.terms, roots, || self.should_timeout())
    }
}

/// Whether a completed, bounded scan finds only integer arithmetic units.
///
/// This is a scheduling hint, not evidence about satisfiability or assertion
/// authority. Boolean alternatives, unsupported terms, an incomplete scan or
/// a live check stop return false. No solver state or term is created.
pub fn is_integer_unit_conjunction(terms: &TermStore, roots: &[TermId]) -> bool {
    scan_integer_unit_conjunction(terms, roots, ay_core::resource::check_stop_requested)
}

fn scan_integer_unit_conjunction(
    terms: &TermStore,
    roots: &[TermId],
    should_stop: impl Fn() -> bool,
) -> bool {
    if roots.is_empty() || roots.len() > MAX_SKELETON_WORK {
        return false;
    }
    let mut pending: Vec<_> = roots
        .iter()
        .rev()
        .map(|&term| Visit::Formula(term, Polarity::Positive))
        .collect();
    let mut remaining = MAX_SKELETON_WORK;
    while let Some(visit) = pending.pop() {
        if remaining == 0 || should_stop() {
            return false;
        }
        remaining -= 1;
        let admitted = match visit {
            Visit::Formula(term, polarity) => match terms.get(term) {
                TermData::Const(Constant::Bool(_)) => true,
                TermData::Not(inner) => append(&mut pending, &[*inner], remaining, |term| {
                    Visit::Formula(term, polarity.opposite())
                }),
                TermData::App(symbol, args) => match (symbol.name(), polarity) {
                    ("and", Polarity::Positive) | ("or", Polarity::Negative) => {
                        append(&mut pending, args, remaining, |term| {
                            Visit::Formula(term, polarity)
                        })
                    }
                    ("=" | "<" | "<=" | ">" | ">=", _) if args.len() == 2 => {
                        append(&mut pending, args, remaining, Visit::Integer)
                    }
                    _ => false,
                },
                _ => false,
            },
            Visit::Integer(term) if terms.sort(term) == &Sort::Int => match terms.get(term) {
                TermData::Const(Constant::Int(_)) | TermData::Var(_, _) => true,
                TermData::App(symbol, args)
                    if matches!(symbol.name(), "+" | "-" | "*" | "div" | "mod" | "abs") =>
                {
                    append(&mut pending, args, remaining, Visit::Integer)
                }
                _ => false,
            },
            Visit::Integer(_) => false,
        };
        if !admitted {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests;
