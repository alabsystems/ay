// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reading a congruence-explanation clause, and the small term/clause
//! primitives the emitter needs.
//!
//! Split out of `congruence_derivation` so each file stays inside the
//! repository's per-file line ceiling.

use ay_core::{Symbol, TermData, TermId, TermStore};

/// One hypothesis of the clause: a literal `(not (= lhs rhs))`.
pub(super) struct Hypothesis {
    pub(super) literal: TermId,
    pub(super) lhs: TermId,
    pub(super) rhs: TermId,
}

/// A derived or stated equality, and how a consumer clause carries it.
#[derive(Clone)]
pub(super) enum Fact {
    /// Stated by a hypothesis: the clause already carries its negation, so no
    /// step and no resolution is needed.
    Stated { literal: TermId },
    /// Derived by `steps[step]`, whose clause is `clause` with `positive`
    /// last.
    Derived {
        step: usize,
        positive: TermId,
        negative: TermId,
        clause: Vec<TermId>,
    },
}

impl Fact {
    /// The literal a consumer clause carries for this fact: the NEGATED
    /// equality, exactly as recorded for a hypothesis.
    pub(super) fn literal(&self) -> TermId {
        match self {
            Self::Stated { literal }
            | Self::Derived {
                negative: literal, ..
            } => *literal,
        }
    }
}

/// Decode a term as an equality `(= lhs rhs)`.
pub(super) fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// The resolvent of `left` and `right` on `pivot_positive`, as a deduplicated
/// literal sequence. `pivot_negative` is dropped from `left` and
/// `pivot_positive` from `right` — the asymmetry matters, because a
/// hypothesis literal the right-hand derivation also carries must SURVIVE.
pub(super) fn resolvent(
    left: &[TermId],
    right: &[TermId],
    pivot_positive: TermId,
    pivot_negative: TermId,
) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::with_capacity(left.len() + right.len());
    for &literal in left {
        if literal != pivot_negative && !out.contains(&literal) {
            out.push(literal);
        }
    }
    for &literal in right {
        if literal != pivot_positive && !out.contains(&literal) {
            out.push(literal);
        }
    }
    out
}

/// Split the clause into its hypotheses and its single positive equality.
///
/// The POLARITY split is the load-bearing part of the schema and mirrors the
/// validator's: a hypothesis is read from a NEGATED equality only. Unlike the
/// validator this reads exactly ONE `Not` wrapper, so `(not (not (= a b)))` is
/// declined rather than treated as a positive literal — the stricter, and
/// therefore fail-closed, direction.
pub(super) fn parse_clause(
    terms: &TermStore,
    literals: &[TermId],
) -> Option<(Vec<Hypothesis>, TermId, TermId, TermId)> {
    if literals.len() < 2 {
        return None;
    }
    // A repeated literal would make the reordering step's multiset check fail
    // and could make an `eq_transitive` premise redundant; decline instead.
    for (position, literal) in literals.iter().enumerate() {
        if literals[..position].contains(literal) {
            return None;
        }
    }
    let mut hypotheses = Vec::with_capacity(literals.len());
    let mut goal: Option<(TermId, TermId, TermId)> = None;
    for &literal in literals {
        match terms.get(literal) {
            TermData::Not(inner) => {
                let (lhs, rhs) = decode_eq(terms, *inner)?;
                hypotheses.push(Hypothesis { literal, lhs, rhs });
            }
            _ => {
                let (lhs, rhs) = decode_eq(terms, literal)?;
                if goal.replace((literal, lhs, rhs)).is_some() {
                    return None;
                }
            }
        }
    }
    let (goal_literal, goal_lhs, goal_rhs) = goal?;
    if hypotheses.is_empty() {
        return None;
    }
    Some((hypotheses, goal_literal, goal_lhs, goal_rhs))
}

/// The symbol and arguments of an application node.
pub(super) fn as_application(terms: &TermStore, term: TermId) -> Option<(Symbol, Vec<TermId>)> {
    match terms.get(term) {
        TermData::App(symbol, args) => Some((symbol.clone(), args.clone())),
        _ => None,
    }
}
