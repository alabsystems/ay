// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small structural helpers for the independently checked ∀∃ witness lane.

use super::{
    contains_quantifier, HashSet, Sort, TermData, TermId, TermStore,
    QUANTIFIED_GATE_MAX_WITNESS_BINDERS, QUANTIFIED_GATE_MAX_WITNESS_TUPLES,
};

/// Binder sorts the ∀∃ witness route accepts: fixed-interpretation domains
/// only, so a witness term means the same thing in every structure satisfying
/// the pins. Uninterpreted sorts stay with finite-universe expansion.
pub(super) fn quantified_gate_witness_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_))
}

/// Split the canonical guarded existential shape
/// `guard_disjuncts ∨ (exists vars. body)`.
///
/// [`TermStore::mk_implies`] canonicalizes `guard => rhs` to
/// `(or (not guard) rhs)`, and `mk_or` may reorder its arguments. Exactly one
/// branch may contain a quantifier; every other branch is retained verbatim in
/// the checked witness obligation. Multiple quantified branches decline so a
/// witness for one disjunct can never masquerade as a witness for another.
pub(super) fn quantified_gate_split_guarded_existential(
    terms: &TermStore,
    matrix: TermId,
) -> Option<(Vec<TermId>, TermId)> {
    let TermData::App(sym, args) = terms.get(matrix) else {
        return Some((Vec::new(), matrix));
    };
    if sym.name() != "or" {
        return Some((Vec::new(), matrix));
    }

    let mut quantified = None;
    let mut guards = Vec::new();
    for &arg in args {
        if contains_quantifier(terms, arg) {
            if quantified.replace(arg).is_some() {
                return None;
            }
        } else {
            guards.push(arg);
        }
    }
    quantified.map(|branch| (guards, branch))
}

/// Extract the polarity-normalized existential block and its quantifier-free
/// body from either a direct or a canonically guarded matrix.
pub(super) fn quantified_gate_extract_existential_block(
    terms: &mut TermStore,
    matrix: TermId,
) -> Option<(Vec<TermId>, Vec<(String, Sort)>, TermId)> {
    let (guards, mut cur) = quantified_gate_split_guarded_existential(terms, matrix)?;
    let mut binders = Vec::new();
    let mut universal = None;
    let mut positive = true;
    loop {
        match terms.get(cur).clone() {
            TermData::Not(inner) => {
                positive = !positive;
                cur = inner;
            }
            TermData::Forall(vars, body, _) => {
                if *universal.get_or_insert(positive) != positive {
                    break;
                }
                binders.extend(vars);
                cur = body;
            }
            TermData::Exists(vars, body, _) => {
                if *universal.get_or_insert(!positive) == positive {
                    break;
                }
                binders.extend(vars);
                cur = body;
            }
            _ => break,
        }
    }
    if universal != Some(false) {
        return None;
    }
    let body = if positive { cur } else { terms.mk_not(cur) };
    if contains_quantifier(terms, body)
        || binders.is_empty()
        || binders.len() > QUANTIFIED_GATE_MAX_WITNESS_BINDERS
        || !binders
            .iter()
            .all(|(_, sort)| quantified_gate_witness_sort(sort))
    {
        return None;
    }
    Some((guards, binders, body))
}

/// Rebuild the sufficient witness obligation for a guarded existential.
pub(super) fn quantified_gate_rebuild_guarded_witness(
    terms: &mut TermStore,
    guards: &[TermId],
    witnessed_body: TermId,
) -> TermId {
    if guards.is_empty() {
        return witnessed_body;
    }
    let mut disjuncts = guards.to_vec();
    disjuncts.push(witnessed_body);
    terms.mk_or(disjuncts)
}

/// Does `term` contain a `Var` named `name`? Used to reject a witness
/// candidate that mentions the existential binder it must eliminate.
/// Conservative: an over-budget walk answers `true` (candidate rejected).
pub(super) fn quantified_gate_mentions_var(terms: &TermStore, term: TermId, name: &str) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![term];
    let mut budget = 20_000usize;
    while let Some(t) = stack.pop() {
        if budget == 0 {
            return true;
        }
        budget -= 1;
        if !seen.insert(t) {
            continue;
        }
        if let TermData::Var(var, _) = terms.get(t) {
            if var == name {
                return true;
            }
        }
        stack.extend(terms.children(t));
    }
    false
}

/// Candidate witness tuples in strongest-first cartesian-product order.
pub(super) fn quantified_gate_witness_tuples(per_binder: &[Vec<TermId>]) -> Vec<Vec<TermId>> {
    let mut tuples: Vec<Vec<TermId>> = vec![Vec::new()];
    for candidates in per_binder {
        let mut next = Vec::new();
        for prefix in &tuples {
            for &candidate in candidates {
                let mut extended = prefix.clone();
                extended.push(candidate);
                next.push(extended);
            }
        }
        tuples = next;
    }
    tuples.truncate(QUANTIFIED_GATE_MAX_WITNESS_TUPLES);
    tuples
}
