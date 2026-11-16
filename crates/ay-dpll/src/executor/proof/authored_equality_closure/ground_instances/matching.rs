// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binder tuples for the instance-seeded closure: ground applications of the
//! authored roots (outside every binder) matched against the applications of
//! a universal's body. Pure hints: `validate_forall_inst_with_progress` re-derives every
//! substitution the closure emits.

use super::*;

/// Ground applications of the authored leaves, first-seen order, never
/// entering a binder (so no proposal can mention a bound variable).
pub(super) fn harvest_ground_applications(
    terms: &TermStore,
    leaves: &[AuthoredLeaf],
    work: &mut usize,
) -> Vec<TermId> {
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut applications = Vec::new();
    let mut stack: Vec<TermId> = leaves.iter().rev().map(|leaf| leaf.term).collect();
    while let Some(term) = stack.pop() {
        if *work >= MAX_MATCH_WORK || applications.len() >= MAX_GROUND_TERMS {
            break;
        }
        *work += 1;
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.extend([*else_branch, *then_branch, *condition]);
            }
            TermData::App(_, args) => {
                applications.push(term);
                stack.extend(args.iter().rev().copied());
            }
            _ => {}
        }
    }
    applications
}

/// Complete binder tuples obtained by matching one application of `body` that
/// mentions a binder against one harvested ground application. Deduplicated,
/// in discovery order.
pub(super) fn binder_tuples(
    terms: &TermStore,
    names: &[String],
    body: TermId,
    ground: &[TermId],
    work: &mut usize,
) -> Vec<Vec<TermId>> {
    let mut patterns = Vec::new();
    collect_patterns(terms, names, body, &mut patterns, work);
    let mut tuples: Vec<Vec<TermId>> = Vec::new();
    for &pattern in &patterns {
        for &candidate in ground {
            if *work >= MAX_MATCH_WORK || tuples.len() >= MAX_INSTANCES {
                return tuples;
            }
            let mut slots = vec![None; names.len()];
            if !match_pattern(terms, names, pattern, candidate, &mut slots, work) {
                continue;
            }
            let Some(values) = slots.into_iter().collect::<Option<Vec<_>>>() else {
                continue;
            };
            if !tuples.contains(&values) {
                tuples.push(values);
            }
        }
    }
    tuples
}

/// Non-connective applications of `term` that mention a binder, outermost
/// first.
fn collect_patterns(
    terms: &TermStore,
    names: &[String],
    term: TermId,
    out: &mut Vec<TermId>,
    work: &mut usize,
) -> bool {
    *work += 1;
    if *work >= MAX_MATCH_WORK {
        return false;
    }
    match terms.get(term) {
        TermData::Var(name, _) => names.contains(name),
        TermData::Not(inner) => collect_patterns(terms, names, *inner, out, work),
        TermData::App(symbol, args) => {
            let connective = matches!(symbol, Symbol::Named(name)
                if matches!(name.as_str(), "or" | "and" | "=>" | "not" | "="));
            let at = out.len();
            let mut mentions = false;
            for &arg in args {
                mentions |= collect_patterns(terms, names, arg, out, work);
            }
            if mentions && !connective && !out.contains(&term) {
                out.insert(at, term);
            }
            mentions
        }
        _ => false,
    }
}

/// Structural match of `pattern` against the ground `candidate`, binding the
/// named binders into `slots`. Binder-free subterms must be the same term.
fn match_pattern(
    terms: &TermStore,
    names: &[String],
    pattern: TermId,
    candidate: TermId,
    slots: &mut [Option<TermId>],
    work: &mut usize,
) -> bool {
    *work += 1;
    if *work >= MAX_MATCH_WORK {
        return false;
    }
    if pattern == candidate {
        return true;
    }
    if terms.sort(pattern) != terms.sort(candidate) {
        return false;
    }
    match (terms.get(pattern), terms.get(candidate)) {
        (TermData::Var(name, _), _) => {
            let Some(slot) = names.iter().position(|binder| binder == name) else {
                return false;
            };
            match slots[slot] {
                Some(bound) => bound == candidate,
                None => {
                    slots[slot] = Some(candidate);
                    true
                }
            }
        }
        (TermData::App(pattern_symbol, pattern_args), TermData::App(symbol, args)) => {
            pattern_symbol == symbol
                && pattern_args.len() == args.len()
                && pattern_args
                    .iter()
                    .zip(args)
                    .all(|(&p, &c)| match_pattern(terms, names, p, c, slots, work))
        }
        (TermData::Not(pattern_inner), TermData::Not(inner)) => {
            match_pattern(terms, names, *pattern_inner, *inner, slots, work)
        }
        _ => false,
    }
}
