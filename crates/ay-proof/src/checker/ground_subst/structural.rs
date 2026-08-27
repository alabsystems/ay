// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FIRST ACCEPTANCE LEG — the purely STRUCTURAL recognizer: the occurrence
//! scan and the exact parallel walk of `P` against `Q` under the substitution
//! map. Nothing here folds, canonicalizes, or interprets any operator: a node
//! pair the map does not explain is a rejection, never a candidate for
//! further reasoning. Everything that reads meaning into a symbol lives in
//! the sibling `normalize` module, which the validator consults only after
//! this leg has refused.

use ay_core::kani_compat::DetHashMap;
use ay_core::{TermData, TermId, TermStore};

/// Whether `term` is a closed literal constant.
pub(super) fn is_literal_constant(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Const(_))
}

/// Whether any mapped key occurs in `term` (quantifier-free walk; a binder
/// makes the answer "reject" by reporting an occurrence-like failure at the
/// caller via the `saw_binder` flag).
pub(super) fn key_occurs_or_binder(
    terms: &TermStore,
    term: TermId,
    map: &DetHashMap<TermId, TermId>,
    budget: &mut usize,
) -> Result<bool, ()> {
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if *budget == 0 {
            return Err(());
        }
        *budget -= 1;
        if map.contains_key(&current) {
            return Ok(true);
        }
        match terms.get(current) {
            TermData::Const(_) | TermData::Var(..) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            // Binders, unexpanded lets, and any future node kind make
            // substitution non-structural; treat them as an occurrence so the
            // caller rejects (fail-closed).
            _ => return Ok(true),
        }
    }
    Ok(false)
}

/// The parallel walk: `q` must be exactly `p` with every mapped-key
/// occurrence replaced by its value.
pub(super) fn substituted_exactly(
    terms: &TermStore,
    p: TermId,
    q: TermId,
    map: &DetHashMap<TermId, TermId>,
    budget: &mut usize,
) -> Result<bool, ()> {
    let mut stack = vec![(p, q)];
    while let Some((p, q)) = stack.pop() {
        if *budget == 0 {
            return Err(());
        }
        *budget -= 1;
        if let Some(&value) = map.get(&p) {
            // Every occurrence of a mapped key must have been replaced.
            if q != value {
                return Ok(false);
            }
            continue;
        }
        if p == q {
            // Equal-and-unmapped is only exact when no mapped key hides
            // below (all occurrences must be replaced simultaneously).
            match key_occurs_or_binder(terms, p, map, budget) {
                Ok(false) => continue,
                Ok(true) => return Ok(false),
                Err(()) => return Err(()),
            }
        }
        match (terms.get(p), terms.get(q)) {
            (TermData::App(sp, ap), TermData::App(sq, aq)) => {
                if sp != sq || ap.len() != aq.len() {
                    return Ok(false);
                }
                stack.extend(ap.iter().copied().zip(aq.iter().copied()));
            }
            (TermData::Not(ip), TermData::Not(iq)) => stack.push((*ip, *iq)),
            (TermData::Ite(cp, tp, ep), TermData::Ite(cq, tq, eq_)) => {
                stack.push((*cp, *cq));
                stack.push((*tp, *tq));
                stack.push((*ep, *eq_));
            }
            // Distinct leaves the map does not explain, or any binder/let:
            // not an exact substitution image.
            _ => return Ok(false),
        }
    }
    Ok(true)
}
