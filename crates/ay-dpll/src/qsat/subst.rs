// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Substitution over the engine's quantifier-free terms, plain and with
//! Boolean/numeral constant folding.

use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

/// Replace variables by terms (no binders below: engine terms are
/// quantifier-free).
pub(crate) fn substitute(terms: &mut TermStore, t: TermId, map: &[(TermId, TermId)]) -> TermId {
    if map.is_empty() {
        return t;
    }
    let mut memo = ay_core::kani_compat::DetHashMap::default();
    subst_rec(terms, t, map, &mut memo)
}

fn subst_rec(
    terms: &mut TermStore,
    t: TermId,
    map: &[(TermId, TermId)],
    memo: &mut ay_core::kani_compat::DetHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&(_, r)) = map.iter().find(|(v, _)| *v == t) {
        return r;
    }
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let r = match terms.get(t).clone() {
        TermData::App(sym, args) if !args.is_empty() => {
            let sort = terms.sort(t).clone();
            let new: Vec<TermId> = args
                .iter()
                .map(|&a| subst_rec(terms, a, map, memo))
                .collect();
            if new == args {
                t
            } else {
                terms.mk_app(sym, new, sort)
            }
        }
        TermData::Not(i) => {
            let n = subst_rec(terms, i, map, memo);
            if n == i {
                t
            } else {
                terms.mk_not_raw(n)
            }
        }
        TermData::Ite(c, a, b) => {
            let (c2, a2, b2) = (
                subst_rec(terms, c, map, memo),
                subst_rec(terms, a, map, memo),
                subst_rec(terms, b, map, memo),
            );
            if (c2, a2, b2) == (c, a, b) {
                t
            } else {
                terms.mk_ite_raw(c2, a2, b2)
            }
        }
        _ => t,
    };
    memo.insert(t, r);
    r
}

/// [`substitute`] that also folds Boolean constants through `and`, `or`,
/// `not`, `=>` and Boolean `ite`, and evaluates arithmetic comparisons whose
/// sides became numerals. Equivalence-preserving; used to present pinned
/// kernel queries in their simplified form.
pub(crate) fn substitute_fold(
    terms: &mut TermStore,
    t: TermId,
    map: &[(TermId, TermId)],
) -> TermId {
    let mut memo = ay_core::kani_compat::DetHashMap::default();
    fold_rec(terms, t, map, &mut memo)
}

fn bool_const(terms: &TermStore, t: TermId) -> Option<bool> {
    match terms.get(t) {
        TermData::Const(ay_core::term::Constant::Bool(b)) => Some(*b),
        _ => None,
    }
}

fn fold_rec(
    terms: &mut TermStore,
    t: TermId,
    map: &[(TermId, TermId)],
    memo: &mut ay_core::kani_compat::DetHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&(_, r)) = map.iter().find(|(v, _)| *v == t) {
        return r;
    }
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let r = stacker::maybe_grow(64 * 1024, 4 * 1024 * 1024, || match terms.get(t).clone() {
        TermData::Not(i) => {
            let n = fold_rec(terms, i, map, memo);
            match bool_const(terms, n) {
                Some(b) => terms.mk_bool(!b),
                None if n == i => t,
                None => terms.mk_not_raw(n),
            }
        }
        TermData::Ite(c, a, b) => {
            let c2 = fold_rec(terms, c, map, memo);
            match bool_const(terms, c2) {
                Some(true) => fold_rec(terms, a, map, memo),
                Some(false) => fold_rec(terms, b, map, memo),
                None => {
                    let a2 = fold_rec(terms, a, map, memo);
                    let b2 = fold_rec(terms, b, map, memo);
                    if (c2, a2, b2) == (c, a, b) {
                        t
                    } else {
                        terms.mk_ite_raw(c2, a2, b2)
                    }
                }
            }
        }
        TermData::App(sym, args) if !args.is_empty() => fold_app(terms, t, sym, args, map, memo),
        _ => t,
    });
    memo.insert(t, r);
    r
}

/// One folded application (see [`substitute_fold`]).
fn fold_app(
    terms: &mut TermStore,
    t: TermId,
    sym: ay_core::term::Symbol,
    args: Vec<TermId>,
    map: &[(TermId, TermId)],
    memo: &mut ay_core::kani_compat::DetHashMap<TermId, TermId>,
) -> TermId {
    let sort = terms.sort(t).clone();
    let new: Vec<TermId> = args
        .iter()
        .map(|&a| fold_rec(terms, a, map, memo))
        .collect();
    match sym.name() {
        "and" | "or" => {
            let unit = sym.name() == "and";
            let mut kept = Vec::with_capacity(new.len());
            for a in new {
                match bool_const(terms, a) {
                    Some(b) if b == unit => {}
                    Some(_) => return terms.mk_bool(!unit),
                    None => kept.push(a),
                }
            }
            match kept.len() {
                0 => terms.mk_bool(unit),
                1 => kept[0],
                _ => terms.mk_app(sym, kept, sort),
            }
        }
        "not" if new.len() == 1 => match bool_const(terms, new[0]) {
            Some(b) => terms.mk_bool(!b),
            None => terms.mk_app(sym, new, sort),
        },
        "=>" if new.len() == 2 => match (bool_const(terms, new[0]), bool_const(terms, new[1])) {
            (Some(false), _) | (_, Some(true)) => terms.mk_bool(true),
            (Some(true), _) => new[1],
            (_, Some(false)) => terms.mk_not_raw(new[0]),
            _ => terms.mk_app(sym, new, sort),
        },
        "=" | "<" | "<=" | ">" | ">=" | "distinct" => {
            let nums: Option<Vec<num_rational::BigRational>> =
                new.iter().map(|&a| super::lin::numeral(terms, a)).collect();
            let bools: Option<Vec<bool>> = new.iter().map(|&a| bool_const(terms, a)).collect();
            let folded = match (nums, bools) {
                (Some(v), _) if v.len() >= 2 => Some(match sym.name() {
                    "=" => v.windows(2).all(|w| w[0] == w[1]),
                    "<" => v.windows(2).all(|w| w[0] < w[1]),
                    "<=" => v.windows(2).all(|w| w[0] <= w[1]),
                    ">" => v.windows(2).all(|w| w[0] > w[1]),
                    ">=" => v.windows(2).all(|w| w[0] >= w[1]),
                    _ => v
                        .iter()
                        .enumerate()
                        .all(|(i, x)| v[i + 1..].iter().all(|y| x != y)),
                }),
                (_, Some(v)) if v.len() == 2 && matches!(sym.name(), "=" | "distinct") => {
                    Some((v[0] == v[1]) == (sym.name() == "="))
                }
                _ => None,
            };
            // `(= c X)` over Booleans with one constant side.
            if folded.is_none() && new.len() == 2 && matches!(sym.name(), "=" | "distinct") {
                let equal = sym.name() == "=";
                for (k, other) in [(0usize, 1usize), (1, 0)] {
                    if let Some(b) = bool_const(terms, new[k]) {
                        if matches!(terms.sort(new[other]), Sort::Bool) {
                            let x = new[other];
                            return if b == equal { x } else { terms.mk_not_raw(x) };
                        }
                    }
                }
            }
            match folded {
                Some(b) => terms.mk_bool(b),
                None if new == args => t,
                None => terms.mk_app(sym, new, sort),
            }
        }
        _ => {
            if new == args {
                t
            } else {
                terms.mk_app(sym, new, sort)
            }
        }
    }
}
