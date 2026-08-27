// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SECOND ACCEPTANCE LEG — the INDEPENDENT checked ground normalizer the
//! validator re-derives both sides through when the exact parallel walk of
//! the sibling `structural` module refuses. This module owns the [`Norm`]
//! normal form and every equivalence the leg is allowed to apply:
//! substitution during the walk, the Boolean folds, `or`/`and` identity-
//! element drops, and the comparison canonicalization gated on Int-sorted
//! arguments. It decides nothing about clause shape and performs no exact
//! matching — it only says what a term's normal form is.

use ay_core::kani_compat::DetHashMap;
use ay_core::{TermData, TermId, TermStore};

/// Owned normal form for the checked-normalization leg. Built pure from the
/// term store (no interning); comparison is structural on the normal forms.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum Norm {
    True,
    False,
    IntConst(num_bigint::BigInt),
    /// Any leaf or unmodeled node, by identity.
    Atom(TermId),
    Not(Box<Norm>),
    /// n-ary with identity elements dropped; empty collapses to the
    /// identity, singletons to the element (see [`norm_junction`]).
    Or(Vec<Norm>),
    And(Vec<Norm>),
    /// Canonical non-strict Int comparison `lhs <= rhs`.
    Le(Box<Norm>, Box<Norm>),
    /// Orientation-normalized equality (smaller normal form first).
    Eq(Box<Norm>, Box<Norm>),
    App(String, Vec<Norm>),
    Ite(Box<Norm>, Box<Norm>, Box<Norm>),
}

fn norm_not(inner: Norm) -> Norm {
    match inner {
        Norm::True => Norm::False,
        Norm::False => Norm::True,
        Norm::Not(x) => *x,
        // `!(c <= x)  <=>  x <= c-1` and `!(x <= c)  <=>  c+1 <= x`, over
        // the INTEGER order only — the builder emits `Le` exclusively for
        // Int-sorted comparisons, so the shift is total here.
        Norm::Le(lhs, rhs) => match (*lhs, *rhs) {
            (Norm::IntConst(c), x) => Norm::Le(Box::new(x), Box::new(Norm::IntConst(c - 1))),
            (x, Norm::IntConst(c)) => Norm::Le(Box::new(Norm::IntConst(c + 1)), Box::new(x)),
            (l, r) => Norm::Not(Box::new(Norm::Le(Box::new(l), Box::new(r)))),
        },
        other => Norm::Not(Box::new(other)),
    }
}

fn norm_le(lhs: Norm, rhs: Norm) -> Norm {
    if let (Norm::IntConst(a), Norm::IntConst(b)) = (&lhs, &rhs) {
        return if a <= b { Norm::True } else { Norm::False };
    }
    Norm::Le(Box::new(lhs), Box::new(rhs))
}

fn norm_junction(items: Vec<Norm>, is_or: bool) -> Norm {
    let (identity, absorber) = if is_or {
        (Norm::False, Norm::True)
    } else {
        (Norm::True, Norm::False)
    };
    let mut kept = Vec::with_capacity(items.len());
    for item in items {
        if item == absorber {
            return absorber;
        }
        if item != identity {
            kept.push(item);
        }
    }
    match kept.len() {
        0 => identity,
        1 => kept.into_iter().next().expect("len checked"),
        _ => {
            if is_or {
                Norm::Or(kept)
            } else {
                Norm::And(kept)
            }
        }
    }
}

/// Normalize `term` with `map` applied as a simultaneous substitution during
/// the walk. `Err(())` means budget exhaustion or a binder/let (fail closed).
pub(super) fn normalize_with_substitution(
    terms: &TermStore,
    term: TermId,
    map: &DetHashMap<TermId, TermId>,
    budget: &mut usize,
) -> Result<Norm, ()> {
    if *budget == 0 {
        return Err(());
    }
    *budget -= 1;
    let term = map.get(&term).copied().unwrap_or(term);
    if let Some(value) = terms.extract_integer_constant(term) {
        return Ok(Norm::IntConst(value));
    }
    match terms.get(term) {
        TermData::Const(constant) => Ok(match constant {
            ay_core::Constant::Bool(true) => Norm::True,
            ay_core::Constant::Bool(false) => Norm::False,
            _ => Norm::Atom(term),
        }),
        TermData::Var(..) => Ok(Norm::Atom(term)),
        TermData::Not(inner) => Ok(norm_not(normalize_with_substitution(
            terms, *inner, map, budget,
        )?)),
        TermData::Ite(c, t, e) => {
            let (c, t, e) = (*c, *t, *e);
            let c = normalize_with_substitution(terms, c, map, budget)?;
            let t = normalize_with_substitution(terms, t, map, budget)?;
            let e = normalize_with_substitution(terms, e, map, budget)?;
            Ok(match c {
                Norm::True => t,
                Norm::False => e,
                c => Norm::Ite(Box::new(c), Box::new(t), Box::new(e)),
            })
        }
        TermData::App(symbol, args) => {
            let name = symbol.name().to_string();
            let args = args.clone();
            let all_int_sorted = args
                .iter()
                .all(|&a| matches!(terms.sort(a), ay_core::Sort::Int));
            let mut normalized = Vec::with_capacity(args.len());
            for &arg in &args {
                normalized.push(normalize_with_substitution(terms, arg, map, budget)?);
            }
            Ok(match (name.as_str(), normalized.len()) {
                ("or", _) => norm_junction(normalized, true),
                ("and", _) => norm_junction(normalized, false),
                ("not", 1) => norm_not(normalized.pop().expect("len checked")),
                ("=", 2) => {
                    let b = normalized.pop().expect("len checked");
                    let a = normalized.pop().expect("len checked");
                    if a == b {
                        Norm::True
                    } else if matches!((&a, &b), (Norm::IntConst(_), Norm::IntConst(_))) {
                        // Distinct, after the identical case above.
                        Norm::False
                    } else if a <= b {
                        Norm::Eq(Box::new(a), Box::new(b))
                    } else {
                        Norm::Eq(Box::new(b), Box::new(a))
                    }
                }
                ("<=", 2) if all_int_sorted => {
                    let b = normalized.pop().expect("len checked");
                    let a = normalized.pop().expect("len checked");
                    norm_le(a, b)
                }
                ("<", 2) if all_int_sorted => {
                    let b = normalized.pop().expect("len checked");
                    let a = normalized.pop().expect("len checked");
                    // `a < b  <=>  !(b <= a)`; norm_not performs the shift.
                    norm_not(norm_le(b, a))
                }
                (">=", 2) if all_int_sorted => {
                    let b = normalized.pop().expect("len checked");
                    let a = normalized.pop().expect("len checked");
                    norm_le(b, a)
                }
                (">", 2) if all_int_sorted => {
                    let b = normalized.pop().expect("len checked");
                    let a = normalized.pop().expect("len checked");
                    norm_not(norm_le(a, b))
                }
                _ => Norm::App(name, normalized),
            })
        }
        // Binders and unexpanded lets: fail closed.
        _ => Err(()),
    }
}
