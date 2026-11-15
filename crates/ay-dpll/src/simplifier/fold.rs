// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The folding rebuild every pass runs after a substitution: Boolean
//! connectives, `ite`, equality, arithmetic and bit-vector predicates are
//! rebuilt through their simplifying constructors, so a substituted constant
//! decides the guards and literals it reaches. Every step is an equivalence.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TermStore};

use super::terms::{rebuild_quantifier, Binder};
use super::WorkBudget;

/// Red zone / segment size for the recursive rebuild (#8414).
const STACK_RED_ZONE: usize = 32 * 1024;
const STACK_SIZE: usize = 1024 * 1024;

/// Rebuild `t` bottom-up through the folding constructors (Boolean
/// connectives, `ite`, equality, arithmetic comparison and constant folding),
/// descending into quantifier bodies. Pure normalization: every rebuild step
/// is an equivalence, so the result has the same models as `t`.
///
/// Returns `None` when the budget runs out (the caller keeps `t`).
pub(super) fn refold(
    terms: &mut TermStore,
    t: TermId,
    cache: &mut HashMap<TermId, TermId>,
    budget: &mut WorkBudget<'_>,
) -> Option<TermId> {
    if let Some(&done) = cache.get(&t) {
        return Some(done);
    }
    if !budget.tick() {
        return None;
    }
    let result = stacker::maybe_grow(STACK_RED_ZONE, STACK_SIZE, || -> Option<TermId> {
        Some(match terms.get(t).clone() {
            TermData::Const(_) | TermData::Var(_, _) => t,
            TermData::Not(inner) => {
                let ni = refold(terms, inner, cache, budget)?;
                if ni == inner {
                    t
                } else {
                    terms.mk_not(ni)
                }
            }
            TermData::Ite(c, a, b) => {
                let nc = refold(terms, c, cache, budget)?;
                let na = refold(terms, a, cache, budget)?;
                let nb = refold(terms, b, cache, budget)?;
                if (nc, na, nb) == (c, a, b) {
                    t
                } else {
                    terms.mk_ite(nc, na, nb)
                }
            }
            TermData::App(sym, args) => {
                let mut new_args = Vec::with_capacity(args.len());
                for &arg in &args {
                    new_args.push(refold(terms, arg, cache, budget)?);
                }
                // An application over constants is rebuilt even when its
                // arguments did not change: a raw constructor (the E-matching
                // substitution builds BV predicates unfolded) may have left it
                // unevaluated.
                if new_args == args && !new_args.iter().all(|&a| is_const(terms, a)) {
                    t
                } else {
                    rebuild_app(terms, &sym, new_args, t)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let nb = refold(terms, body, cache, budget)?;
                if nb == body {
                    t
                } else {
                    rebuild_quantifier(terms, t, Binder::Forall, vars, nb, triggers)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let nb = refold(terms, body, cache, budget)?;
                if nb == body {
                    t
                } else {
                    rebuild_quantifier(terms, t, Binder::Exists, vars, nb, triggers)
                }
            }
            // Lets are expanded before solving; any other node is kept.
            _ => t,
        })
    })?;
    cache.insert(t, result);
    Some(result)
}

/// Rebuild one application with the folding constructor for its operator.
pub(super) fn rebuild_app(
    terms: &mut TermStore,
    sym: &Symbol,
    args: Vec<TermId>,
    original: TermId,
) -> TermId {
    let binary = args.len() == 2;
    match sym.name() {
        "and" => terms.mk_and(args),
        "or" => terms.mk_or(args),
        "=>" if binary => terms.mk_implies(args[0], args[1]),
        "xor" if binary => terms.mk_xor(args[0], args[1]),
        "distinct" if args.len() >= 2 => terms.mk_distinct(args),
        // Bit-vector predicates and structure the E-matching rebuild leaves
        // raw: fold them so a substituted constant decides an `ite` guard.
        "bvult" if binary => terms.mk_bvult(args[0], args[1]),
        "bvule" if binary => terms.mk_bvule(args[0], args[1]),
        "bvugt" if binary => terms.mk_bvugt(args[0], args[1]),
        "bvuge" if binary => terms.mk_bvuge(args[0], args[1]),
        "bvslt" if binary => terms.mk_bvslt(args[0], args[1]),
        "bvsle" if binary => terms.mk_bvsle(args[0], args[1]),
        "bvsgt" if binary => terms.mk_bvsgt(args[0], args[1]),
        "bvsge" if binary => terms.mk_bvsge(args[0], args[1]),
        "concat" if binary => terms.mk_bvconcat(args),
        "extract" if args.len() == 1 => match sym {
            Symbol::Indexed(_, indices) if indices.len() == 2 => {
                terms.mk_bvextract(indices[0], indices[1], args[0])
            }
            _ => crate::ematching::mk_app_simplified(terms, sym, args, original),
        },
        _ => crate::ematching::mk_app_simplified(terms, sym, args, original),
    }
}

/// Is `t` a node whose value is fixed (`true`/`false` or a literal)?
pub(super) fn is_const(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.get(t), TermData::Const(_))
}
