// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constant-fold `((_ to_fp eb sb) <rm> <real>)` into the IEEE bit pattern.
//!
//! When the rounding mode and the real argument are both constants — the
//! standard way FP literals are written, e.g. `((_ to_fp 8 24) RNE 0.5)` — the
//! result is fully determined by correct IEEE-754 rounding. We compute the bit
//! pattern and rewrite the term to the (already bit-blasted) 1-argument
//! `((_ to_fp eb sb) <BV>)` reinterpret form, so no new solving path is needed.
//!
//! Without this, a real-argument `to_fp` is reported `Unsupported` and the whole
//! FP query returns `unknown` (a real, common gap, since this is *the* SMT-LIB
//! FP-literal syntax).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{TermId, TermStore};
use ay_fp::{round_rational_to_ieee_bits, RoundingMode};
use num_rational::BigRational;
use num_traits::Zero;

/// Rewrite every assertion, folding constant-real `to_fp` applications.
pub(super) fn fold_to_fp_real_constants(
    terms: &mut TermStore,
    assertions: &[TermId],
) -> Vec<TermId> {
    let mut cache: HashMap<TermId, TermId> = HashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite(terms, a, &mut cache))
        .collect()
}

/// The rounding mode denoted by `term`, if it is a constant `RNE`/`RNA`/… symbol.
fn rounding_mode_of(terms: &TermStore, term: TermId) -> Option<RoundingMode> {
    if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
        if args.is_empty() {
            return RoundingMode::from_name(name);
        }
    }
    None
}

/// The exact rational value of `term`, if it is a constant real expression
/// (`Const`, unary `-`, or `/` of constants — the literal forms SMT-LIB uses).
fn const_real_of(terms: &TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            const_real_of(terms, args[0]).map(|r| -r)
        }
        TermData::App(Symbol::Named(name), args) if name == "/" && args.len() == 2 => {
            let num = const_real_of(terms, args[0])?;
            let den = const_real_of(terms, args[1])?;
            if den.is_zero() {
                None
            } else {
                Some(num / den)
            }
        }
        _ => None,
    }
}

fn rewrite(terms: &mut TermStore, term: TermId, cache: &mut HashMap<TermId, TermId>) -> TermId {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }
    let data = terms.get(term).clone();
    let sort = terms.sort(term).clone();
    let result = match data {
        TermData::Const(_) | TermData::Var(_, _) => term,
        TermData::Not(inner) => {
            let ni = rewrite(terms, inner, cache);
            if ni == inner {
                term
            } else {
                terms.mk_not(ni)
            }
        }
        TermData::Ite(c, t, e) => {
            let nc = rewrite(terms, c, cache);
            let nt = rewrite(terms, t, cache);
            let ne = rewrite(terms, e, cache);
            if nc == c && nt == t && ne == e {
                term
            } else {
                terms.mk_ite(nc, nt, ne)
            }
        }
        // `to_fp` with a constant rounding mode and a constant real → fold to the
        // IEEE bit pattern wrapped in the 1-arg BV-reinterpret `to_fp`.
        TermData::App(Symbol::Indexed(name, indices), args)
            if name == "to_fp" && indices.len() == 2 && args.len() == 2 =>
        {
            if let (Some(rm), Some(value)) = (
                rounding_mode_of(terms, args[0]),
                const_real_of(terms, args[1]),
            ) {
                let (eb, sb) = (indices[0], indices[1]);
                let bits = round_rational_to_ieee_bits(&value, eb, sb, rm);
                let bv = terms.mk_bitvec(bits, eb + sb);
                terms.mk_app(Symbol::indexed("to_fp", vec![eb, sb]), vec![bv], sort)
            } else {
                rewrite_app(
                    terms,
                    Symbol::Indexed(name, indices),
                    &args,
                    sort,
                    term,
                    cache,
                )
            }
        }
        TermData::App(sym, args) => rewrite_app(terms, sym, &args, sort, term, cache),
        TermData::Let(bindings, body) => {
            let new_bindings: Vec<_> = bindings
                .iter()
                .map(|(n, v)| (n.clone(), rewrite(terms, *v, cache)))
                .collect();
            let nb = rewrite(terms, body, cache);
            if nb == body && new_bindings == bindings {
                term
            } else {
                terms.mk_let(new_bindings, nb)
            }
        }
        // Do not descend into quantifier bodies: bound variables would be
        // unaffected and folding only targets ground constant literals.
        TermData::Forall(..) | TermData::Exists(..) => term,
        _ => term,
    };
    cache.insert(term, result);
    result
}

fn rewrite_app(
    terms: &mut TermStore,
    sym: Symbol,
    args: &[TermId],
    sort: ay_core::Sort,
    term: TermId,
    cache: &mut HashMap<TermId, TermId>,
) -> TermId {
    let new_args: Vec<TermId> = args.iter().map(|&a| rewrite(terms, a, cache)).collect();
    if new_args == args {
        term
    } else {
        terms.mk_app(sym, new_args, sort)
    }
}
