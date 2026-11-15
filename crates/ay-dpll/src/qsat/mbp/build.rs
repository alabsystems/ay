// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical atoms for projected literals.

use ay_core::term::Symbol;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::super::lin::Lin;
use super::int::modp;
use super::{Lit, MbpDecline, Rel};

fn without_constant(l: &Lin) -> Lin {
    let mut s = l.clone();
    s.constant = BigRational::zero();
    s
}

/// Build the atom of a literal; `Ok(None)` for a literal that is constantly
/// true.
pub(super) fn build(
    terms: &mut TermStore,
    lit: &Lit,
) -> Result<Option<(TermId, bool)>, MbpDecline> {
    match lit {
        Lit::Keep(a, v) => Ok(Some((*a, *v))),
        Lit::Arith(rel, lin) => build_arith(terms, *rel, lin),
        Lit::Div(d, lin, pos) => build_divides(terms, d, lin, *pos),
    }
}

fn constant_truth(rel: Rel, c: &BigRational) -> bool {
    match rel {
        Rel::Le => *c <= BigRational::zero(),
        Rel::Lt => *c < BigRational::zero(),
        Rel::Eq => c.is_zero(),
        Rel::Ne => !c.is_zero(),
    }
}

/// Integer normalization: integral coefficients, `<` as `≤ −1`, gcd
/// reduction (with the floor on the bound).
fn normalize_int(mut l: Lin, mut rel: Rel) -> (Lin, Rel) {
    l.scale(&BigRational::from_integer(l.denom_lcm()));
    if rel == Rel::Lt {
        l.constant += BigRational::one();
        rel = Rel::Le;
    }
    let g = l
        .coeffs
        .values()
        .fold(BigInt::zero(), |g, c| g.gcd(&c.to_integer()));
    if g.is_zero() || g.is_one() {
        return (l, rel);
    }
    let gq = BigRational::from_integer(g);
    match rel {
        Rel::Le => {
            // Σa·x + k ≤ 0  ⇔  Σ(a/g)·x ≤ ⌊−k/g⌋
            let k = -l.constant.clone() / &gq;
            let mut vars = without_constant(&l);
            vars.scale(&gq.recip());
            vars.constant = -BigRational::from_integer(k.floor().to_integer());
            (vars, rel)
        }
        Rel::Eq | Rel::Ne if (&l.constant / &gq).is_integer() => {
            l.scale(&gq.recip());
            (l, rel)
        }
        _ => (l, rel),
    }
}

fn build_arith(
    terms: &mut TermStore,
    rel: Rel,
    lin: &Lin,
) -> Result<Option<(TermId, bool)>, MbpDecline> {
    if lin.is_const() {
        return if constant_truth(rel, &lin.constant) {
            Ok(None)
        } else {
            Err(MbpDecline::Preservation)
        };
    }
    let int = lin.all_int(terms);
    let (mut l, rel) = if int {
        normalize_int(lin.clone(), rel)
    } else {
        let mut l = lin.clone();
        if let Some(first) = l.coeffs.values().next().cloned() {
            l.scale(&first.abs().recip());
        }
        (l, rel)
    };
    if matches!(rel, Rel::Eq | Rel::Ne) {
        if let Some(first) = l.coeffs.values().next().cloned() {
            if first.is_negative() {
                l.scale(&-BigRational::one());
            }
        }
    }
    let sort = if int { Sort::Int } else { Sort::Real };
    let k = -l.constant.clone();
    let lhs = without_constant(&l)
        .to_term(terms, &sort)
        .ok_or(MbpDecline::Build)?;
    let rhs = if int {
        if !k.is_integer() {
            return Err(MbpDecline::Build);
        }
        terms.mk_int(k.to_integer())
    } else {
        terms.mk_rational(k)
    };
    let (name, value) = match rel {
        Rel::Le => ("<=", true),
        Rel::Lt => ("<", true),
        Rel::Eq => ("=", true),
        Rel::Ne => ("=", false),
    };
    Ok(Some((
        terms.mk_app(Symbol::named(name), vec![lhs, rhs], Sort::Bool),
        value,
    )))
}

/// `d | lin` as `(= (mod L d) k)`: `L` the non-constant part with its
/// coefficients reduced modulo `d`, `k = (-c) mod d`. Every residue lemma over
/// one `L` then shares the single `(mod L d)` term, which the ground kernel
/// purifies once (as `(mod (+ x 1) 3)`, `(mod x 3)`, `(mod (+ x 2) 3)` it
/// purified three unrelated terms and could not refute their exhaustion).
fn build_divides(
    terms: &mut TermStore,
    d: &BigInt,
    lin: &Lin,
    pos: bool,
) -> Result<Option<(TermId, bool)>, MbpDecline> {
    let s = lin.denom_lcm();
    let d = d * &s;
    let mut l = lin.scaled(&BigRational::from_integer(s));
    if d.is_one() {
        return if pos {
            Ok(None)
        } else {
            Err(MbpDecline::Preservation)
        };
    }
    let keys: Vec<TermId> = l.coeffs.keys().copied().collect();
    for k in keys {
        let c = l.coeff(k).to_integer();
        l.coeffs.remove(&k);
        l.add_var(k, BigRational::from_integer(modp(&c, &d)));
    }
    l.constant = BigRational::from_integer(modp(&l.constant.to_integer(), &d));
    if l.is_const() {
        return if l.constant.is_zero() == pos {
            Ok(None)
        } else {
            Err(MbpDecline::Preservation)
        };
    }
    let residue = modp(&(-l.constant.to_integer()), &d);
    let body = without_constant(&l)
        .to_term(terms, &Sort::Int)
        .ok_or(MbpDecline::Build)?;
    let dt = terms.mk_int(d);
    let modt = terms.mk_app(Symbol::named("mod"), vec![body, dt], Sort::Int);
    let k = terms.mk_int(residue);
    Ok(Some((
        terms.mk_app(Symbol::named("="), vec![modt, k], Sort::Bool),
        pos,
    )))
}
