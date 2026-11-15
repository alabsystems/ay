// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooper-style elimination of one `Int` variable under the model.

use ay_core::TermId;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::super::lin::{Lin, Model, Val};
use super::{int_lcm, Lit, MbpDecline, Rel};

/// `n mod d` in `[0, d)` for a positive `d`.
pub(super) fn modp(n: &BigInt, d: &BigInt) -> BigInt {
    n.mod_floor(d)
}

/// What an eliminated `Int` variable was replaced by.
pub(super) enum IntSubst {
    /// `v := lin` (integral).
    Term(Lin),
    /// `v := (div lin k)`, exact inside the projection.
    Div(Lin, BigInt),
}

/// Strict bounds, disequalities and negated divisibility over `v` become
/// non-strict bounds and positive divisibility, on the side `M` satisfies.
fn normalize(v: TermId, lits: &mut [Lit], m: &Model) -> Result<(), MbpDecline> {
    for lit in lits.iter_mut() {
        match lit {
            Lit::Arith(Rel::Lt, lin) if lin.mentions(v) => {
                lin.constant += BigRational::one();
                *lit = Lit::Arith(Rel::Le, lin.clone());
            }
            Lit::Arith(Rel::Ne, lin) if lin.mentions(v) => {
                let val = lin.eval(m).ok_or(MbpDecline::Model)?;
                let mut l = lin.clone();
                if !val.is_negative() {
                    l.scale(&-BigRational::one());
                }
                l.constant += BigRational::one();
                *lit = Lit::Arith(Rel::Le, l);
            }
            Lit::Div(d, lin, false) if lin.mentions(v) => {
                let val = lin.eval(m).ok_or(MbpDecline::Model)?;
                if !val.is_integer() {
                    return Err(MbpDecline::Model);
                }
                let r = modp(&val.to_integer(), d);
                let mut l = lin.clone();
                l.constant -= BigRational::from_integer(r);
                *lit = Lit::Div(d.clone(), l, true);
            }
            _ => {}
        }
    }
    Ok(())
}

/// The true equality over `v` with the smallest coefficient, if any.
fn best_equality(v: TermId, lits: &[Lit]) -> Option<usize> {
    let mut best: Option<(usize, BigRational)> = None;
    for (i, lit) in lits.iter().enumerate() {
        if let Lit::Arith(Rel::Eq, lin) = lit {
            let a = lin.coeff(v).abs();
            if !a.is_zero() && best.as_ref().is_none_or(|(_, b)| a < *b) {
                best = Some((i, a));
            }
        }
    }
    best.map(|(i, _)| i)
}

/// Resolve `v` through the equality `a·v + r = 0` at `index`.
fn resolve_equality(v: TermId, lits: &mut Vec<Lit>, index: usize) -> Result<IntSubst, MbpDecline> {
    let Lit::Arith(_, eq) = lits[index].clone() else {
        return Err(MbpDecline::Build);
    };
    let a = eq.coeff(v).to_integer();
    let r = eq.without(v); // a·v + r = 0
    let abs_a = a.abs();
    let sign = BigRational::from_integer(if a.is_negative() {
        -BigInt::one()
    } else {
        BigInt::one()
    });
    lits.remove(index);
    if abs_a.is_one() {
        // v = −r·sign(a)
        let t = r.scaled(&-sign.clone());
        for lit in lits.iter_mut() {
            match lit {
                Lit::Arith(_, lin) | Lit::Div(_, lin, _) if lin.mentions(v) => {
                    *lin = lin.subst(v, &t)
                }
                _ => {}
            }
        }
        return Ok(IntSubst::Term(t));
    }
    // |a|·lit, with a·v replaced by −r.
    let abs_q = BigRational::from_integer(abs_a.clone());
    for lit in lits.iter_mut() {
        let (lin, scale_d) = match lit {
            Lit::Arith(_, lin) => (lin, None),
            Lit::Div(d, lin, _) => (lin, Some(d)),
            Lit::Keep(..) => continue,
        };
        let b = lin.coeff(v);
        if b.is_zero() {
            continue;
        }
        let mut rest = lin.without(v);
        rest.scale(&abs_q);
        // b·|a|·v = b·sign(a)·(a·v) = −b·sign(a)·r
        let mut repl = r.clone();
        repl.scale(&(-(b * &sign)));
        rest.add(&repl);
        *lin = rest;
        if let Some(d) = scale_d {
            *d *= &abs_a;
        }
    }
    lits.push(Lit::Div(abs_a.clone(), r.clone(), true));
    // v = −sign(a)·r / |a|
    Ok(IntSubst::Div(r.scaled(&-sign), abs_a))
}

/// Rescale every literal over `v` to coefficient `±1` over `w = L·v`
/// (the same id), returning `L`.
fn unit_coefficients(v: TermId, lits: &mut [Lit]) -> BigInt {
    let mut l_big = BigInt::one();
    for lit in lits.iter() {
        if let Lit::Arith(_, lin) | Lit::Div(_, lin, _) = lit {
            let c = lin.coeff(v);
            if !c.is_zero() {
                l_big = int_lcm(&l_big, &c.to_integer().abs());
            }
        }
    }
    for lit in lits.iter_mut() {
        let (lin, d) = match lit {
            Lit::Arith(_, lin) => (lin, None),
            Lit::Div(d, lin, _) => (lin, Some(d)),
            Lit::Keep(..) => continue,
        };
        let c = lin.coeff(v);
        if c.is_zero() {
            continue;
        }
        let f = &l_big / c.to_integer().abs();
        let mut s = lin.without(v);
        s.scale(&BigRational::from_integer(f.clone()));
        s.add_var(
            v,
            if c.is_negative() {
                -BigRational::one()
            } else {
                BigRational::one()
            },
        );
        *lin = s;
        if let Some(d) = d {
            *d *= &f;
        }
    }
    l_big
}

/// A bound term with its value in the model.
type Valued = Option<(Lin, BigInt)>;

/// The largest lower and least upper bound on `w` (unit coefficients),
/// with their values in `m`.
fn best_bounds(w: TermId, lits: &[Lit], m: &Model) -> Result<(Valued, Valued), MbpDecline> {
    let mut lower: Valued = None;
    let mut upper: Valued = None;
    for lit in lits {
        let Lit::Arith(Rel::Le, lin) = lit else {
            continue;
        };
        let c = lin.coeff(w);
        if c.is_zero() {
            continue;
        }
        let rest = lin.without(w);
        if c.is_negative() {
            // −w + rest ≤ 0  ⇒  w ≥ rest
            let val = rest.eval(m).ok_or(MbpDecline::Model)?.to_integer();
            if lower.as_ref().is_none_or(|(_, b)| val > *b) {
                lower = Some((rest, val));
            }
        } else {
            // w + rest ≤ 0  ⇒  w ≤ −rest
            let bound = rest.scaled(&-BigRational::one());
            let val = bound.eval(m).ok_or(MbpDecline::Model)?.to_integer();
            if upper.as_ref().is_none_or(|(_, b)| val < *b) {
                upper = Some((bound, val));
            }
        }
    }
    Ok((lower, upper))
}

/// Eliminate one `Int` variable (Cooper under the model). `lits` must
/// already be integralized; new literals are appended.
pub(super) fn eliminate_int(
    v: TermId,
    lits: &mut Vec<Lit>,
    m: &Model,
) -> Result<IntSubst, MbpDecline> {
    let mv = m.num(v).cloned().unwrap_or_else(BigRational::zero);
    if !mv.is_integer() {
        return Err(MbpDecline::Model);
    }
    let mv = mv.to_integer();
    normalize(v, lits, m)?;
    if let Some(index) = best_equality(v, lits) {
        return resolve_equality(v, lits, index);
    }
    let l_big = unit_coefficients(v, lits);
    let w = v;
    let mw = &mv * &l_big;
    let mut model_w = m.clone();
    model_w
        .vals
        .insert(w, Val::Num(BigRational::from_integer(mw.clone())));
    if !l_big.is_one() {
        lits.push(Lit::Div(l_big.clone(), Lin::var(w), true));
    }
    // D = lcm of the divisors over w.
    let mut dd = BigInt::one();
    for lit in lits.iter() {
        if let Lit::Div(d, lin, true) = lit {
            if lin.mentions(w) {
                dd = int_lcm(&dd, d);
            }
        }
    }
    let t = match best_bounds(w, lits, &model_w)? {
        (Some((l, lv)), _) => {
            let mut t = l;
            t.constant += BigRational::from_integer(modp(&(&mw - &lv), &dd));
            t
        }
        (None, Some((u, uv))) => {
            let mut t = u;
            t.constant -= BigRational::from_integer(modp(&(&uv - &mw), &dd));
            t
        }
        (None, None) => Lin::constant(BigRational::from_integer(modp(&mw, &dd))),
    };
    for lit in lits.iter_mut() {
        match lit {
            Lit::Arith(_, lin) | Lit::Div(_, lin, _) if lin.mentions(w) => *lin = lin.subst(w, &t),
            _ => {}
        }
    }
    Ok(if l_big.is_one() {
        IntSubst::Term(t)
    } else {
        IntSubst::Div(t, l_big)
    })
}
