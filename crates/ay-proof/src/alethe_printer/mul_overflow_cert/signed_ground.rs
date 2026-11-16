// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Word-level steps the signed row's facts share: literals, ground
//! evaluation (the checker evaluates only into a literal), the sign bit of a
//! known word, a word reassembled from its own extracts, and a product with
//! a zero operand.

use super::helpers::{eq_step, symm, trans};
use super::lin::Blaster;
use super::proof::{Prem, Proof, S};
use super::signed::Signed;
use super::term::{Op, T};

pub(super) fn not(p: &mut Proof<'_>, x: T) -> T {
    p.t.not(x)
}

/// `lit` when `pos`, its negation otherwise.
pub(super) fn lit(p: &mut Proof<'_>, x: T, pos: bool) -> T {
    if pos {
        x
    } else {
        p.t.not(x)
    }
}

/// `(= c v)` by `evaluate` for a ground `c` and a value `v` spelled as a
/// literal or a concatenation of literals; the checker evaluates only into
/// a literal, so a concatenation is reached through its literal.
pub(super) fn eval(p: &mut Proof<'_>, c: T, v: T) -> S {
    let Some(l) = literal(p, v).filter(|&l| l != v) else {
        return eq_step(p, c, v, "evaluate", &[]);
    };
    let e1 = eq_step(p, c, l, "evaluate", &[]);
    let e2 = eq_step(p, v, l, "evaluate", &[]);
    let e2s = symm(p, e2);
    trans(p, &[e1, e2s])
}

/// The literal of a literal or of a concatenation of literals.
fn literal(p: &mut Proof<'_>, v: T) -> Option<T> {
    match p.t.op(v) {
        Op::Lit(_) => Some(v),
        Op::Concat => {
            let mut bits = Vec::new();
            for a in p.t.args(v).to_vec().into_iter().rev() {
                let Op::Lit(b) = p.t.op(a) else {
                    return None;
                };
                bits.extend(b.iter().copied());
            }
            Some(p.t.lit(bits))
        }
        _ => None,
    }
}

/// The value of a sign-bit atom `(= ((_ extract n-1 n-1) w) v)` once `w` is
/// a known ground word: `eqw` is `(= w g)`; the step `(cl atom)` or
/// `(cl (not atom))`.
pub(super) fn sign_of_ground(p: &mut Proof<'_>, atom: T, eqw: S) -> Option<S> {
    let (ex, v) = (p.t.args(atom)[0], p.t.args(atom)[1]);
    let g = p.t.args(p.unit(eqw))[1];
    let Op::Extract(hi, lo) = *p.t.op(ex) else {
        return None;
    };
    let lit_g = literal(p, g)?;
    let Op::Lit(bits) = p.t.op(lit_g) else {
        return None;
    };
    let bit = bits[hi as usize];
    let exg = p.t.extract(hi, lo, g);
    let c1 = eq_step(p, ex, exg, "cong", &[eqw]);
    let lit1 = p.t.lit(vec![bit]);
    let e1 = eval(p, exg, lit1);
    let exl = trans(p, &[c1, e1]);
    let atom2 = p.t.eq(lit1, v);
    let c2 = eq_step(p, atom, atom2, "cong", &[exl]);
    let value = lit1 == v;
    let cv = if value { p.t.tt } else { p.t.ff };
    let e2 = eval(p, atom2, cv);
    let te = trans(p, &[c2, e2]);
    let target = if value { atom } else { p.t.not(atom) };
    let e = p.unit(te);
    let mut prem = p.gate(e);
    prem.extend(p.gate(cv));
    prem.push(Prem::Step(te));
    p.derive(&[target], &prem, &[])
}

/// `(= word target)` for a word spelled as a concatenation of `target`'s
/// extracts: both sides bit-blast to the same `@bit_of` projections.
pub(super) fn reassembled(p: &mut Proof<'_>, word: T, target: T) -> Option<S> {
    let mut bl = Blaster::new(&[], &[]);
    let (wb, ws) = bl.blast(p, word)?;
    let (tb, ts) = bl.blast(p, target)?;
    if wb != tb {
        return None;
    }
    let tss = symm(p, ts?);
    Some(trans(p, &[ws?, tss]))
}

/// `(= (bvmul ..) z)` for a product with a zero operand `which` (0 or 1),
/// given `(= operand z)`.
pub(super) fn zero_product(
    p: &mut Proof<'_>,
    s: &Signed,
    prod: T,
    which: usize,
    hz: S,
) -> Option<S> {
    let n = s.n();
    let l0 = p.t.lit(super::bits::zero(n));
    let ez = eval(p, s.z, l0);
    let args = p.t.args(prod).to_vec();
    let mut with_z = args.clone();
    with_z[which] = s.z;
    let mut with_l = args;
    with_l[which] = l0;
    let pz = p.t.mul(with_z[0], with_z[1]);
    let pl = p.t.mul(with_l[0], with_l[1]);
    let c1 = eq_step(p, prod, pz, "cong", &[hz]);
    let c2 = eq_step(p, pz, pl, "cong", &[ez]);
    let c3 = eq_step(p, pl, l0, "poly_simp", &[]);
    let ezs = symm(p, ez);
    Some(trans(p, &[c1, c2, c3, ezs]))
}
