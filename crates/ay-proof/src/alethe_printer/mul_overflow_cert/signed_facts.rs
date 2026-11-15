// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The signed row's `(cl (= OV RV))` from the unsigned core over the
//! magnitudes. Every fact below is a small clause — a word-level chain of
//! `cong`/`ite_simplify`/`poly_simp`/`evaluate` steps under its hypotheses,
//! or a bit-level clause over bit-blasted word atoms — and one local
//! refutation over their atoms combines them.
//!
//! The case analysis the facts encode: with `s` the magnitudes' sign
//! (`sA xor sB`) and `p` the wrapped product's top bit, `|A| * |B| mod 2^n`
//! is the product (`s = 0`) or its negation (`s = 1`). When `p = s` the
//! active `bvsdiv` case divides exactly that magnitude by `|B|`, so it gives
//! back `A` exactly when the unsigned core says there is no high half, and
//! the magnitude is within `LIM`. When `p != s` (and `A != 0`) the product
//! overflowed, and the case's quotient cannot be `A`: its top bit would have
//! to be set, which takes a divisor of one and a dividend of `MIN`, and then
//! `A` is `MIN` with `B = -1` — the excluded case — or the signs agree after all.

use super::div_lemma::DivLemma;
use super::helpers::{eq_step, split_or, symm, trans, transfer};
use super::local::{bitfact, branch, under};
use super::proof::{Prem, Proof, S};
use super::row::Row;
use super::signed::Signed;
use super::signed_cases::{contradictions, quotients, spec_overflows};
use super::signed_ground::{eval, lit, not, reassembled, sign_of_ground, zero_product};
use super::term::T;

/// What the unsigned core over the magnitudes proved.
pub(crate) struct Core<'a> {
    pub(crate) row: &'a Row,
    /// `(cl (= (not hz) (and (not az) (not qb))))`.
    pub(crate) tb: S,
    /// `(cl (or (not (= P Z)) (= Q Z)))`: a zero wrapped product has quotient zero.
    pub(crate) zero: S,
}

pub(super) struct Atoms {
    pub(super) xaa: T,
    pub(super) xan: T,
    pub(super) xbb: T,
    pub(super) xbn: T,
    pub(super) lop: T,
    pub(super) lonp: T,
    pub(super) limmax: T,
    pub(super) limmin: T,
    pub(super) pz: T,
    pub(super) dz: T,
    pub(super) ndz: T,
    pub(super) az: T,
    pub(super) xaz: T,
    pub(super) xbz: T,
    pub(super) db: T,
    pub(super) lz: T,
    pub(super) qbx: T,
    pub(super) pzt: T,
    pub(super) qz: T,
    /// `(= case_k A)` for the four case results.
    pub(super) sk: [T; 4],
    /// `(= q_k qT)`.
    pub(super) eqk: [T; 4],
}

impl Atoms {
    fn new(p: &mut Proof, s: &Signed, row: &Row) -> Self {
        let t = &mut p.t;
        Atoms {
            xaa: t.eq(s.xa, s.a),
            xan: t.eq(s.xa, s.na),
            xbb: t.eq(s.xb, s.b),
            xbn: t.eq(s.xb, s.nb),
            lop: t.eq(s.lo, s.pp),
            lonp: t.eq(s.lo, s.np),
            limmax: t.eq(s.lim, s.maxw),
            limmin: t.eq(s.lim, s.minw),
            pz: t.eq(s.pp, s.z),
            dz: t.eq(s.d, s.z),
            ndz: t.eq(s.nd, s.z),
            az: t.eq(s.a, s.z),
            xaz: t.eq(s.xa, s.z),
            xbz: t.eq(s.xb, s.z),
            db: t.eq(s.d, s.b),
            lz: t.eq(s.lo, s.z),
            qbx: t.eq(row.q, s.xa),
            pzt: t.eq(row.p, row.z),
            qz: t.eq(row.q, row.z),
            sk: s.res.map(|r| t.eq(r, s.a)),
            eqk: s.q.map(|q| t.eq(q, row.q)),
        }
    }
}

pub(crate) fn prove(p: &mut Proof, s: &Signed, core: &Core<'_>, dl: &DivLemma) -> Option<S> {
    let row = core.row;
    let at = Atoms::new(p, s, row);
    let zero = split_or(p, core.zero);
    let mut facts: Vec<S> = vec![core.tb, zero];
    let (wa, wp) = core_words(p, s, row, &at, &mut facts)?;
    by_sign(p, s, &at, &mut facts)?;
    let not_both_p = sign_bits(p, s, &at, &mut facts)?;
    divisor(p, s, &at, &mut facts)?;
    zero_operands(p, s, &at, &mut facts)?;
    overflow(p, s, &at, &mut facts)?;
    case_taken(p, s, &at, &mut facts)?;
    quotients(p, s, row, &at, wa, wp, &mut facts)?;
    contradictions(p, s, &at, dl, not_both_p, &mut facts)?;
    // Combine.
    let g = p.t.eq(s.ov, s.rv);
    let mut prem: Vec<Prem> = facts.iter().map(|&f| Prem::Step(f)).collect();
    let tb_eq = p.unit(core.tb);
    let tb_and = p.t.args(tb_eq)[1];
    for gate in [
        g, s.ov, s.rv, s.first, s.spec, s.c[0], s.c[1], s.c[2], tb_eq, tb_and,
    ] {
        prem.extend(p.gate(gate));
    }
    p.derive(&[g], &prem, &[])
}

/// The core's words are the magnitudes: `(= a |B|)`, `(= p lo)` (returned)
/// and the zero and quotient atoms read through them.
fn core_words(
    p: &mut Proof,
    s: &Signed,
    row: &Row,
    at: &Atoms,
    facts: &mut Vec<S>,
) -> Option<(S, S)> {
    let wa = reassembled(p, row.a, s.xb)?;
    let wb = reassembled(p, row.b, s.xa)?;
    let wp = {
        let flipped = p.t.mul(s.xb, s.xa);
        let c = eq_step(p, row.p, flipped, "cong", &[wa, wb]);
        let ps = eq_step(p, flipped, s.lo, "poly_simp", &[]);
        trans(p, &[c, ps])
    };
    facts.push(under(p, &[row.az], at.xbz, |p, h| {
        let ws = symm(p, wa);
        Some(trans(p, &[ws, h[0]]))
    })?);
    facts.push(under(p, &[at.xbz], row.az, |p, h| {
        Some(trans(p, &[wa, h[0]]))
    })?);
    // a zero quotient is `|A|` exactly when `|A|` is zero
    facts.push(under(p, &[at.qz, at.qbx], at.xaz, |p, h| {
        let xq = symm(p, h[1]);
        Some(trans(p, &[xq, h[0]]))
    })?);
    facts.push(under(p, &[at.qz, at.xaz], at.qbx, |p, h| {
        let zx = symm(p, h[1]);
        Some(trans(p, &[h[0], zx]))
    })?);
    facts.push(under(p, &[at.lz], at.pzt, |p, h| {
        Some(trans(p, &[wp, h[0]]))
    })?);
    facts.push(under(p, &[row.qb], at.qbx, |p, h| {
        Some(trans(p, &[h[0], wb]))
    })?);
    facts.push(under(p, &[at.qbx], row.qb, |p, h| {
        let wbs = symm(p, wb);
        Some(trans(p, &[h[0], wbs]))
    })?);
    Some((wa, wp))
}

/// The magnitudes, the wrapped magnitude product and the limit by the signs.
fn by_sign(p: &mut Proof, s: &Signed, at: &Atoms, facts: &mut Vec<S>) -> Option<()> {
    for (sign, x, same, neg) in [(s.sa, s.xa, at.xaa, at.xan), (s.sb, s.xb, at.xbb, at.xbn)] {
        let nsign = not(p, sign);
        facts.push(under(p, &[nsign], same, |p, h| branch(p, x, h[0]))?);
        facts.push(under(p, &[sign], neg, |p, h| branch(p, x, h[0]))?);
    }
    // The wrapped magnitude product is the product or its negation.
    for (ha, hb, target, ma, mb) in [
        (at.xaa, at.xbb, at.lop, s.a, s.b),
        (at.xan, at.xbn, at.lop, s.na, s.nb),
        (at.xaa, at.xbn, at.lonp, s.a, s.nb),
        (at.xan, at.xbb, at.lonp, s.na, s.b),
    ] {
        facts.push(under(p, &[ha, hb], target, |p, h| {
            let prod = p.t.mul(ma, mb);
            let c = eq_step(p, s.lo, prod, "cong", &[h[0], h[1]]);
            let rhs = p.t.args(target)[1];
            if prod == rhs {
                return Some(c);
            }
            let ps = eq_step(p, prod, rhs, "poly_simp", &[]);
            Some(trans(p, &[c, ps]))
        })?);
    }
    // The limit by the signs.
    for (va, vb) in [(true, true), (false, false), (true, false), (false, true)] {
        let (la, lb) = (lit(p, s.sa, va), lit(p, s.sb, vb));
        let target = if va == vb { at.limmax } else { at.limmin };
        let ss_lit = lit(p, s.ss, va == vb);
        facts.push(under(p, &[la, lb], target, |p, h| {
            let mut prem = p.gate(s.ss);
            prem.push(Prem::Step(h[0]));
            prem.push(Prem::Step(h[1]));
            let ssf = p.derive(&[ss_lit], &prem, &[])?;
            branch(p, s.lim, ssf)
        })?);
    }
    Some(())
}

/// One-bit facts of the product's and the divisor's sign bits; returns
/// `(cl (not p0) (not p1))`.
fn sign_bits(p: &mut Proof, s: &Signed, at: &Atoms, facts: &mut Vec<S>) -> Option<S> {
    let (np0, np1) = (not(p, s.p0), not(p, s.p1));
    let (nd0, nd1) = (not(p, s.d0), not(p, s.d1));
    let not_both_p = bitfact(p, &[], &[np0, np1])?;
    facts.push(bitfact(p, &[], &[s.p0, s.p1])?);
    facts.push(not_both_p);
    facts.push(bitfact(p, &[], &[s.d0, s.d1])?);
    facts.push(bitfact(p, &[], &[nd0, nd1])?);
    // a zero word's sign bit is clear; equal words' sign bits agree
    facts.push(under(p, &[at.pz], s.p0, |p, h| {
        sign_of_ground(p, s.p0, h[0])
    })?);
    let ex_d = p.t.args(s.d1)[0];
    let ex_b = p.t.args(s.sb)[0];
    for (from, to) in [(s.d1, s.sb), (s.sb, s.d1)] {
        facts.push(under(p, &[at.db, from], to, |p, h| {
            let ce = eq_step(p, ex_d, ex_b, "cong", &[h[0]]);
            let ab = eq_step(p, s.d1, s.sb, "cong", &[ce]);
            let eq = if from == s.d1 { ab } else { symm(p, ab) };
            transfer(p, eq, h[1])
        })?);
    }
    Some(not_both_p)
}

/// The divisor `D` is `B` off the special cases, and neither `D` nor `-D`
/// is zero unless `B` is.
fn divisor(p: &mut Proof, s: &Signed, at: &Atoms, facts: &mut Vec<S>) -> Option<()> {
    let (nbz, nspec) = (not(p, s.bz), not(p, s.spec));
    facts.push(under(p, &[nbz, nspec], at.db, |p, h| {
        let mut prem = p.gate(s.dc);
        prem.extend(h.iter().map(|&x| Prem::Step(x)));
        let ndc = not(p, s.dc);
        let f = p.derive(&[ndc], &prem, &[])?;
        branch(p, s.d, f)
    })?);
    facts.push(under(p, &[at.db, at.dz], s.bz, |p, h| {
        let bd = symm(p, h[0]);
        Some(trans(p, &[bd, h[1]]))
    })?);
    let nz = p.t.neg(s.z);
    facts.push(under(p, &[at.ndz], at.dz, |p, h| {
        let back = p.t.neg(s.nd);
        let e1 = eq_step(p, s.d, back, "poly_simp", &[]);
        let e2 = eq_step(p, back, nz, "cong", &[h[0]]);
        let e3 = eval(p, nz, s.z);
        Some(trans(p, &[e1, e2, e3]))
    })?);
    Some(())
}

/// Zero operands, word by word, and the zero products they make.
fn zero_operands(p: &mut Proof, s: &Signed, at: &Atoms, facts: &mut Vec<S>) -> Option<()> {
    let nz = p.t.neg(s.z);
    for (w, x, neg, zero, same, negated) in [
        (s.a, s.xa, s.na, at.az, at.xaa, at.xan),
        (s.b, s.xb, s.nb, s.bz, at.xbb, at.xbn),
    ] {
        let xz = p.t.eq(x, s.z);
        // `w = 0` with `|w| = w` or `|w| = -w` makes `|w| = 0`
        facts.push(under(p, &[zero, same], xz, |p, h| {
            Some(trans(p, &[h[1], h[0]]))
        })?);
        facts.push(under(p, &[zero, negated], xz, |p, h| {
            let c = eq_step(p, neg, nz, "cong", &[h[0]]);
            let e = eval(p, nz, s.z);
            Some(trans(p, &[h[1], c, e]))
        })?);
        // and back
        facts.push(under(p, &[xz, same], zero, |p, h| {
            let wx = symm(p, h[1]);
            Some(trans(p, &[wx, h[0]]))
        })?);
        facts.push(under(p, &[xz, negated], zero, |p, h| {
            let back = p.t.neg(neg);
            let nx = p.t.neg(x);
            let e1 = eq_step(p, w, back, "poly_simp", &[]);
            let xs = symm(p, h[1]);
            let e2 = eq_step(p, back, nx, "cong", &[xs]);
            let e3 = eq_step(p, nx, nz, "cong", &[h[0]]);
            let e4 = eval(p, nz, s.z);
            Some(trans(p, &[e1, e2, e3, e4]))
        })?);
    }
    facts.push(under(p, &[at.az, at.xaa], at.xan, |p, h| {
        let c = eq_step(p, s.na, nz, "cong", &[h[0]]);
        let e = eval(p, nz, s.z);
        let to_na = trans(p, &[c, e]);
        let zn = symm(p, to_na);
        Some(trans(p, &[h[1], h[0], zn]))
    })?);
    let nsa = not(p, s.sa);
    facts.push(under(p, &[at.az], nsa, |p, h| {
        sign_of_ground(p, s.sa, h[0])
    })?);
    facts.push(under(p, &[at.az], at.pz, |p, h| {
        zero_product(p, s, s.pp, 0, h[0])
    })?);
    facts.push(under(p, &[at.xaz], at.lz, |p, h| {
        zero_product(p, s, s.lo, 0, h[0])
    })?);
    facts.push(under(p, &[at.xbz], at.lz, |p, h| {
        zero_product(p, s, s.lo, 1, h[0])
    })?);
    facts.push(under(p, &[at.pz, at.lop], at.lz, |p, h| {
        Some(trans(p, &[h[1], h[0]]))
    })?);
    facts.push(under(p, &[at.pz, at.lonp], at.lz, |p, h| {
        let c = eq_step(p, s.np, nz, "cong", &[h[0]]);
        let e = eval(p, nz, s.z);
        Some(trans(p, &[h[1], c, e]))
    })?);
    facts.push(under(p, &[at.pz, at.lonp], at.lop, |p, h| {
        let c = eq_step(p, s.np, nz, "cong", &[h[0]]);
        let e = eval(p, nz, s.z);
        let hs = symm(p, h[0]);
        Some(trans(p, &[h[1], c, e, hs]))
    })?);
    Some(())
}

/// The overflow side: the magnitude product against the limit by the
/// product's sign bit, `B = 0` is not `B = -1`, and `MIN * -1` overflows.
fn overflow(p: &mut Proof, s: &Signed, at: &Atoms, facts: &mut Vec<S>) -> Option<()> {
    let (nlz, novl) = (not(p, at.lz), not(p, s.ovl));
    let (nlop, nlonp) = (not(p, at.lop), not(p, at.lonp));
    let (nmax, nmin) = (not(p, at.limmax), not(p, at.limmin));
    let (np0, np1) = (not(p, s.p0), not(p, s.p1));
    let nbneg1 = not(p, s.bneg1);
    for cl in [
        vec![nlz, novl],
        vec![nlop, np0, nmax, novl],
        vec![nlonp, np1, nmin, novl],
        vec![nlop, np1, nmax, s.ovl],
        vec![nlonp, np0, at.pz, nmin, s.ovl],
    ] {
        facts.push(bitfact(p, &[], &cl)?);
    }
    facts.push(under(p, &[s.bz], nbneg1, |p, h| {
        let other = p.t.eq(s.z, s.neg1);
        let c = eq_step(p, s.bneg1, other, "cong", &[h[0]]);
        let ff = p.t.ff;
        let e = eval(p, other, ff);
        let bf = trans(p, &[c, e]);
        let be = p.unit(bf);
        let mut prem = p.gate(be);
        prem.extend(p.gate(ff));
        prem.push(Prem::Step(bf));
        p.derive(&[nbneg1], &prem, &[])
    })?);
    facts.push(spec_overflows(p, s)?);
    Some(())
}

/// The `bvsdiv` case taken, and its result against `A`.
fn case_taken(p: &mut Proof, s: &Signed, at: &Atoms, facts: &mut Vec<S>) -> Option<()> {
    let paths: [Vec<(usize, bool)>; 4] = [
        vec![(0, true)],
        vec![(0, false), (1, true)],
        vec![(0, false), (1, false), (2, true)],
        vec![(0, false), (1, false), (2, false)],
    ];
    for (k, path) in paths.iter().enumerate() {
        let conds: Vec<T> = path.iter().map(|&(i, v)| lit(p, s.c[i], v)).collect();
        let to_res = |p: &mut Proof, hs: &[S]| -> Option<S> {
            let mut chain = Vec::new();
            for (j, &(i, _)) in path.iter().enumerate() {
                chain.push(branch(p, s.ites[i], hs[j])?);
            }
            Some(trans(p, &chain))
        };
        let mut hyps = conds.clone();
        hyps.push(s.sda);
        facts.push(under(p, &hyps, at.sk[k], |p, hs| {
            let e = to_res(p, hs)?;
            let es = symm(p, e);
            Some(trans(p, &[es, hs[hs.len() - 1]]))
        })?);
        let mut hyps = conds;
        hyps.push(at.sk[k]);
        facts.push(under(p, &hyps, s.sda, |p, hs| {
            let e = to_res(p, hs)?;
            Some(trans(p, &[e, hs[hs.len() - 1]]))
        })?);
    }
    Some(())
}
