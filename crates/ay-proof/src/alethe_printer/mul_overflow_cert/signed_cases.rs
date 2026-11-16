// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The signed row's facts about the `bvsdiv` cases: `MIN * -1` overflows,
//! each case's quotient against the unsigned core's, and the cases whose
//! quotient cannot be `A` (the product's top bit disagrees with the
//! operands' signs), read off the division lemma's top-bit conjunct.

use super::div_lemma::{top_set, zero_test, DivLemma};
use super::helpers::{conjoin, eq_step, project, symm, trans};
use super::local::{bitfact, bitfact_with, branch, under};
use super::proof::{Prem, Proof, S};
use super::row::Row;
use super::signed::Signed;
use super::signed_facts::Atoms;
use super::signed_ground::{eval, not};
use super::term::{Op, T};

/// `(cl (not amin) (not bneg1) ovl)`: `MIN * -1` overflows, by evaluation
/// once both operands and the limit are known.
pub(super) fn spec_overflows(p: &mut Proof<'_>, s: &Signed) -> Option<S> {
    under(p, &[s.amin, s.bneg1], s.ovl, |p, h| {
        let sa = bitfact(p, &[h[0]], &[s.sa])?;
        let sb = bitfact(p, &[h[1]], &[s.sb])?;
        let xan = branch(p, s.xa, sa)?;
        let nmin = p.t.neg(s.minw);
        let c1 = eq_step(p, s.na, nmin, "cong", &[h[0]]);
        let e1 = eval(p, nmin, s.minw);
        let xam = trans(p, &[xan, c1, e1]);
        let xbn = branch(p, s.xb, sb)?;
        let nneg1 = p.t.neg(s.neg1);
        let c2 = eq_step(p, s.nb, nneg1, "cong", &[h[1]]);
        let e2 = eval(p, nneg1, s.one);
        let xbo = trans(p, &[xbn, c2, e2]);
        let mut prem = p.gate(s.ss);
        prem.push(Prem::Step(sa));
        prem.push(Prem::Step(sb));
        let ssf = p.derive(&[s.ss], &prem, &[])?;
        let limm = branch(p, s.lim, ssf)?;
        let mo = p.t.mul(s.minw, s.one);
        let lom = eq_step(p, s.lo, mo, "cong", &[xam, xbo]);
        let u = p.t.ult(s.maxw, mo);
        let c3 = eq_step(p, s.ovl, u, "cong", &[limm, lom]);
        let tt = p.t.tt;
        let e3 = eval(p, u, tt);
        let ot = trans(p, &[c3, e3]);
        let te = p.unit(ot);
        let mut prem = p.gate(te);
        prem.extend(p.gate(tt));
        prem.push(Prem::Step(ot));
        p.derive(&[s.ovl], &prem, &[])
    })
}

/// Each case's quotient is the core's quotient when its dividend is the
/// wrapped magnitude product and its divisor `|B|`; and against `|A|`.
pub(super) fn quotients(
    p: &mut Proof<'_>,
    s: &Signed,
    row: &Row,
    at: &Atoms,
    wa: S,
    wp: S,
    facts: &mut Vec<S>,
) -> Option<()> {
    let nazt = not(p, row.az);
    for k in 0..4 {
        let (lo_atom, xb_atom) = (
            if k % 2 == 0 { at.lop } else { at.lonp },
            if k < 2 { at.xbb } else { at.xbn },
        );
        let qk = s.q[k];
        facts.push(under(
            p,
            &[lo_atom, at.db, xb_atom, nazt],
            at.eqk[k],
            |p, h| {
                let xl = symm(p, h[0]);
                let wps = symm(p, wp);
                let xe = trans(p, &[xl, wps]);
                let ye0 = if k < 2 {
                    h[1]
                } else {
                    let nb = p.t.neg(s.b);
                    eq_step(p, s.nd, nb, "cong", &[h[1]])
                };
                let ye1 = symm(p, h[2]);
                let ye2 = symm(p, wa);
                let apb = branch(p, row.ap, h[3])?;
                let ye3 = symm(p, apb);
                let ye = trans(p, &[ye0, ye1, ye2, ye3]);
                Some(eq_step(p, qk, row.q, "cong", &[xe, ye]))
            },
        )?);
        let negated = k == 1 || k == 2;
        let xa_atom = if negated { at.xan } else { at.xaa };
        let res = s.res[k];
        facts.push(under(
            p,
            &[at.eqk[k], xa_atom, at.sk[k]],
            at.qbx,
            |p, h| {
                let e1 = symm(p, h[0]);
                if !negated {
                    let xs = symm(p, h[1]);
                    return Some(trans(p, &[e1, h[2], xs]));
                }
                let nn = p.t.neg(res);
                let e2 = eq_step(p, qk, nn, "poly_simp", &[]);
                let e3 = eq_step(p, nn, s.na, "cong", &[h[2]]);
                let e4 = symm(p, h[1]);
                Some(trans(p, &[e1, e2, e3, e4]))
            },
        )?);
        facts.push(under(
            p,
            &[at.eqk[k], xa_atom, at.qbx],
            at.sk[k],
            |p, h| {
                if !negated {
                    return Some(trans(p, &[h[0], h[2], h[1]]));
                }
                let nq = p.t.neg(row.q);
                let nx = p.t.neg(s.xa);
                let nna = p.t.neg(s.na);
                let e1 = eq_step(p, res, nq, "cong", &[h[0]]);
                let e2 = eq_step(p, nq, nx, "cong", &[h[2]]);
                let e3 = eq_step(p, nx, nna, "cong", &[h[1]]);
                let e4 = eq_step(p, nna, s.a, "poly_simp", &[]);
                Some(trans(p, &[e1, e2, e3, e4]))
            },
        )?);
    }
    Some(())
}

/// The division lemma's instance at each `bvsdiv` case's `bvudiv`, and the
/// literals the contradictions share.
struct Tops {
    /// The dividend and divisor of each case's `bvudiv`.
    pairs: [(T, T); 4],
    /// Each instance split into `(cl (not (not YZ)) (and E U TOP ZERO))`.
    split: Vec<S>,
    /// Each instance's `(and YONE XT)`.
    both: Vec<T>,
    /// `(= ((_ extract n-1 n-1) q_k) #b1)`.
    qtop: Vec<T>,
    nsa: T,
    naz: T,
    ndz: T,
    nndz: T,
    /// `(not (= case_k A))`.
    nsk: Vec<T>,
}

impl Tops {
    fn new(p: &mut Proof<'_>, s: &Signed, at: &Atoms, dl: &DivLemma) -> Option<Self> {
        let pairs = [(s.pp, s.d), (s.np, s.d), (s.pp, s.nd), (s.np, s.nd)];
        let mut split = Vec::new();
        let mut both = Vec::new();
        for &(x, y) in &pairs {
            let sp = dl.split_instance(p, x, y)?;
            let conj = *p.clause(sp).last()?;
            let top = p.t.args(conj)[2];
            both.push(p.t.args(top)[1]);
            split.push(sp);
        }
        let qtop: Vec<T> = s.q.iter().map(|&q| top_set(p, q)).collect();
        let (nsa, naz) = (not(p, s.sa), not(p, at.az));
        let (ndz, nndz) = (not(p, at.dz), not(p, at.ndz));
        let nsk: Vec<T> = at.sk.iter().map(|&x| p.t.not(x)).collect();
        Some(Tops {
            pairs,
            split,
            both,
            qtop,
            nsa,
            naz,
            ndz,
            nndz,
            nsk,
        })
    }

    /// `(cl BOTH_k)` from the top bit of `q_k` (the step `top`) and the
    /// divisor's word disequality (the step `nz`).
    fn both_from(&self, p: &mut Proof<'_>, k: usize, top: S, nz: S) -> Option<S> {
        let y = self.pairs[k].1;
        let yz = zero_test(p, y);
        let nyz = p.t.not(yz);
        let nzb = bitfact_with(p, &[nz], &[nyz], &[y])?;
        let [_, _, topc, _] = DivLemma::conjuncts(p, self.split[k], nzb)?;
        let top_or = p.unit(topc);
        let mut prem = p.gate(top_or);
        prem.push(Prem::Step(topc));
        prem.push(Prem::Step(top));
        p.derive(&[self.both[k]], &prem, &[])
    }
}

/// The cases whose quotient cannot be `A` (the product's top bit disagrees
/// with the operands' signs), through the division lemma's top-bit conjunct.
pub(super) fn contradictions(
    p: &mut Proof<'_>,
    s: &Signed,
    at: &Atoms,
    dl: &DivLemma,
    not_both_p: S,
    facts: &mut Vec<S>,
) -> Option<()> {
    let tp = Tops::new(p, s, at, dl)?;
    // k = 0: positive A, nonnegative product: the quotient's top bit would need P[n-1].
    let f0 = under(p, &[s.sa, s.p0, tp.ndz], tp.nsk[0], |p, h| {
        let inner = under(p, &[at.sk[0]], s.p1, |p, h2| {
            let top = bitfact(p, &[h2[0], h[0]], &[tp.qtop[0]])?;
            let b = tp.both_from(p, 0, top, h[2])?;
            project(p, b, 1)
        })?;
        p.derive(
            &[tp.nsk[0]],
            &[Prem::Step(inner), Prem::Step(h[1]), Prem::Step(not_both_p)],
            &[],
        )
    })?;
    facts.push(f0);
    // k = 2: the same through `-D`.
    let f2 = under(p, &[tp.nsa, tp.naz, s.p0, tp.nndz], tp.nsk[2], |p, h| {
        let inner = under(p, &[at.sk[2]], s.p1, |p, h2| {
            let top = bitfact(p, &[h2[0], h[0], h[1]], &[tp.qtop[2]])?;
            let b = tp.both_from(p, 2, top, h[3])?;
            project(p, b, 1)
        })?;
        p.derive(
            &[tp.nsk[2]],
            &[Prem::Step(inner), Prem::Step(h[2]), Prem::Step(not_both_p)],
            &[],
        )
    })?;
    facts.push(f2);
    min_cases(p, s, at, &tp, facts)
}

/// The cases whose dividend is `-P` (k = 1, 3): a set top quotient bit takes
/// a divisor of one and a dividend of `MIN`, so the case gives back `MIN`.
/// For k = 1 that sets `A`'s clear sign bit; for k = 3 it makes `A = MIN`
/// and, through `-D = 1`, `B = D = -1`, the excluded case.
fn min_cases(
    p: &mut Proof<'_>,
    s: &Signed,
    at: &Atoms,
    tp: &Tops,
    facts: &mut Vec<S>,
) -> Option<()> {
    let nmin = p.t.neg(s.minw);
    let ppmin = p.t.eq(s.pp, s.minw);
    let qmin = p.t.mk(Op::Udiv, &[nmin, s.one]);
    let f1 = under(p, &[tp.nsa, tp.naz, s.p1, tp.ndz], tp.nsk[1], |p, h| {
        let inner = under(p, &[at.sk[1]], s.sa, |p, h2| {
            let top = bitfact(p, &[h2[0], h[0], h[1]], &[tp.qtop[1]])?;
            let b = tp.both_from(p, 1, top, h[3])?;
            let done = project(p, b, 0)?;
            let npt = project(p, b, 1)?;
            let pm = bitfact(p, &[h[2], npt], &[ppmin])?;
            let npm = eq_step(p, s.np, nmin, "cong", &[pm]);
            let e1 = eq_step(p, s.q[1], qmin, "cong", &[npm, done]);
            let e2 = eval(p, qmin, s.minw);
            let qm = trans(p, &[e1, e2]);
            let a1 = symm(p, h2[0]);
            let a2 = eq_step(p, s.res[1], nmin, "cong", &[qm]);
            let a3 = eval(p, nmin, s.minw);
            let am = trans(p, &[a1, a2, a3]);
            bitfact(p, &[am], &[s.sa])
        })?;
        p.derive(&[tp.nsk[1]], &[Prem::Step(inner), Prem::Step(h[0])], &[])
    })?;
    facts.push(f1);
    let neg_one = p.t.neg(s.one);
    let nnd = p.t.neg(s.nd);
    let qmin3 = p.t.mk(Op::Udiv, &[nmin, s.one]);
    let f3 = under(
        p,
        &[s.sa, s.p1, tp.nndz, at.db, at.sk[3]],
        s.spec,
        |p, h| {
            let top = bitfact(p, &[h[4], h[0]], &[tp.qtop[3]])?;
            let b = tp.both_from(p, 3, top, h[2])?;
            let done = project(p, b, 0)?;
            let npt = project(p, b, 1)?;
            let pm = bitfact(p, &[h[1], npt], &[ppmin])?;
            let npm = eq_step(p, s.np, nmin, "cong", &[pm]);
            let e1 = eq_step(p, s.q[3], qmin3, "cong", &[npm, done]);
            let e2 = eval(p, qmin3, s.minw);
            let a1 = symm(p, h[4]);
            let am = trans(p, &[a1, e1, e2]);
            let b1 = symm(p, h[3]);
            let b2 = eq_step(p, s.d, nnd, "poly_simp", &[]);
            let b3 = eq_step(p, nnd, neg_one, "cong", &[done]);
            let b4 = eval(p, neg_one, s.neg1);
            let bm = trans(p, &[b1, b2, b3, b4]);
            conjoin(p, s.spec, &[am, bm])
        },
    )?;
    facts.push(f3);
    Some(())
}
