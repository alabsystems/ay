// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Monotonicity and bound of a wide product, one multiplier bit per Horner
//! stage: for `U_j = ZX * Z(d >> j)` (operands `n` bits, ring `2n` bits),
//! `U_j <= (2^n - 1)(2^(n-j) - 1)` and `d >> j != 0 => U_j >= ZX`.

use super::bits;
use super::helpers::{eq_step, forall_lemma, instantiate, project, split_or, trans};
use super::horner::{and_from, bit_times, body_from_clause, ground};
use super::lin::{lin1, lin_prove, LinOpts};
use super::proof::{Prem, Proof, S};
use super::term::{Sort, T};

pub(crate) struct Mono {
    n: u32,
    x: Vec<T>,
    e: Vec<T>,
    c: T,
    body: T,
    fact: S,
}

struct W {
    zx: T,
    zd: T,
    zdp: T,
    zero: T,
}

fn words(p: &mut Proof<'_>, n: u32, x: &[T], e: &[T]) -> W {
    let ff = p.t.ff;
    let mut xb = x.to_vec();
    xb.resize(2 * n as usize, ff);
    let zx = p.t.bb(&xb);
    let zn = p.t.lit(bits::zero(n));
    let ew = p.t.bb(e);
    let mut ep: Vec<T> = e[1..].to_vec();
    ep.push(ff);
    let ewp = p.t.bb(&ep);
    let (zd, zdp) = (p.t.concat(&[zn, ew]), p.t.concat(&[zn, ewp]));
    let zero = p.t.bb(&vec![ff; 2 * n as usize]);
    W { zx, zd, zdp, zero }
}

/// `(and (not (bvult C U)) (or (= Zd ZERO) (not (bvult U ZX))))`.
fn inv(p: &mut Proof<'_>, w: &W, zd: T, c: T) -> T {
    let u = p.t.mul(w.zx, zd);
    let b = p.t.ult(c, u);
    let nb = p.t.not(b);
    let z = p.t.eq(zd, w.zero);
    let m = p.t.ult(u, w.zx);
    let nm = p.t.not(m);
    let o = p.t.or(&[z, nm]);
    p.t.and(&[nb, o])
}

fn shape(p: &mut Proof<'_>, n: u32, x: &[T], e: &[T], c: T, cp: T) -> (T, T, T) {
    let nn = 2 * n;
    let w = words(p, n, x, e);
    let maxl = p.t.lit(bits::mask(n, nn));
    let lim = p.t.lit(bits::add(
        &bits::add(&bits::pow2(nn - 1, nn), &bits::neg(&bits::pow2(n - 1, nn))),
        &bits::from_u64(1, nn),
    ));
    let sum = p.t.add(&[cp, cp, maxl]);
    let k1 = p.t.eq(c, sum);
    let k2 = p.t.ult(cp, lim);
    let k = p.t.and(&[k1, k2]);
    let (zdp, zd) = (w.zdp, w.zd);
    (k, inv(p, &w, zdp, cp), inv(p, &w, zd, c))
}

impl Mono {
    pub(crate) fn new(p: &mut Proof<'_>, n: u32, prefix: &str) -> Option<Self> {
        let nn = 2 * n;
        let x: Vec<T> = (0..n)
            .map(|i| p.t.var(&format!("{prefix}x{i}"), Sort::Bool))
            .collect();
        let e: Vec<T> = (0..n)
            .map(|i| p.t.var(&format!("{prefix}e{i}"), Sort::Bool))
            .collect();
        let c = p.t.var(&format!("{prefix}C"), Sort::Bv(nn));
        let cp = p.t.var(&format!("{prefix}Cp"), Sort::Bv(nn));
        let (k, prev, cur) = shape(p, n, &x, &e, c, cp);
        let (nk, np) = (p.t.not(k), p.t.not(prev));
        let body = p.t.or(&[nk, np, cur]);
        let mut vars = x.clone();
        vars.extend(&e);
        vars.push(c);
        vars.push(cp);
        let mut mono = Mono {
            n,
            x,
            e,
            c,
            body,
            fact: 0,
        };
        let fact = forall_lemma(p, &vars, |p| Some((body, mono.prove(p, k, prev, cur)?)))?;
        mono.fact = fact;
        Some(mono)
    }

    fn prove(&self, p: &mut Proof<'_>, k: T, prev: T, cur: T) -> Option<S> {
        let nn = 2 * self.n;
        let w = words(p, self.n, &self.x, &self.e);
        let (u, up) = (p.t.mul(w.zx, w.zd), p.t.mul(w.zx, w.zdp));
        let sp = p.anchor(&[]);
        let ak = p.assume(k);
        let ap = p.assume(prev);
        let (k1, k2) = (project(p, ak, 0)?, project(p, ak, 1)?);
        let (bp, mp) = (project(p, ap, 0)?, project(p, ap, 1)?);
        let ff = p.t.ff;
        let mut ze0 = vec![self.e[0]];
        ze0.resize(nn as usize, ff);
        let ze0 = p.t.bb(&ze0);
        let sum = p.t.add(&[w.zdp, w.zdp, ze0]);
        let dec_t = p.t.eq(w.zd, sum);
        let dec = lin1(p, &[], dec_t, &LinOpts::default())?;
        let xs = p.t.mul(w.zx, sum);
        let c1 = eq_step(p, u, xs, "cong", &[dec]);
        let v = p.t.mul(w.zx, ze0);
        let r1rhs = p.t.add(&[up, up, v]);
        let p1 = eq_step(p, xs, r1rhs, "poly_simp", &[]);
        let r1 = trans(p, &[c1, p1]);
        let mut cases = Vec::new();
        for positive in [true, false] {
            let ca = p.anchor(&[]);
            let lit = if positive {
                self.e[0]
            } else {
                p.t.not(self.e[0])
            };
            let ae = p.assume(lit);
            let (vs, vr) = bit_times(p, self.e[0], positive, ae, ze0, v)?;
            let a = p.t.add(&[up, up, v]);
            let b = p.t.add(&[up, up, vr]);
            let c = eq_step(p, a, b, "cong", &[vs]);
            let r2 = if positive {
                trans(p, &[r1, c])
            } else {
                let d = p.t.add(&[up, up]);
                let ps = eq_step(p, b, d, "poly_simp", &[]);
                trans(p, &[r1, c, ps])
            };
            let ctx = Ctx {
                u,
                up,
                w: &w,
                r2,
                bp,
                mp,
                k1,
                k2,
                ae,
                prev,
                cur,
            };
            self.case(p, &ctx, positive)?;
            let nl = p.t.not(lit);
            cases.push(p.close(ca, &[nl, cur], "subproof", &[ae]));
        }
        let prems: Vec<Prem> = cases.iter().map(|&s| Prem::Step(s)).collect();
        p.derive(&[cur], &prems, &[])?;
        let (nk, np) = (p.t.not(k), p.t.not(prev));
        let spc = p.close(sp, &[nk, np, cur], "subproof", &[ak, ap]);
        body_from_clause(p, self.body, spc)
    }

    fn case(&self, p: &mut Proof<'_>, c: &Ctx<'_>, positive: bool) -> Option<S> {
        let bnd_t = {
            let b = p.t.ult(self.c, c.u);
            p.t.not(b)
        };
        let mon_t = {
            let m = p.t.ult(c.u, c.w.zx);
            p.t.not(m)
        };
        let mono_or = p.t.args(c.cur)[1];
        let hyps = [c.r2, c.bp, c.k1, c.k2];
        let (bnd, mo) = if positive {
            let r = lin_prove(p, &hyps, &[bnd_t, mon_t], &LinOpts::default())?;
            let mut prem = p.gate(mono_or);
            prem.push(Prem::Step(r[1]));
            (r[0], p.derive(&[mono_or], &prem, &[])?)
        } else {
            let bnd = lin1(p, &hyps, bnd_t, &LinOpts::default())?;
            (bnd, self.mono_even(p, c, mon_t, mono_or)?)
        };
        and_from(p, c.cur, &[bnd, mo])
    }

    /// The even case: `Zd' = 0` makes `Zd = 0`; otherwise `U' >= ZX` and `U = 2U'`.
    fn mono_even(&self, p: &mut Proof<'_>, c: &Ctx<'_>, mon_t: T, mono_or: T) -> Option<S> {
        let zc = p.t.eq(c.w.zdp, c.w.zero);
        let s1 = p.anchor(&[]);
        let az = p.assume(zc);
        let zd0 = p.t.eq(c.w.zd, c.w.zero);
        let zz = lin1(p, &[az, c.ae], zd0, &LinOpts::default())?;
        let mut prem = p.gate(mono_or);
        prem.push(Prem::Step(zz));
        p.derive(&[mono_or], &prem, &[])?;
        let nzc = p.t.not(zc);
        let sc1 = p.close(s1, &[nzc, mono_or], "subproof", &[az]);
        let s2 = p.anchor(&[]);
        let anz = p.assume(nzc);
        let um = p.t.ult(c.up, c.w.zx);
        let num = p.t.not(um);
        let prev_or = p.t.args(c.prev)[1];
        let mut prem = p.gate(prev_or);
        prem.push(Prem::Step(c.mp));
        prem.push(Prem::Step(anz));
        let pm = p.derive(&[num], &prem, &[])?;
        let mon = lin1(p, &[c.r2, c.bp, c.k1, c.k2, pm], mon_t, &LinOpts::default())?;
        let mut prem = p.gate(mono_or);
        prem.push(Prem::Step(mon));
        p.derive(&[mono_or], &prem, &[])?;
        let nnzc = p.t.not(nzc);
        let sc2 = p.close(s2, &[nnzc, mono_or], "subproof", &[anz]);
        p.derive(&[mono_or], &[Prem::Step(sc1), Prem::Step(sc2)], &[])
    }

    /// Instances for multiplicand bits `xb` and multiplier bits `db`; returns the step
    /// for the final invariant over `U_0 = ZX * (concat 0 bb(db))`.
    pub(crate) fn run(&self, p: &mut Proof<'_>, xb: &[T], db: &[T]) -> Option<S> {
        let (n, ff) = (self.n, p.t.ff);
        let cs = consts(n);
        let mut ebase = vec![db[n as usize - 1]];
        ebase.resize(n as usize, ff);
        let (cn1, cn) = (
            p.t.lit(cs[n as usize - 1].clone()),
            p.t.lit(cs[n as usize].clone()),
        );
        let (_, prev, _) = shape(p, n, xb, &ebase, cn1, cn);
        let mut fact = self.base(p, xb, &ebase, prev)?;
        for j in (0..n as usize).rev() {
            let mut e: Vec<T> = db[j..].to_vec();
            e.resize(n as usize, ff);
            let mut args = xb.to_vec();
            args.extend(&e);
            args.push(p.t.lit(cs[j].clone()));
            args.push(p.t.lit(cs[j + 1].clone()));
            let inst = instantiate(p, self.fact, &args)?;
            let parts = split_or(p, inst);
            let kt = p.t.args(p.t.args(p.unit(inst))[0])[0];
            let kf = ground(p, kt)?;
            let curt = p.t.args(p.unit(inst))[2];
            fact = p.derive(
                &[curt],
                &[Prem::Step(parts), Prem::Step(kf), Prem::Step(fact)],
                &[],
            )?;
        }
        Some(fact)
    }

    fn base(&self, p: &mut Proof<'_>, xb: &[T], ebase: &[T], prev: T) -> Option<S> {
        let nn = 2 * self.n;
        let w = words(p, self.n, xb, ebase);
        let up = p.t.mul(w.zx, w.zdp);
        let l0 = p.t.lit(bits::zero(nn));
        let k0 = eq_step(p, w.zdp, l0, "evaluate", &[]);
        let xz = p.t.mul(w.zx, l0);
        let u0 = eq_step(p, up, xz, "cong", &[k0]);
        let u1 = eq_step(p, xz, l0, "poly_simp", &[]);
        let uz = trans(p, &[u0, u1]);
        let u = p.t.ult(l0, up);
        let uu = p.t.ult(l0, l0);
        let cb = eq_step(p, u, uu, "cong", &[uz]);
        let ff = p.t.ff;
        let ev = eq_step(p, uu, ff, "evaluate", &[]);
        let nb = trans(p, &[cb, ev]);
        let ue = p.t.eq(u, ff);
        let nu = p.t.not(u);
        let mut prem = vec![Prem::Step(nb)];
        prem.extend(p.gate(ue));
        prem.extend(p.gate(ff));
        let b1 = p.derive(&[nu], &prem, &[])?;
        let zc = p.t.eq(w.zdp, w.zero);
        let rz = ground(p, zc)?;
        let prev_or = p.t.args(prev)[1];
        let mut prem = p.gate(prev_or);
        prem.push(Prem::Step(rz));
        let b2 = p.derive(&[prev_or], &prem, &[])?;
        and_from(p, prev, &[b1, b2])
    }
}

/// `(2^n - 1)(2^(n-j) - 1)` at width `2n` for `j = 0..=n`.
fn consts(n: u32) -> Vec<Vec<bool>> {
    let nn = 2 * n;
    let maxl = bits::mask(n, nn);
    let mut c = vec![bits::zero(nn); n as usize + 1];
    for j in (0..n as usize).rev() {
        let twice = bits::add(&c[j + 1], &c[j + 1]);
        c[j] = bits::add(&twice, &maxl);
    }
    c
}

struct Ctx<'a> {
    u: T,
    up: T,
    w: &'a W,
    r2: S,
    bp: S,
    mp: S,
    k1: S,
    k2: S,
    ae: S,
    prev: T,
    cur: T,
}
