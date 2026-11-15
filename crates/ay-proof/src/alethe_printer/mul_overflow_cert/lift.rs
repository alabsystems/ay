// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A narrow limb product lifted to the wide ring. For `m`-bit `x, y`, one
//! Horner stage of `V_j = X * (y >> j)` (in `2m` bits) relates
//! `(concat 0 V_j)` to `W_j = ZX * Z(y >> j)` (in `4m` bits) and bounds
//! `V_j <= (2^m - 1)(2^(m-j) - 1)`, so the narrow product never wraps.

use super::bits;
use super::helpers::{eq_step, forall_lemma, instantiate, lincomb, project, split_or, symm, trans};
use super::horner::{and_from, bit_times, body_from_clause, ground};
use super::lin::{lin1, lin_prove, LinOpts};
use super::proof::{Prem, Proof, S};
use super::term::{Sort, T};

pub(crate) struct Words {
    pub(crate) x128: T,
    pub(crate) yd: T,
    pub(crate) ydp: T,
    pub(crate) zx: T,
    pub(crate) zyd: T,
    pub(crate) zydp: T,
}

pub(crate) struct Lift {
    m: u32,
    x: Vec<T>,
    e: Vec<T>,
    c: T,
    body: T,
    fact: S,
}

fn words(p: &mut Proof, m: u32, x: &[T], e: &[T]) -> Words {
    let (n, nn, ff) = (2 * m, 4 * m, p.t.ff);
    let mut xb = x.to_vec();
    xb.resize(n as usize, ff);
    let x128 = p.t.bb(&xb);
    let ew = p.t.bb(e);
    let mut ep: Vec<T> = e[1..].to_vec();
    ep.push(ff);
    let ewp = p.t.bb(&ep);
    let z1 = p.t.lit(bits::zero(n - m));
    let (yd, ydp) = (p.t.concat(&[z1, ew]), p.t.concat(&[z1, ewp]));
    xb.resize(nn as usize, ff);
    let zx = p.t.bb(&xb);
    let z2 = p.t.lit(bits::zero(nn - m));
    let (zyd, zydp) = (p.t.concat(&[z2, ew]), p.t.concat(&[z2, ewp]));
    Words {
        x128,
        yd,
        ydp,
        zx,
        zyd,
        zydp,
    }
}

fn zv(p: &mut Proof, m: u32, v: T) -> T {
    let z = p.t.lit(bits::zero(2 * m));
    p.t.concat(&[z, v])
}

/// `(and (= (concat 0 V) W) (not (bvult C V)))`.
fn inv(p: &mut Proof, m: u32, v: T, w: T, c: T) -> T {
    let z = zv(p, m, v);
    let e = p.t.eq(z, w);
    let u = p.t.ult(c, v);
    let nu = p.t.not(u);
    p.t.and(&[e, nu])
}

/// `(K, PREV, CUR)` of the stage with multiplicand bits `x` and suffix bits `e`.
fn shape(p: &mut Proof, m: u32, x: &[T], e: &[T], c: T, cp: T) -> (T, T, T) {
    let n = 2 * m;
    let w = words(p, m, x, e);
    let (v, vp) = (p.t.mul(w.x128, w.yd), p.t.mul(w.x128, w.ydp));
    let (ww, wp) = (p.t.mul(w.zx, w.zyd), p.t.mul(w.zx, w.zydp));
    let maxm = p.t.lit(bits::mask(m, n));
    let lim = p.t.lit(bits::add(
        &bits::add(&bits::pow2(n - 1, n), &bits::neg(&bits::pow2(m - 1, n))),
        &bits::from_u64(1, n),
    ));
    let sum = p.t.add(&[cp, cp, maxm]);
    let k1 = p.t.eq(c, sum);
    let k2 = p.t.ult(cp, lim);
    let k = p.t.and(&[k1, k2]);
    (k, inv(p, m, vp, wp, cp), inv(p, m, v, ww, c))
}

impl Lift {
    pub(crate) fn new(p: &mut Proof, m: u32, prefix: &str) -> Option<Self> {
        let n = 2 * m;
        let x: Vec<T> = (0..m)
            .map(|i| p.t.var(&format!("{prefix}x{i}"), Sort::Bool))
            .collect();
        let e: Vec<T> = (0..m)
            .map(|i| p.t.var(&format!("{prefix}e{i}"), Sort::Bool))
            .collect();
        let c = p.t.var(&format!("{prefix}C"), Sort::Bv(n));
        let cp = p.t.var(&format!("{prefix}Cp"), Sort::Bv(n));
        let (k, prev, cur) = shape(p, m, &x, &e, c, cp);
        let (nk, nprev) = (p.t.not(k), p.t.not(prev));
        let body = p.t.or(&[nk, nprev, cur]);
        let mut vars = x.clone();
        vars.extend(&e);
        vars.push(c);
        vars.push(cp);
        let mut lift = Lift {
            m,
            x,
            e,
            c,
            body,
            fact: 0,
        };
        let fact = forall_lemma(p, &vars, |p| Some((body, lift.prove(p, k, prev, cur)?)))?;
        lift.fact = fact;
        Some(lift)
    }

    fn prove(&self, p: &mut Proof, k: T, prev: T, cur: T) -> Option<S> {
        let m = self.m;
        let (n, nn) = (2 * m, 4 * m);
        let w = words(p, m, &self.x, &self.e);
        let (v, vp) = (p.t.mul(w.x128, w.yd), p.t.mul(w.x128, w.ydp));
        let (ww, wp) = (p.t.mul(w.zx, w.zyd), p.t.mul(w.zx, w.zydp));
        let sp = p.anchor(&[]);
        let ak = p.assume(k);
        let ap = p.assume(prev);
        let (k1, k2) = (project(p, ak, 0)?, project(p, ak, 1)?);
        let (ep, bp) = (project(p, ap, 0)?, project(p, ap, 1)?);
        let ff = p.t.ff;
        let mut ye0 = vec![self.e[0]];
        ye0.resize(n as usize, ff);
        let ye0 = p.t.bb(&ye0);
        let mut ze0 = vec![self.e[0]];
        ze0.resize(nn as usize, ff);
        let ze0 = p.t.bb(&ze0);
        let r1 = Self::decompose(p, w.yd, w.ydp, ye0, w.x128, v, vp)?;
        let r2 = Self::decompose(p, w.zyd, w.zydp, ze0, w.zx, ww, wp)?;
        let mut cases = Vec::new();
        for positive in [true, false] {
            let ca = p.anchor(&[]);
            let lit = if positive {
                self.e[0]
            } else {
                p.t.not(self.e[0])
            };
            let ae = p.assume(lit);
            let ctx = Case {
                ae,
                ye0,
                ze0,
                w: &w,
                v,
                vp,
                ww,
                wp,
                r1,
                r2,
                k1,
                k2,
                ep,
                bp,
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

    /// `(= V (bvadd V' V' (bvmul X e0word)))` from the bit decomposition of the suffix.
    fn decompose(p: &mut Proof, yd: T, ydp: T, e0w: T, x: T, v: T, vp: T) -> Option<S> {
        let sum = p.t.add(&[ydp, ydp, e0w]);
        let dec_t = p.t.eq(yd, sum);
        let dec = lin1(p, &[], dec_t, &LinOpts::default())?;
        let xs = p.t.mul(x, sum);
        let c1 = eq_step(p, v, xs, "cong", &[dec]);
        let v1 = p.t.mul(x, e0w);
        let rhs = p.t.add(&[vp, vp, v1]);
        let p1 = eq_step(p, xs, rhs, "poly_simp", &[]);
        Some(trans(p, &[c1, p1]))
    }

    fn case(&self, p: &mut Proof, c: &Case<'_>, positive: bool) -> Option<S> {
        let nn = 4 * self.m;
        let v1 = p.t.mul(c.w.x128, c.ye0);
        let w1 = p.t.mul(c.w.zx, c.ze0);
        let (v1s, v1r) = bit_times(p, self.e[0], positive, c.ae, c.ye0, v1)?;
        let (w1s, w1r) = bit_times(p, self.e[0], positive, c.ae, c.ze0, w1)?;
        let rv = Self::settle(p, c.vp, v1, v1r, v1s, c.r1, positive)?;
        let rw = Self::settle(p, c.wp, w1, w1r, w1s, c.r2, positive)?;
        let (zvv, zvp) = (zv(p, self.m, c.v), zv(p, self.m, c.vp));
        let rhs = if positive {
            p.t.add(&[zvp, zvp, c.w.zx])
        } else {
            p.t.add(&[zvp, zvp])
        };
        let tgt = p.t.eq(zvv, rhs);
        let bnd_t = {
            let u = p.t.ult(self.c, c.v);
            p.t.not(u)
        };
        let r = lin_prove(
            p,
            &[rv, c.bp, c.k1, c.k2],
            &[bnd_t, tgt],
            &LinOpts::default(),
        )?;
        let two = p.t.lit(bits::pow2(1, nn));
        let m1 = p.t.lit(bits::neg(&bits::from_u64(1, nn)));
        let eq = lincomb(
            p,
            zvv,
            c.ww,
            &[(r[1], None), (c.ep, Some(two)), (rw, Some(m1))],
        )?;
        and_from(p, c.cur, &[eq, r[0]])
    }

    /// `(= V (bvadd V' V' t))` (or without `t` when it is zero).
    fn settle(p: &mut Proof, vp: T, v1: T, v1r: T, v1s: S, r1: S, positive: bool) -> Option<S> {
        let a = p.t.add(&[vp, vp, v1]);
        let b = p.t.add(&[vp, vp, v1r]);
        let c = eq_step(p, a, b, "cong", &[v1s]);
        if positive {
            return Some(trans(p, &[r1, c]));
        }
        let d = p.t.add(&[vp, vp]);
        let ps = eq_step(p, b, d, "poly_simp", &[]);
        Some(trans(p, &[r1, c, ps]))
    }

    /// Run the Horner instances for `x * y`; returns the final invariant step and `(V_0, W_0)`.
    pub(crate) fn run(&self, p: &mut Proof, xb: &[T], yb: &[T]) -> Option<(S, T, T)> {
        let (m, ff) = (self.m, p.t.ff);
        let n = 2 * m;
        let cs = consts(m);
        let mut ebase = vec![yb[m as usize - 1]];
        ebase.resize(m as usize, ff);
        let (cm1, cm) = (
            p.t.lit(cs[m as usize - 1].clone()),
            p.t.lit(cs[m as usize].clone()),
        );
        let (_, prev, _) = shape(p, m, xb, &ebase, cm1, cm);
        let w = words(p, m, xb, &ebase);
        let mut fact = self.base(p, &w, prev, n)?;
        for j in (0..m as usize).rev() {
            let mut e: Vec<T> = yb[j..].to_vec();
            e.resize(m as usize, ff);
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
        let w = words(p, m, xb, yb);
        let (v0, w0) = (p.t.mul(w.x128, w.yd), p.t.mul(w.zx, w.zyd));
        Some((fact, v0, w0))
    }

    fn base(&self, p: &mut Proof, w: &Words, prev: T, n: u32) -> Option<S> {
        let nn = 2 * n;
        let (l0n, l0nn) = (p.t.lit(bits::zero(n)), p.t.lit(bits::zero(nn)));
        let (vp, wp) = (p.t.mul(w.x128, w.ydp), p.t.mul(w.zx, w.zydp));
        let k0 = eq_step(p, w.ydp, l0n, "evaluate", &[]);
        let k1 = eq_step(p, w.zydp, l0nn, "evaluate", &[]);
        let vz = zero_product(p, vp, w.x128, l0n, k0);
        let wz = zero_product(p, wp, w.zx, l0nn, k1);
        let (zvp, zl) = (zv(p, self.m, vp), zv(p, self.m, l0n));
        let zc = eq_step(p, zvp, zl, "cong", &[vz]);
        let ze = eq_step(p, zl, l0nn, "evaluate", &[]);
        let wzs = symm(p, wz);
        let e0 = trans(p, &[zc, ze, wzs]);
        let u = p.t.ult(l0n, vp);
        let u0 = p.t.ult(l0n, l0n);
        let cb = eq_step(p, u, u0, "cong", &[vz]);
        let ff = p.t.ff;
        let ev = eq_step(p, u0, ff, "evaluate", &[]);
        let nb = trans(p, &[cb, ev]);
        let nu = p.t.not(u);
        let ue = p.t.eq(u, ff);
        let mut prem = vec![Prem::Step(nb)];
        prem.extend(p.gate(ue));
        prem.extend(p.gate(ff));
        let b0 = p.derive(&[nu], &prem, &[])?;
        and_from(p, prev, &[e0, b0])
    }
}

/// `(= (bvmul x d) 0)` from `(= d 0)`.
fn zero_product(p: &mut Proof, prod: T, x: T, zero: T, dz: S) -> S {
    let xz = p.t.mul(x, zero);
    let a = eq_step(p, prod, xz, "cong", &[dz]);
    let b = eq_step(p, xz, zero, "poly_simp", &[]);
    trans(p, &[a, b])
}

/// The stage bounds `(2^m - 1)(2^(m-j) - 1)` for `j = 0..=m` at width `2m`.
fn consts(m: u32) -> Vec<Vec<bool>> {
    let n = 2 * m;
    let maxm = bits::mask(m, n);
    let mut c = vec![bits::zero(n); m as usize + 1];
    for j in (0..m as usize).rev() {
        let twice = bits::add(&c[j + 1], &c[j + 1]);
        c[j] = bits::add(&twice, &maxm);
    }
    c
}

struct Case<'a> {
    ae: S,
    ye0: T,
    ze0: T,
    w: &'a Words,
    v: T,
    vp: T,
    ww: T,
    wp: T,
    r1: S,
    r2: S,
    k1: S,
    k2: S,
    ep: S,
    bp: S,
    cur: T,
}
