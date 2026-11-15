// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One level of the checker's restoring divider as a quantified lemma. Over
//! Boolean variables for the recursive result `(q', r')` of `x >> 1`, the
//! divisor bits and a quotient bound `C`, the stage preserves
//! `x = q*y + r` (exact, in twice the width), `r < y`, `r <= x` and `q <= C`.

use super::bits;
use super::clean::{udiv_stage, ult_bits, Stage};
use super::helpers::{eq_step, forall_lemma, lincomb, project, symm, trans, transfer, word_eq};
use super::horner::{and_from, body_from_clause};
use super::lin::{lin1, lin_prove, LinOpts};
use super::proof::{Prem, Proof, S};
use super::term::{Op, Sort, T};
use ay_core::kani_compat::DetHashSet as HashSet;

pub(crate) struct DivStage {
    pub(crate) n: u32,
    q2: Vec<T>,
    r2: Vec<T>,
    x: Vec<T>,
    y: Vec<T>,
    c: T,
    st: Stage,
    pub(crate) yz: T,
    k: T,
    invp: T,
    invc: T,
    body: T,
    pub(crate) fact: S,
}

/// `(concat 0 w)` at twice the width.
pub(crate) fn z(p: &mut Proof, n: u32, w: T) -> T {
    let zn = p.t.lit(bits::zero(n));
    p.t.concat(&[zn, w])
}

/// `(and (= (+ (* zQ zY) zR) zX) (bvult R Y) (not (bvult X R)) (not (bvult C Q)))`.
pub(crate) fn inv(p: &mut Proof, n: u32, q: &[T], r: &[T], x: &[T], y: &[T], c: T) -> T {
    let (qw, rw, xw, yw) = (p.t.bb(q), p.t.bb(r), p.t.bb(x), p.t.bb(y));
    let (zq, zy, zr, zx) = (z(p, n, qw), z(p, n, yw), z(p, n, rw), z(p, n, xw));
    let m = p.t.mul(zq, zy);
    let s = p.t.add(&[m, zr]);
    let e = p.t.eq(s, zx);
    let u = p.t.ult(rw, yw);
    let a = p.t.ult(xw, rw);
    let na = p.t.not(a);
    let b = p.t.ult(c, qw);
    let nb = p.t.not(b);
    p.t.and(&[e, u, na, nb])
}

pub(crate) fn shifted_x(p: &Proof, x: &[T]) -> Vec<T> {
    let mut v = x[1..].to_vec();
    v.push(p.t.ff);
    v
}

/// Defining clauses of every gate below `t` (to `depth` levels).
pub(crate) fn gates_rec(p: &mut Proof, t: T, depth: usize) -> Vec<Prem> {
    let mut out = Vec::new();
    let mut stack = vec![(t, 0usize)];
    let mut seen = HashSet::default();
    while let Some((u, d)) = stack.pop() {
        if d > depth || !seen.insert(u) {
            continue;
        }
        if p.t.is_gate(u) {
            out.extend(p.gate(u));
            for &a in p.t.args(u).to_vec().iter() {
                stack.push((a, d + 1));
            }
        } else if matches!(p.t.op(u), Op::Not) {
            stack.push((p.t.args(u)[0], d));
        } else if matches!(p.t.op(u), Op::True | Op::False) {
            out.extend(p.gate(u));
        }
    }
    out
}

impl DivStage {
    pub(crate) fn new(p: &mut Proof, n: u32, prefix: &str) -> Option<Self> {
        let mk = |p: &mut Proof, tag: &str| -> Vec<T> {
            (0..n)
                .map(|i| p.t.var(&format!("{prefix}{tag}{i}"), Sort::Bool))
                .collect()
        };
        let (q2, r2, x, y) = (mk(p, "q"), mk(p, "r"), mk(p, "x"), mk(p, "y"));
        let c = p.t.var(&format!("{prefix}C"), Sort::Bv(n));
        let cp = p.t.var(&format!("{prefix}Cp"), Sort::Bv(n));
        let st = udiv_stage(&mut p.t, &x, &y, &q2, &r2);
        let ff = p.t.ff;
        let yeqs: Vec<T> = y.iter().map(|&b| p.t.eq(b, ff)).collect();
        let yz = p.t.and(&yeqs);
        let one = p.t.lit(bits::from_u64(1, n));
        let half = p.t.lit(bits::pow2(n - 1, n));
        let sum = p.t.add(&[cp, cp, one]);
        let k1 = p.t.eq(c, sum);
        let k2 = p.t.ult(cp, half);
        let k = p.t.and(&[k1, k2]);
        let xs = shifted_x(p, &x);
        let invp = inv(p, n, &q2, &r2, &xs, &y, cp);
        let invc = inv(p, n, &st.quot, &st.rem, &x, &y, c);
        let nyz = p.t.not(yz);
        let (n1, nk, np) = (p.t.not(nyz), p.t.not(k), p.t.not(invp));
        let body = p.t.or(&[n1, nk, np, invc]);
        let mut vars = q2.clone();
        vars.extend(&r2);
        vars.extend(&x);
        vars.extend(&y);
        vars.push(c);
        vars.push(cp);
        let mut ds = DivStage {
            n,
            q2,
            r2,
            x,
            y,
            c,
            st,
            yz,
            k,
            invp,
            invc,
            body,
            fact: 0,
        };
        ds.fact = forall_lemma(p, &vars, |p| Some((body, ds.prove(p)?)))?;
        Some(ds)
    }
}

/// Facts shared by the three cases of one stage.
struct Common {
    ep: S,
    ultp: S,
    nultp: S,
    qbp: S,
    k1: S,
    k2: S,
    nq_top: S,
    nr_top: S,
    w2: S,
    w4: S,
    cut: Vec<T>,
}

impl DivStage {
    fn opts(&self, c: &Common) -> LinOpts {
        LinOpts {
            cut_extra: c.cut.clone(),
            ..LinOpts::default()
        }
    }

    fn words(&self, p: &mut Proof) -> (T, T, T, T, T, T, T) {
        let xs = shifted_x(p, &self.x);
        (
            p.t.bb(&self.q2),
            p.t.bb(&self.r2),
            p.t.bb(&self.y),
            p.t.bb(&xs),
            p.t.bb(&self.st.quot),
            p.t.bb(&self.st.rem),
            p.t.bb(&self.x),
        )
    }

    fn prove(&self, p: &mut Proof) -> Option<S> {
        let sp = p.anchor(&[]);
        let nyz = p.t.not(self.yz);
        let a1 = p.assume(nyz);
        let ak = p.assume(self.k);
        let a3 = p.assume(self.invp);
        let common = self.common(p, a3, ak)?;
        let mut cases = vec![self.case_xlt(p, &common)?];
        for co1 in [true, false] {
            cases.push(self.case_ge(p, &common, co1)?);
        }
        let prems: Vec<Prem> = cases.iter().map(|&s| Prem::Step(s)).collect();
        p.derive(&[self.invc], &prems, &[])?;
        let (n1, nk, np) = (p.t.not(nyz), p.t.not(self.k), p.t.not(self.invp));
        let spc = p.close(sp, &[n1, nk, np, self.invc], "subproof", &[a1, ak, a3]);
        body_from_clause(p, self.body, spc)
    }

    fn common(&self, p: &mut Proof, a3: S, ak: S) -> Option<Common> {
        let n = self.n;
        let (ep, ultp, nultp, qbp) = (
            project(p, a3, 0)?,
            project(p, a3, 1)?,
            project(p, a3, 2)?,
            project(p, a3, 3)?,
        );
        let (k1, k2) = (project(p, ak, 0)?, project(p, ak, 1)?);
        let mut cut = self.st.c_sa.clone();
        cut.extend(&self.st.c_my);
        cut.extend(&self.st.c_lt);
        let (qp, rp, _, xp, _, _, xw) = self.words(p);
        let mut c = Common {
            ep,
            ultp,
            nultp,
            qbp,
            k1,
            k2,
            nq_top: 0,
            nr_top: 0,
            w2: 0,
            w4: 0,
            cut,
        };
        // q'_{n-1} = F because Q' <= C' < 2^(n-1)
        let half = p.t.lit(bits::pow2(n - 1, n));
        let qh_t = p.t.ult(qp, half);
        let qh = lin1(p, &[qbp, k2], qh_t, &self.opts(&c))?;
        let hb = super::clean::const_bits(&p.t, &bits::pow2(n - 1, n));
        let ch = ult_bits(&mut p.t, &self.q2, &hb);
        let hw = p.t.bb(&hb);
        let qhw = p.t.ult(qp, hw);
        let kc = eq_step(p, half, hw, "bitblast_const", &[]);
        let cq = eq_step(p, qh_t, qhw, "cong", &[kc]);
        let bu = eq_step(p, qhw, ch[ch.len() - 1], "bitblast_ult", &[]);
        let qeq = trans(p, &[cq, bu]);
        let cf = transfer(p, qeq, qh)?;
        let mut prem = vec![Prem::Step(cf)];
        for &g in &ch {
            prem.extend(gates_rec(p, g, usize::MAX));
        }
        let (ff, tt) = (p.t.ff, p.t.tt);
        prem.extend(p.gate(ff));
        prem.extend(p.gate(tt));
        let nq = p.t.not(self.q2[n as usize - 1]);
        c.nq_top = p.derive(&[nq], &prem, &[])?;
        // r'_{n-1} = F because R' <= X' and the top bit of X' is false
        let xs = shifted_x(p, &self.x);
        let ch2 = ult_bits(&mut p.t, &xs, &self.r2);
        let u2 = p.t.ult(xp, rp);
        let bu2 = eq_step(p, u2, ch2[ch2.len() - 1], "bitblast_ult", &[]);
        let nb = transfer(p, bu2, nultp)?;
        let mut prem = gates_rec(p, ch2[ch2.len() - 1], 3);
        prem.push(Prem::Step(nb));
        prem.extend(p.gate(ff));
        prem.extend(p.gate(tt));
        let nr = p.t.not(self.r2[n as usize - 1]);
        c.nr_top = p.derive(&[nr], &prem, &[])?;
        let mut odd = vec![self.x[0]];
        odd.resize(n as usize, ff);
        let oddw = p.t.bb(&odd);
        let tw = p.t.bb(&self.st.r1sa);
        let (zx, zxp, zo, zt, zrp) = (
            z(p, n, xw),
            z(p, n, xp),
            z(p, n, oddw),
            z(p, n, tw),
            z(p, n, rp),
        );
        let s4 = p.t.add(&[zxp, zxp, zo]);
        let w4t = p.t.eq(zx, s4);
        c.w4 = lin1(p, &[], w4t, &self.opts(&c))?;
        let s2 = p.t.add(&[zrp, zrp, zo]);
        let w2t = p.t.eq(zt, s2);
        let mut o = self.opts(&c);
        o.extra_chains = vec![self.st.c_sa.clone()];
        c.w2 = lin1(p, &[c.nr_top], w2t, &o)?;
        Some(c)
    }

    fn bitfact(p: &mut Proof, target: T, gates: &[T], asm: &[S]) -> Option<S> {
        let mut prem = Vec::new();
        for &g in gates {
            prem.extend(p.gate(g));
        }
        prem.extend(asm.iter().map(|&s| Prem::Step(s)));
        p.derive(&[target], &prem, &[])
    }

    fn case_xlt(&self, p: &mut Proof, c: &Common) -> Option<S> {
        let n = self.n;
        let (ff, nn) = (p.t.ff, 2 * n);
        let (_, _, yw, _, qw, rw, xw) = self.words(p);
        let ca = p.anchor(&[]);
        let ax = p.assume(self.st.xlt);
        let mut qf = Vec::new();
        let mut rf = Vec::new();
        for i in 0..n as usize {
            let e = p.t.eq(self.st.quot[i], ff);
            qf.push(Self::bitfact(p, e, &[self.st.quot[i], e, ff], &[ax])?);
            let e = p.t.eq(self.st.rem[i], self.x[i]);
            rf.push(Self::bitfact(p, e, &[self.st.rem[i], e], &[ax])?);
        }
        let zero_n = p.t.bb(&vec![ff; n as usize]);
        let qz = word_eq(p, qw, zero_n, &qf)?;
        let rz = word_eq(p, rw, xw, &rf)?;
        let zn = p.t.lit(bits::zero(n));
        let k0 = eq_step(p, zn, zero_n, "bitblast_const", &[]);
        let k0s = symm(p, k0);
        let q0l = trans(p, &[qz, k0s]);
        let (zq, zzn, zr, zx, zy) = (
            z(p, n, qw),
            z(p, n, zn),
            z(p, n, rw),
            z(p, n, xw),
            z(p, n, yw),
        );
        let zqs = eq_step(p, zq, zzn, "cong", &[q0l]);
        let zrs = eq_step(p, zr, zx, "cong", &[rz]);
        let l0 = p.t.lit(bits::zero(nn));
        let zz = eq_step(p, zzn, l0, "evaluate", &[]);
        let zq2 = trans(p, &[zqs, zz]);
        let (m_l, m_r) = (p.t.mul(zq, zy), p.t.mul(l0, zy));
        let m1 = eq_step(p, m_l, m_r, "cong", &[zq2]);
        let (a_l, a_r) = (p.t.add(&[m_l, zr]), p.t.add(&[m_r, zx]));
        let m2 = eq_step(p, a_l, a_r, "cong", &[m1, zrs]);
        let m3 = eq_step(p, a_r, zx, "poly_simp", &[]);
        let ex = trans(p, &[m2, m3]);
        let t1 = p.t.ult(rw, yw);
        let t2 = {
            let u = p.t.ult(xw, rw);
            p.t.not(u)
        };
        let t3 = {
            let u = p.t.ult(self.c, qw);
            p.t.not(u)
        };
        let mut o = self.opts(c);
        o.params = vec![(self.st.xlt, ax)];
        o.extra_chains = vec![self.st.c_lt.clone()];
        let r = lin_prove(p, &[rz, q0l], &[t1, t2, t3], &o)?;
        and_from(p, self.invc, &[ex, r[0], r[1], r[2]])?;
        let nl = p.t.not(self.st.xlt);
        Some(p.close(ca, &[nl, self.invc], "subproof", &[ax]))
    }
}

impl DivStage {
    /// The case `x >= y`: the quotient doubles and takes `co1` as its new low bit.
    fn case_ge(&self, p: &mut Proof, c: &Common, co1: bool) -> Option<S> {
        let n = self.n;
        let nn = 2 * n;
        let (_, _, yw, _, qw, rw, xw) = self.words(p);
        let ca = p.anchor(&[]);
        let nx = p.t.not(self.st.xlt);
        let an = p.assume(nx);
        let col = if co1 {
            self.st.co1
        } else {
            p.t.not(self.st.co1)
        };
        let ac = p.assume(col);
        let (w1, qb) = self.quotient_ge(p, c, co1, an, ac)?;
        let zq = z(p, n, qw);
        let zy = z(p, n, yw);
        let target_bits = if co1 {
            self.st.rmy.clone()
        } else {
            self.st.r1sa.clone()
        };
        let mut rr = Vec::new();
        for i in 0..n as usize {
            let e = p.t.eq(self.st.rem[i], target_bits[i]);
            rr.push(Self::bitfact(
                p,
                e,
                &[self.st.rem[i], self.st.r1sa2[i], e],
                &[an, ac],
            )?);
        }
        let tw = p.t.bb(&self.st.r1sa);
        let (zr, zt, zx) = (z(p, n, rw), z(p, n, tw), z(p, n, xw));
        let params = vec![(nx, an), (col, ac)];
        let (rrm, w3) = if co1 {
            let rmw = p.t.bb(&self.st.rmy);
            let rrm = word_eq(p, rw, rmw, &rr)?;
            let s = p.t.add(&[zr, zy]);
            let w3t = p.t.eq(s, zt);
            let mut o = self.opts(c);
            o.params = params.clone();
            o.extra_chains = vec![self.st.c_my.clone()];
            (rrm, lin1(p, &[rrm], w3t, &o)?)
        } else {
            let rrm = word_eq(p, rw, tw, &rr)?;
            (rrm, eq_step(p, zr, zt, "cong", &[rrm]))
        };
        let lhs = {
            let m = p.t.mul(zq, zy);
            p.t.add(&[m, zr])
        };
        let two = p.t.lit(bits::pow2(1, nn));
        let m1 = p.t.lit(bits::neg(&bits::from_u64(1, nn)));
        let eq = lincomb(
            p,
            lhs,
            zx,
            &[
                (w1, Some(zy)),
                (w3, None),
                (c.w2, None),
                (c.ep, Some(two)),
                (c.w4, Some(m1)),
            ],
        )?;
        let t1 = p.t.ult(rw, yw);
        let t2 = {
            let u = p.t.ult(xw, rw);
            p.t.not(u)
        };
        let mut o = self.opts(c);
        o.params = params;
        o.extra_chains = vec![self.st.c_my.clone(), self.st.c_sa.clone()];
        let hyps = if co1 {
            vec![rrm, c.ultp, c.nultp, c.nr_top]
        } else {
            vec![rrm, c.nultp]
        };
        let r = lin_prove(p, &hyps, &[t1, t2], &o)?;
        and_from(p, self.invc, &[eq, r[0], r[1], qb])?;
        let (n1, n2) = (p.t.not(nx), p.t.not(col));
        Some(p.close(ca, &[n1, n2, self.invc], "subproof", &[an, ac]))
    }

    /// The quotient half of [`Self::case_ge`]: `Q = 2 Q' + co1` (at `n` bits
    /// and zero-extended to `2n`) and the bound `Q <= C`.
    fn quotient_ge(&self, p: &mut Proof, c: &Common, co1: bool, an: S, ac: S) -> Option<(S, S)> {
        let n = self.n;
        let nn = 2 * n;
        let (ff, tt) = (p.t.ff, p.t.tt);
        let (qp, _, _, _, qw, _, _) = self.words(p);
        let bit0 = if co1 { tt } else { ff };
        let e0 = p.t.eq(self.st.quot[0], bit0);
        let mut qif = vec![Self::bitfact(
            p,
            e0,
            &[self.st.quot[0], self.st.q1_0, e0, tt, ff],
            &[an, ac],
        )?];
        for i in 1..n as usize {
            let e = p.t.eq(self.st.quot[i], self.q2[i - 1]);
            qif.push(Self::bitfact(p, e, &[self.st.quot[i], e], &[an])?);
        }
        let mut qsh = vec![bit0];
        qsh.extend(&self.q2[..n as usize - 1]);
        let qshw = p.t.bb(&qsh);
        let qq = word_eq(p, qw, qshw, &qif)?;
        let one_n = p.t.lit(bits::from_u64(1, n));
        let one_nn = p.t.lit(bits::from_u64(1, nn));
        let (zq, zqp) = (z(p, n, qw), z(p, n, qp));
        let (w1n_r, w1_r) = if co1 {
            (p.t.add(&[qp, qp, one_n]), p.t.add(&[zqp, zqp, one_nn]))
        } else {
            (p.t.add(&[qp, qp]), p.t.add(&[zqp, zqp]))
        };
        let (w1n_t, w1_t) = (p.t.eq(qw, w1n_r), p.t.eq(zq, w1_r));
        let w = lin_prove(p, &[qq, c.nq_top], &[w1n_t, w1_t], &self.opts(c))?;
        let qb_t = {
            let u = p.t.ult(self.c, qw);
            p.t.not(u)
        };
        let qb = lin1(p, &[w[0], c.qbp, c.k1, c.k2], qb_t, &self.opts(c))?;
        Some((w[1], qb))
    }
}
