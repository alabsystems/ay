// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (F3) `(not az), hz => qb`: with no high half the product is exact, and the
//! quotient differs from `B` by `D` only if `A * D` (at least `A`, at most
//! `(2^n - 1)^2`) equals the remainder (below `A`) or its negation.

use super::assembly::{Asm, Ds};
use super::div::z;
use super::helpers::{eq_step, lincomb, project, symm, trans, transfer, word_eq};
use super::lin::{lin1, tri_eq, LinOpts};
use super::lin_bits::bit_facts;
use super::proof::{Prem, Proof, S};
use super::school::{lit_minus1, lit_pow};
use super::term::T;

pub(crate) struct F3<'b> {
    ds: &'b Ds,
    sp: S,
    e0pp: S,
    u0: S,
    dt: T,
    dw: T,
    zd: T,
    vd: S,
    u0t: T,
    mo: S,
    bnd: S,
    cur: T,
    lt: T,
}

impl<'a> Asm<'a> {
    pub(crate) fn f3(&self, p: &mut Proof, ds: &Ds) -> Option<S> {
        let r = &self.c.row;
        let (n, nn) = (r.n(), 4 * r.m);
        let a = p.anchor(&[]);
        let naz = p.t.not(r.az);
        let hn = p.assume(naz);
        let hh = p.assume(r.hz);
        let (ya, apa) = self.ap_eq_a(p, ds, hn)?;
        let wh = {
            let b = p.t.bits(r.h);
            p.t.bb(&b)
        };
        let vhs = symm(p, self.vh);
        let hw = trans(p, &[vhs, hh, self.sz]);
        let mut bf = bit_facts(p, hw)?;
        bf.resize(nn as usize, self.refl);
        let zero = p.t.args(p.unit(self.k0))[1];
        let zh0 = word_eq(p, self.sc.zh, zero, &bf)?;
        let k0s = symm(p, self.k0);
        let ezh = trans(p, &[zh0, k0s]);
        let _ = wh;
        let lhs = p.t.mul(self.c.za, self.c.zb);
        let cn = lit_pow(p, n, nn);
        let sp = lincomb(p, lhs, self.sc.zp, &[(self.sc.s, None), (ezh, Some(cn))])?;
        let (m_l, m_r) = (p.t.mul(ds.zq0, ds.zyp), p.t.mul(ds.zq0, self.c.za));
        let c1 = eq_step(p, m_l, m_r, "cong", &[ya]);
        let (a_l, a_r) = (p.t.add(&[m_l, ds.zr0]), p.t.add(&[m_r, ds.zr0]));
        let c2 = eq_step(p, a_l, a_r, "cong", &[c1]);
        let c2s = symm(p, c2);
        let e0pp = trans(p, &[c2s, ds.e0]);
        let (u1, u2) = (p.t.ult(ds.r0w, ds.yw), p.t.ult(ds.r0w, self.a128));
        let cu = eq_step(p, u1, u2, "cong", &[apa]);
        let u0 = transfer(p, cu, ds.u0)?;
        let lt = p.t.ult(ds.q0w, self.b128);
        let gt = p.t.ult(self.b128, ds.q0w);
        let (sub1, sub2) = (p.t.sub(self.b128, ds.q0w), p.t.sub(ds.q0w, self.b128));
        let dt = p.t.ite(lt, sub1, sub2);
        let dw = {
            let b = p.t.bits(dt);
            p.t.bb(&b)
        };
        let zd = z(p, n, dw);
        let vd = eq_step(p, dt, dw, "bitblast_var", &[]);
        let db = p.t.bits(dt);
        let cur = self.mono_run(p, &db)?;
        let curt = p.unit(cur);
        let u0t = p.t.mul(self.c.za, zd);
        let mo = project(p, cur, 1)?;
        let bnd = project(p, cur, 0)?;
        let f = F3 {
            ds,
            sp,
            e0pp,
            u0,
            dt,
            dw,
            zd,
            vd,
            u0t,
            mo,
            bnd,
            cur: curt,
            lt,
        };
        let s_lt = p.anchor(&[]);
        let hlt = p.assume(lt);
        self.mono_case(p, &f, hlt, true, hlt)?;
        let nlt = p.t.not(lt);
        let c_lt = p.close(s_lt, &[nlt, r.qb], "subproof", &[hlt]);
        let s_nlt = p.anchor(&[]);
        let hnlt = p.assume(nlt);
        let s_gt = p.anchor(&[]);
        let hgt = p.assume(gt);
        self.mono_case(p, &f, hgt, false, hnlt)?;
        let ngt = p.t.not(gt);
        let c_gt = p.close(s_gt, &[ngt, r.qb], "subproof", &[hgt]);
        let s_eq = p.anchor(&[]);
        let hngt = p.assume(ngt);
        let eqq = tri_eq(p, ds.q0w, self.b128, hnlt, hngt)?;
        let sbs = symm(p, self.sb);
        trans(p, &[ds.uq, eqq, sbs]);
        let nngt = p.t.not(ngt);
        let c_eq = p.close(s_eq, &[nngt, r.qb], "subproof", &[hngt]);
        p.derive(&[r.qb], &[Prem::Step(c_gt), Prem::Step(c_eq)], &[])?;
        let nnlt = p.t.not(nlt);
        let c_nlt = p.close(s_nlt, &[nnlt, r.qb], "subproof", &[hnlt]);
        p.derive(&[r.qb], &[Prem::Step(c_lt), Prem::Step(c_nlt)], &[])?;
        let (n1, n2) = (p.t.not(naz), p.t.not(r.hz));
        Some(p.close(a, &[n1, n2, r.qb], "subproof", &[hn, hh]))
    }

    fn mono_case(
        &self,
        p: &mut Proof,
        f: &F3<'_>,
        asm: S,
        lt_holds: bool,
        lt_fact: S,
    ) -> Option<S> {
        let r = &self.c.row;
        let nn = 4 * r.m;
        let cv = if lt_holds { p.t.tt } else { p.t.ff };
        let e = p.t.eq(f.lt, cv);
        let mut prem = p.gate(e);
        prem.extend(p.gate(cv));
        prem.push(Prem::Step(lt_fact));
        let ec = p.derive(&[e], &prem, &[])?;
        let (sub1, sub2) = (p.t.sub(self.b128, f.ds.q0w), p.t.sub(f.ds.q0w, self.b128));
        let sub = if lt_holds { sub1 } else { sub2 };
        let it = p.t.ite(cv, sub1, sub2);
        let d1 = eq_step(p, f.dt, it, "cong", &[ec]);
        let d2 = eq_step(p, it, sub, "ite_simplify", &[]);
        let dsub = trans(p, &[d1, d2]);
        let dss = symm(p, dsub);
        let subw = trans(p, &[dss, f.vd]);
        let (other, total) = if lt_holds {
            (f.ds.q0w, self.b128)
        } else {
            (self.b128, f.ds.q0w)
        };
        let so = p.t.add(&[sub, other]);
        let ps = eq_step(p, so, total, "poly_simp", &[]);
        let dwo = p.t.add(&[f.dw, other]);
        let cd = eq_step(p, so, dwo, "cong", &[subw]);
        let cds = symm(p, cd);
        let hd = trans(p, &[cds, ps]);
        let n = r.n();
        let (zo, zt) = if lt_holds {
            (f.ds.zq0, self.c.zb)
        } else {
            (self.c.zb, f.ds.zq0)
        };
        let s = p.t.add(&[f.zd, zo]);
        let det = p.t.eq(s, zt);
        let op = LinOpts {
            opaque_leaves: true,
            ..LinOpts::default()
        };
        let de = lin1(p, &[hd, asm], det, &op)?;
        let zero = p.t.args(p.unit(self.k0))[1];
        let zc = p.t.eq(f.zd, zero);
        let sa = p.anchor(&[]);
        let hz0 = p.assume(zc);
        let asm_lit = p.unit(asm);
        let nasm = p.t.not(asm_lit);
        lin1(p, &[hz0, de], nasm, &op)?;
        let nzc = p.t.not(zc);
        let sc = p.close(sa, &[nzc, nasm], "subproof", &[hz0]);
        let dnz = p.derive(&[nzc], &[Prem::Step(sc), Prem::Step(asm)], &[])?;
        let ug = p.t.ult(f.u0t, self.c.za);
        let nug = p.t.not(ug);
        let mono_or = p.t.args(f.cur)[1];
        let mut prem = p.gate(mono_or);
        prem.push(Prem::Step(f.mo));
        prem.push(Prem::Step(dnz));
        let ge = p.derive(&[nug], &prem, &[])?;
        let m1 = lit_minus1(p, nn);
        let rlt = p.t.ult(f.ds.r0w, self.a128);
        let nrlt = p.t.not(rlt);
        let nr = if lt_holds {
            let equ = lincomb(
                p,
                f.u0t,
                f.ds.zr0,
                &[(de, Some(self.c.za)), (f.sp, None), (f.e0pp, Some(m1))],
            )?;
            lin1(p, &[equ, ge], nrlt, &op)?
        } else {
            let l = p.t.add(&[f.u0t, f.ds.zr0]);
            let l0 = p.t.args(p.unit(self.k0))[0];
            let equ = lincomb(
                p,
                l,
                l0,
                &[(de, Some(self.c.za)), (f.sp, Some(m1)), (f.e0pp, None)],
            )?;
            lin1(p, &[equ, ge, f.bnd], nrlt, &op)?
        };
        let _ = n;
        p.derive(&[r.qb], &[Prem::Step(nr), Prem::Step(f.u0)], &[])
    }

    fn mono_run(&self, p: &mut Proof, db: &[T]) -> Option<S> {
        self.mono.run(p, &self.c.abits, db)
    }
}
