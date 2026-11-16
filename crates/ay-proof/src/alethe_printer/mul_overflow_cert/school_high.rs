// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The schoolbook high half against the wide product (`s7`) and the wrapped
//! product as the low limbs of `PLL` and `MID` (`s8`).

use super::{limb_words, lit_neg_pow, lit_pow, padded, Ctx, Parts};
use crate::alethe_printer::mul_overflow_cert::helpers::{eq_step, lincomb, symm, trans};
use crate::alethe_printer::mul_overflow_cert::lin::{lin1, Blaster, LinOpts};
use crate::alethe_printer::mul_overflow_cert::lin_bits::bit_facts;
use crate::alethe_printer::mul_overflow_cert::proof::{Proof, S};
use crate::alethe_printer::mul_overflow_cert::term::T;

impl Ctx {
    /// `(= (bvmul 2^n ZH) (bvmul 2^n (bvadd ZXH ZPHH (bvmul 2^m Zc))))`: `H` agrees with the
    /// wide sum on its low `2m` bits.
    pub(super) fn s7(&self, p: &mut Proof<'_>, q: &Parts) -> Option<(S, T)> {
        let r = &self.row;
        let (m, n, nn) = (r.m, r.n(), 4 * r.m);
        let cbs = self.cb_fact(p)?;
        let shs = self.sh_fact(p, cbs)?;
        let zh = self.zw(p, r.h);
        let zhb = p.t.bits(zh);
        let sh1 = self.shift_nn_n(p, &zhb)?;
        let zcb = p.t.bits(q.zc);
        let shm = self.shift_nn_m(p, &zcb)?;
        let s64c = p.t.args(p.unit(shm))[1];
        let cm = lit_pow(p, m, nn);
        let mc = p.t.mul(cm, q.zc);
        let wh = p.t.add(&[q.zxh, q.zphh, mc]);
        let whp = p.t.add(&[q.zxh, q.zphh, s64c]);
        let cw = eq_step(p, wh, whp, "cong", &[shm]);
        let mut bw = Blaster::new(&[], &[]);
        let (wb, sw) = bw.blast(p, whp)?;
        let sw = sw?;
        let whb = p.t.bb(&wb);
        let sh2 = self.shift_nn_n(p, &wb)?;
        let hw = {
            let b = p.t.bits(r.h);
            p.t.bb(&b)
        };
        let vh = eq_step(p, r.h, hw, "bitblast_var", &[]);
        let wlow = p.t.bb(&wb[..n as usize]);
        let tgt = p.t.eq(hw, wlow);
        let shbits = p.t.args(p.t.args(p.unit(shs))[1]).to_vec();
        let o = LinOpts {
            opaque: vec![r.mid, r.phh],
            known: vec![(r.sh, shbits, shs)],
            ..LinOpts::default()
        };
        let vhs = symm(p, vh);
        let low = lin1(p, &[vhs], tgt, &o)?;
        let bitsf = bit_facts(p, low)?;
        let s1 = p.t.args(p.unit(sh1))[1];
        let s2 = p.t.args(p.unit(sh2))[1];
        let s12 = eq_step(p, s1, s2, "cong", &bitsf);
        let cn = lit_pow(p, n, nn);
        let (lhs7, rhs7) = (p.t.mul(cn, whb), p.t.mul(cn, wh));
        let t1 = trans(p, &[cw, sw]);
        let t1s = symm(p, t1);
        let c7 = eq_step(p, lhs7, rhs7, "cong", &[t1s]);
        let sh2s = symm(p, sh2);
        Some((trans(p, &[sh1, s12, sh2s, c7]), zh))
    }

    /// `(= ZP (bvadd (bvmul 2^m ZML) ZL0))`: the wrapped product is the low limb of `PLL`
    /// below the low limb of `MID`, by ring steps at `2m` bits.
    pub(super) fn s8(&self, p: &mut Proof<'_>, q: &Parts) -> Option<(S, T)> {
        let r = &self.row;
        let (m, n) = (r.m, r.n());
        let mut bn = Blaster::new(&[r.a_lo, r.a_hi, r.b_lo, r.b_hi], &[]);
        let (_, sa) = bn.blast(p, r.a)?;
        let (_, sb) = bn.blast(p, r.b)?;
        let xs: Vec<T> = [r.a_hi, r.a_lo, r.b_hi, r.b_lo]
            .iter()
            .map(|&v| p.t.zext(m, v))
            .collect();
        let mut words = Vec::new();
        let mut steps = Vec::new();
        for &x in &xs {
            let (b, s) = bn.blast(p, x)?;
            words.push(p.t.bb(&b));
            steps.push(s?);
        }
        let (x1, x0, y1, y0) = (words[0], words[1], words[2], words[3]);
        let (a128, x1v, x0v) = limb_words(p, &self.a1, &self.a0, n);
        let (b128, y1v, y0v) = limb_words(p, &self.b1, &self.b0, n);
        if (x1v, x0v, y1v, y0v) != (x1, x0, y1, y0) {
            return None;
        }
        let ea = self.limb_split(p, a128, x1, x0, &self.sh_n_m)?;
        let eb = self.limb_split(p, b128, y1, y0, &self.sh_n_m)?;
        let cm = lit_pow(p, m, n);
        let (mx1, my1) = (p.t.mul(cm, x1), p.t.mul(cm, y1));
        let (aex, bex) = (p.t.add(&[mx1, x0]), p.t.add(&[my1, y0]));
        let ab = p.t.mul(a128, b128);
        let p1 = eq_step(p, r.p, ab, "cong", &[sa?, sb?]);
        let abx = p.t.mul(aex, bex);
        let p2 = eq_step(p, ab, abx, "cong", &[ea, eb]);
        let swap = r.order.swap;
        let spelled = |p: &mut Proof<'_>, k: usize, x: T, y: T| {
            if swap[k] {
                p.t.mul(y, x)
            } else {
                p.t.mul(x, y)
            }
        };
        let (x1y0, x0y1, x0y0) = (
            spelled(p, 1, x1, y0),
            spelled(p, 2, x0, y1),
            spelled(p, 0, x0, y0),
        );
        // the operand steps of product `k` in its spelled order
        let ordered = |k: usize, sx: S, sy: S| if swap[k] { (sy, sx) } else { (sx, sy) };
        let (mx1y0, mx0y1) = (p.t.mul(cm, x1y0), p.t.mul(cm, x0y1));
        let pex = p.t.add(&[mx1y0, mx0y1, x0y0]);
        let p3 = eq_step(p, pex, abx, "poly_simp", &[]);
        let (whl, wlh, wll, wp, wmid) = (
            self.word(p, r.phl),
            self.word(p, r.plh),
            self.word(p, r.pll),
            self.word(p, r.p),
            self.word(p, r.mid),
        );
        let (hl1, hl2) = ordered(1, steps[0], steps[3]);
        let (lh1, lh2) = ordered(2, steps[1], steps[2]);
        let (ll1, ll2) = ordered(0, steps[1], steps[3]);
        let ehl = self.product_word(p, x1y0, r.phl, whl, hl1, hl2)?;
        let elh = self.product_word(p, x0y1, r.plh, wlh, lh1, lh2)?;
        let ell = self.product_word(p, x0y0, r.pll, wll, ll1, ll2)?;
        let pll = p.t.bits(r.pll);
        let mid = p.t.bits(r.mid);
        let xtw = p.t.bb(&padded(p, &pll[m as usize..], n));
        let l0w = p.t.bb(&padded(p, &pll[..m as usize], n));
        let xhw = p.t.bb(&padded(p, &mid[m as usize..], n));
        let mlw = p.t.bb(&padded(p, &mid[..m as usize], n));
        let epll = self.limb_split(p, wll, xtw, l0w, &self.sh_n_m)?;
        let emid = self.limb_split(p, wmid, xhw, mlw, &self.sh_n_m)?;
        let dmid = self.mid_def(p, q, xtw, whl, wlh)?;
        let (mwhl, mwlh) = (p.t.mul(cm, whl), p.t.mul(cm, wlh));
        let pw = p.t.add(&[mwhl, mwlh, wll]);
        let (mm1, mm2) = (
            eq_step(p, mx1y0, mwhl, "cong", &[ehl]),
            eq_step(p, mx0y1, mwlh, "cong", &[elh]),
        );
        let cpw = eq_step(p, pex, pw, "cong", &[mm1, mm2, ell]);
        let vp = eq_step(p, r.p, wp, "bitblast_var", &[]);
        let vps = symm(p, vp);
        let p3s = symm(p, p3);
        let rp = trans(p, &[vps, p1, p2, p3s, cpw]);
        let mml = p.t.mul(cm, mlw);
        let tgtw = p.t.add(&[mml, l0w]);
        let nm = lit_neg_pow(p, m, n);
        let rq = lincomb(
            p,
            wp,
            tgtw,
            &[(rp, None), (epll, None), (dmid, Some(nm)), (emid, Some(cm))],
        )?;
        let mut tb = pll[..m as usize].to_vec();
        tb.extend(&mid[..m as usize]);
        self.s8_close(p, q, rq, [wp, tgtw, mlw, l0w], &tb)
    }

    /// The tail of [`Self::s8`]: from `W(P) = 2^m W(ML) + W(L0)` at `2m`
    /// bits to the zero-extended statement.
    fn s8_close(&self, p: &mut Proof<'_>, q: &Parts, rq: S, w: [T; 4], tb: &[T]) -> Option<(S, T)> {
        let [wp, tgtw, mlw, l0w] = w;
        let r = &self.row;
        let (m, nn) = (r.m, 4 * r.m);
        let mlb = p.t.bits(mlw);
        let shm2 = self.sh_n_m.inst(p, &mlb)?;
        let sm2 = p.t.args(p.unit(shm2))[1];
        let s2l = p.t.add(&[sm2, l0w]);
        let c82 = eq_step(p, tgtw, s2l, "cong", &[shm2]);
        let l8a = trans(p, &[rq, c82]);
        let tgtp = p.t.bb(tb);
        let t8 = p.t.eq(wp, tgtp);
        let l8 = lin1(p, &[l8a], t8, &LinOpts::default())?;
        let zp = self.zw(p, r.p);
        let zmlb = p.t.bits(q.zml);
        let s8 = self.sh_nn_m.inst(p, &zmlb)?;
        let s8w = p.t.args(p.unit(s8))[1];
        let s8l = p.t.add(&[s8w, q.zl0]);
        let t8b = p.t.eq(zp, s8l);
        let l8b = lin1(p, &[l8], t8b, &LinOpts::default())?;
        let cmm = lit_pow(p, m, nn);
        let mzml = p.t.mul(cmm, q.zml);
        let fin = p.t.add(&[mzml, q.zl0]);
        let s8s = symm(p, s8);
        let c8 = eq_step(p, s8l, fin, "cong", &[s8s]);
        Some((trans(p, &[l8b, c8]), zp))
    }

    fn word(&self, p: &mut Proof<'_>, t: T) -> T {
        let b = p.t.bits(t);
        p.t.bb(&b)
    }

    /// `(= (bvmul X Y) W(prod))` for `prod = (bvmul (zext x) (zext y))` re-spelled over its operand words.
    fn product_word(&self, p: &mut Proof<'_>, xy: T, prod: T, wprod: T, sx: S, sy: S) -> Option<S> {
        let (sxs, sys) = (symm(p, sx), symm(p, sy));
        let c = eq_step(p, xy, prod, "cong", &[sxs, sys]);
        let v = eq_step(p, prod, wprod, "bitblast_var", &[]);
        Some(trans(p, &[c, v]))
    }

    /// `(= W(MID) (bvadd (bvadd XT W(S1)) W(S2)))`: `MID` re-spelled over canonical words.
    fn mid_def(&self, p: &mut Proof<'_>, q: &Parts, xtw: T, whl: T, wlh: T) -> Option<S> {
        let r = &self.row;
        let mut bm = Blaster::new(&[r.pll, r.phl, r.plh], &[]);
        let (xtb, sxt) = bm.blast(p, r.xt)?;
        if p.t.bb(&xtb) != xtw {
            return None;
        }
        let (s1, s2) = r.cross();
        let (w1, w2) = if r.order.plh_first {
            (wlh, whl)
        } else {
            (whl, wlh)
        };
        let v1 = eq_step(p, s1, w1, "bitblast_var", &[]);
        let v2 = eq_step(p, s2, w2, "bitblast_var", &[]);
        let inner = p.t.add(&[r.xt, s1]);
        let inner2 = p.t.add(&[xtw, w1]);
        let ci = eq_step(p, inner, inner2, "cong", &[sxt?, v1]);
        let outer2 = p.t.add(&[inner2, w2]);
        let dm = eq_step(p, r.mid, outer2, "cong", &[ci, v2]);
        Some(trans(p, &[q.hm, dm]))
    }
}
