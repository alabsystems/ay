// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The schoolbook identity `(bvmul ZA ZB) = 2^n ZH + ZP` in the `4m`-bit ring:
//! the wide product of the two `2m`-bit operands is the overflow test's high
//! half `H` above the wrapped product `P`.

use super::bits;
use super::chain::cone;
use super::clean::shl_bits;
use super::helpers::{eq_step, lincomb, project, symm, trans, transfer, word_eq};
use super::lift::Lift;
use super::lin::{lin1, Blaster, LinOpts};
use super::proof::{Prem, Proof, S};
use super::row::Row;
use super::shift::{double_shift, ShiftLemma};
use super::term::{Op, T};
use ay_core::kani_compat::DetHashSet as HashSet;

#[path = "school_high.rs"]
mod high;

pub(crate) struct Ctx {
    pub(crate) row: Row,
    sh_nn_m: ShiftLemma,
    pub(crate) sh_n_m: ShiftLemma,
    lift: Lift,
    pub(crate) abits: Vec<T>,
    pub(crate) za: T,
    pub(crate) zb: T,
    za0: T,
    za1: T,
    zb0: T,
    zb1: T,
    a0: Vec<T>,
    a1: Vec<T>,
    b0: Vec<T>,
    b1: Vec<T>,
}

pub(crate) struct School {
    pub(crate) s: S,
    pub(crate) zp: T,
    pub(crate) zh: T,
}

fn padded(p: &Proof, bits: &[T], w: u32) -> Vec<T> {
    let mut v = bits.to_vec();
    v.resize(w as usize, p.t.ff);
    v
}

impl Ctx {
    pub(crate) fn new(p: &mut Proof, row: Row, prefix: &str) -> Option<Self> {
        let m = row.m;
        let (n, nn) = (2 * m, 4 * m);
        let dbl_nn = ShiftLemma::doubling(p, nn, &format!("{prefix}d{nn}_"))?;
        let dbl_n = ShiftLemma::doubling(p, n, &format!("{prefix}d{n}_"))?;
        let (sh_nn_m, sh_n_m) = if m % 8 == 0 {
            let s8nn = ShiftLemma::power(p, &dbl_nn, 8, &format!("{prefix}e{nn}_"))?;
            let s8n = ShiftLemma::power(p, &dbl_n, 8, &format!("{prefix}e{n}_"))?;
            (
                ShiftLemma::power(p, &s8nn, m / 8, &format!("{prefix}f{nn}_"))?,
                ShiftLemma::power(p, &s8n, m / 8, &format!("{prefix}f{n}_"))?,
            )
        } else {
            (
                ShiftLemma::power(p, &dbl_nn, m, &format!("{prefix}f{nn}_"))?,
                ShiftLemma::power(p, &dbl_n, m, &format!("{prefix}f{n}_"))?,
            )
        };
        let lift = Lift::new(p, m, &format!("{prefix}l"))?;
        let (a0, a1, b0, b1) = (
            p.t.bits(row.a_lo),
            p.t.bits(row.a_hi),
            p.t.bits(row.b_lo),
            p.t.bits(row.b_hi),
        );
        let mut abits = a0.clone();
        abits.extend(&a1);
        let mut bbits = b0.clone();
        bbits.extend(&b1);
        let za = p.t.bb(&padded(p, &abits, nn));
        let zb = p.t.bb(&padded(p, &bbits, nn));
        let za0 = p.t.bb(&padded(p, &a0, nn));
        let za1 = p.t.bb(&padded(p, &a1, nn));
        let zb0 = p.t.bb(&padded(p, &b0, nn));
        let zb1 = p.t.bb(&padded(p, &b1, nn));
        Some(Ctx {
            row,
            sh_nn_m,
            sh_n_m,
            lift,
            abits,
            za,
            zb,
            za0,
            za1,
            zb0,
            zb1,
            a0,
            a1,
            b0,
            b1,
        })
    }

    /// Operand bits of product `k` (`pll, phl, plh, phh`) in its spelled order.
    fn operands(&self, k: usize) -> (&[T], &[T]) {
        let (x, y) = match k {
            0 => (&self.a0, &self.b0),
            1 => (&self.a1, &self.b0),
            2 => (&self.a0, &self.b1),
            _ => (&self.a1, &self.b1),
        };
        if self.row.order.swap[k] {
            (y, x)
        } else {
            (x, y)
        }
    }

    /// `bb(bits(t) ++ F*n)`: a `2m`-bit term zero-extended to the wide ring.
    pub(crate) fn zw(&self, p: &mut Proof, t: T) -> T {
        let b = p.t.bits(t);
        let pb = padded(p, &b, 4 * self.row.m);
        p.t.bb(&pb)
    }

    pub(crate) fn shift_nn_n(&self, p: &mut Proof, b: &[T]) -> Option<S> {
        double_shift(p, &self.sh_nn_m, b)
    }

    pub(crate) fn shift_nn_m(&self, p: &mut Proof, b: &[T]) -> Option<S> {
        self.sh_nn_m.inst(p, b)
    }

    /// `(= Zw (bvadd (bvmul 2^k Zhi) Zlo))` where `Zw`'s bits are `Zlo`'s then `Zhi`'s.
    pub(crate) fn limb_split(
        &self,
        p: &mut Proof,
        zw: T,
        zhi: T,
        zlo: T,
        sh: &ShiftLemma,
    ) -> Option<S> {
        let hb = p.t.bits(zhi);
        let s = sh.inst(p, &hb)?;
        let sw = p.t.args(p.unit(s))[1];
        let sum = p.t.add(&[sw, zlo]);
        let tgt = p.t.eq(zw, sum);
        let lp = lin1(p, &[], tgt, &LinOpts::default())?;
        let c = p.t.lit(bits::pow2(sh.k, sh.w));
        let mh = p.t.mul(c, zhi);
        let sum2 = p.t.add(&[mh, zlo]);
        let ss = symm(p, s);
        let cg = eq_step(p, sum, sum2, "cong", &[ss]);
        Some(trans(p, &[lp, cg]))
    }

    /// `(= Z(prod) (bvmul ZX ZY))` and `(not (bvult c0 prod))` for a limb product.
    fn prod_lift(&self, p: &mut Proof, prod: T, xb: &[T], yb: &[T]) -> Option<(S, S)> {
        let n = self.row.n();
        let (fact, v0, w0) = self.lift.run(p, xb, yb)?;
        let mut bl = Blaster::new(&[], &[]);
        let (pa0, pa1) = (p.t.args(prod)[0], p.t.args(prod)[1]);
        let (_, sx) = bl.blast(p, pa0)?;
        let (by, sy) = bl.blast(p, pa1)?;
        let v0y = p.t.args(v0)[1];
        let (vyb, vys) = bl.blast(p, v0y)?;
        if vyb != by {
            return None;
        }
        let x128 = p.t.args(v0)[0];
        let byw = p.t.bb(&by);
        let mid = p.t.mul(x128, byw);
        let cv = eq_step(p, v0, mid, "cong", &vys.into_iter().collect::<Vec<_>>());
        let prem: Vec<S> = sx.into_iter().chain(sy).collect();
        let c1 = eq_step(p, prod, mid, "cong", &prem);
        let cvs = symm(p, cv);
        let cp = trans(p, &[c1, cvs]);
        let zn = p.t.lit(bits::zero(n));
        let (cprod, cv0) = (p.t.concat(&[zn, prod]), p.t.concat(&[zn, v0]));
        let zc = eq_step(p, cprod, cv0, "cong", &[cp]);
        let (_, bzs) = bl.blast(p, cprod)?;
        let bzs = bzs?;
        let e0 = project(p, fact, 0)?;
        let w0y = p.t.args(w0)[1];
        let (wyb, wys) = bl.blast(p, w0y)?;
        let zx = p.t.args(w0)[0];
        let wyw = p.t.bb(&wyb);
        let w0c = p.t.mul(zx, wyw);
        let cw = eq_step(p, w0, w0c, "cong", &wys.into_iter().collect::<Vec<_>>());
        let bzr = symm(p, bzs);
        let l = trans(p, &[bzr, zc, e0, cw]);
        let b0 = project(p, fact, 1)?;
        let c0 = p.t.args(p.t.args(p.unit(b0))[0])[0];
        let (u1, u2) = (p.t.ult(c0, prod), p.t.ult(c0, v0));
        let cb = eq_step(p, u1, u2, "cong", &[cp]);
        let bd = transfer(p, cb, b0)?;
        Some((l, bd))
    }
}

impl Ctx {
    /// `(= CB (@bbterm c))` for `CB = (ite c #b1 #b0)`.
    fn cb_fact(&self, p: &mut Proof) -> Option<S> {
        let (c, cb) = (self.row.c, self.row.cb);
        let cbw = p.t.bb(&[c]);
        let mut out = Vec::new();
        for val in [true, false] {
            let a = p.anchor(&[]);
            let lit = if val { c } else { p.t.not(c) };
            let h = p.assume(lit);
            let cv = if val { p.t.tt } else { p.t.ff };
            let e = p.t.eq(c, cv);
            let mut prem = p.gate(e);
            prem.extend(p.gate(cv));
            prem.push(Prem::Step(h));
            let ec = p.derive(&[e], &prem, &[])?;
            let (b1, b0) = (p.t.lit(bits::from_u64(1, 1)), p.t.lit(bits::zero(1)));
            let it = p.t.ite(cv, b1, b0);
            let s1 = eq_step(p, cb, it, "cong", &[ec]);
            let v = if val { b1 } else { b0 };
            let s2 = eq_step(p, it, v, "ite_simplify", &[]);
            let cvw = p.t.bb(&[cv]);
            let s3 = eq_step(p, v, cvw, "bitblast_const", &[]);
            let ecs = symm(p, ec);
            let s4 = eq_step(p, cvw, cbw, "cong", &[ecs]);
            trans(p, &[s1, s2, s3, s4]);
            let nl = p.t.not(lit);
            let ceq = p.t.eq(cb, cbw);
            out.push(p.close(a, &[nl, ceq], "subproof", &[h]));
        }
        let ceq = p.t.eq(cb, cbw);
        let prems: Vec<Prem> = out.iter().map(|&s| Prem::Step(s)).collect();
        p.derive(&[ceq], &prems, &[])
    }

    /// `(= SH (@bbterm F*m, c, F*(m-1)))` through the checker's shifter.
    fn sh_fact(&self, p: &mut Proof, cbs: S) -> Option<S> {
        let (m, n) = (self.row.m, self.row.n());
        let c = self.row.c;
        let x = p.t.zext(n - 1, self.row.cb);
        let mut bl = Blaster::new(&[], &[(self.row.cb, vec![c], cbs)]);
        let (xb, sx) = bl.blast(p, x)?;
        let (yb, sy) = bl.blast(p, self.row.shamt)?;
        let (xw, yw) = (p.t.bb(&xb), p.t.bb(&yb));
        let size_term = p.t.lit(bits::from_u64(u64::from(n), n));
        let size_bits = p.t.bits(size_term);
        let res = shl_bits(&mut p.t, &xb, &yb, &size_bits);
        let shl = p.t.mk(Op::Shl, &[xw, yw]);
        let resw = p.t.bb(&res);
        let s1 = eq_step(p, shl, resw, "bitblast_shl", &[]);
        let prem: Vec<S> = sx.into_iter().chain(sy).collect();
        let c1 = eq_step(p, self.row.sh, shl, "cong", &prem);
        let mut evs = Vec::new();
        let szv = bits::from_u64(u64::from(n), n);
        for (i, &bt) in size_bits.iter().enumerate() {
            let v = if szv[i] { p.t.tt } else { p.t.ff };
            let e = p.t.eq(bt, v);
            let ev = p.emit(&[e], "evaluate", &[], &[]);
            let lit = if szv[i] { bt } else { p.t.not(bt) };
            let mut pr = vec![Prem::Step(ev)];
            pr.extend(p.gate(e));
            pr.extend(p.gate(v));
            evs.push(Prem::Step(p.derive(&[lit], &pr, &[])?));
        }
        let ff = p.t.ff;
        let mut tgt = vec![ff; m as usize];
        tgt.push(c);
        tgt.resize(n as usize, ff);
        let mut bitf = Vec::new();
        for i in 0..n as usize {
            let e = p.t.eq(res[i], tgt[i]);
            let (gates, _) = cone(
                p,
                e,
                &HashSet::default(),
                &HashSet::default(),
                &HashSet::default(),
            );
            let mut pr = Vec::new();
            for g in gates {
                pr.extend(p.gate(g));
            }
            pr.extend(evs.iter().copied());
            bitf.push(p.derive(&[e], &pr, &[])?);
        }
        let tw = p.t.bb(&tgt);
        let we = word_eq(p, resw, tw, &bitf)?;
        Some(trans(p, &[c1, s1, we]))
    }
}

/// Unsigned limb split of `x = 2^m hi + lo` at `2m` bits for an operand's limbs.
fn limb_words(p: &mut Proof, hi: &[T], lo: &[T], n: u32) -> (T, T, T) {
    let mut whole = lo.to_vec();
    whole.extend(hi);
    (
        p.t.bb(&whole),
        p.t.bb(&padded(p, hi, n)),
        p.t.bb(&padded(p, lo, n)),
    )
}

pub(crate) fn lit_pow(p: &mut Proof, k: u32, w: u32) -> T {
    p.t.lit(bits::pow2(k, w))
}

pub(crate) fn lit_neg_pow(p: &mut Proof, k: u32, w: u32) -> T {
    p.t.lit(bits::neg(&bits::pow2(k, w)))
}

pub(crate) fn lit_minus1(p: &mut Proof, w: u32) -> T {
    p.t.lit(bits::neg(&bits::from_u64(1, w)))
}

struct Parts {
    zphl: T,
    zplh: T,
    zphh: T,
    zt: T,
    zl0: T,
    zmid: T,
    zxh: T,
    zml: T,
    zc: T,
    /// `(not (bvult c0 S2))` for the middle sum's later summand `S2`.
    bsecond: S,
    hm: S,
}

impl Ctx {
    pub(crate) fn schoolbook(&self, p: &mut Proof) -> Option<School> {
        let r = &self.row;
        let (m, n, nn) = (r.m, r.n(), 4 * r.m);
        let ea = self.limb_split(p, self.za, self.za1, self.za0, &self.sh_nn_m)?;
        let eb = self.limb_split(p, self.zb, self.zb1, self.zb0, &self.sh_nn_m)?;
        let mut lifts = Vec::with_capacity(4);
        for (k, prod) in [r.pll, r.phl, r.plh, r.phh].into_iter().enumerate() {
            let (xb, yb) = self.operands(k);
            lifts.push(self.prod_lift(p, prod, xb, yb)?);
        }
        let [(lll, _), (lhl, bhl), (llh, blh), (lhh, _)] = lifts[..] else {
            return None;
        };
        // The middle sum's carry compares against `xt` plus its LATER summand.
        let bsecond = if r.order.plh_first { bhl } else { blh };
        let (zpll, zphl, zplh, zphh) = (
            self.zw(p, r.pll),
            self.zw(p, r.phl),
            self.zw(p, r.plh),
            self.zw(p, r.phh),
        );
        let (cn, cm) = (lit_pow(p, n, nn), lit_pow(p, m, nn));
        let mhh = p.t.mul(cn, zphh);
        let mhl = p.t.mul(cm, zphl);
        let mlh = p.t.mul(cm, zplh);
        let r3 = p.t.add(&[mhh, mhl, mlh, zpll]);
        let lhs = p.t.mul(self.za, self.zb);
        let ma1 = p.t.mul(cm, self.za1);
        let aex = p.t.add(&[ma1, self.za0]);
        let (nn_n, nn_m, m1) = (
            lit_neg_pow(p, n, nn),
            lit_neg_pow(p, m, nn),
            lit_minus1(p, nn),
        );
        let e3 = lincomb(
            p,
            lhs,
            r3,
            &[
                (ea, Some(self.zb)),
                (eb, Some(aex)),
                (lhh, Some(nn_n)),
                (lhl, Some(nn_m)),
                (llh, Some(nn_m)),
                (lll, Some(m1)),
            ],
        )?;
        let pll = p.t.bits(r.pll);
        let zt = p.t.bb(&padded(p, &pll[m as usize..], nn));
        let zl0 = p.t.bb(&padded(p, &pll[..m as usize], nn));
        let e4 = self.limb_split(p, zpll, zt, zl0, &self.sh_nn_m)?;
        let zc = p.t.bb(&padded(p, &[r.c], nn));
        let zmid = self.zw(p, r.mid);
        let midw = {
            let b = p.t.bits(r.mid);
            p.t.bb(&b)
        };
        let vm = eq_step(p, r.mid, midw, "bitblast_var", &[]);
        let hm = symm(p, vm);
        let mid = p.t.bits(r.mid);
        let zxh = p.t.bb(&padded(p, &mid[m as usize..], nn));
        let zml = p.t.bb(&padded(p, &mid[..m as usize], nn));
        let parts = Parts {
            zphl,
            zplh,
            zphh,
            zt,
            zl0,
            zmid,
            zxh,
            zml,
            zc,
            bsecond,
            hm,
        };
        let e5 = self.s5(p, &parts)?;
        let e6 = self.limb_split(p, zmid, zxh, zml, &self.sh_nn_m)?;
        let (e7, zh) = self.s7(p, &parts)?;
        let (e8, zp) = self.s8(p, &parts)?;
        let zhs = p.t.mul(cn, zh);
        let rhs = p.t.add(&[zhs, zp]);
        let s = lincomb(
            p,
            lhs,
            rhs,
            &[
                (e3, None),
                (e4, None),
                (e5, Some(nn_m)),
                (e6, Some(cm)),
                (e7, Some(m1)),
                (e8, Some(m1)),
            ],
        )?;
        Some(School { s, zp, zh })
    }

    /// `(= (bvadd ZMID (bvmul 2^n Zc)) (bvadd ZT ZS1 ZS2))`: the middle sum and its carry.
    fn s5(&self, p: &mut Proof, q: &Parts) -> Option<S> {
        let r = &self.row;
        let nn = 4 * r.m;
        let zcb = p.t.bits(q.zc);
        let shc = self.shift_nn_n(p, &zcb)?;
        let sc = p.t.args(p.unit(shc))[1];
        let l = p.t.add(&[q.zmid, sc]);
        let (zfirst, zsecond) = if r.order.plh_first {
            (q.zplh, q.zphl)
        } else {
            (q.zphl, q.zplh)
        };
        let rr = p.t.add(&[q.zt, zfirst, zsecond]);
        let tgt = p.t.eq(l, rr);
        let o = LinOpts {
            opaque: vec![r.pll, r.phl, r.plh],
            defs: vec![r.c],
            ..LinOpts::default()
        };
        let l5 = lin1(p, &[q.hm, q.bsecond], tgt, &o)?;
        let cn = lit_pow(p, 2 * r.m, nn);
        let mc = p.t.mul(cn, q.zc);
        let l2 = p.t.add(&[q.zmid, mc]);
        let shs = symm(p, shc);
        let c5 = eq_step(p, l, l2, "cong", &[shs]);
        let c5s = symm(p, c5);
        Some(trans(p, &[c5s, l5]))
    }
}
