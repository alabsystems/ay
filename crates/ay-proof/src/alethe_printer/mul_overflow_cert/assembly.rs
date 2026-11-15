// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The certificate of the overflow identity `L = R`: `H = 0` exactly when
//! `A = 0` or the quotient of the wrapped product by `A` gives back `B`.
//! (F1) `A = 0 => H = 0`; (F2) `A != 0, Q = B => H = 0`; (F3) `A != 0, H = 0 => Q = B`.

use super::bits;
use super::clean::bb_equal;
use super::div::z;
use super::div_lemma::DivLemma;
use super::helpers::{eq_step, lincomb, symm, trans, transfer, word_eq};
use super::lin::{lin1, Blaster, LinOpts};
use super::lin_bits::bit_facts;
use super::mono::Mono;
use super::proof::{Prem, Proof, S};
use super::school::{lit_minus1, lit_pow, Ctx, School};
use super::term::{Op, T};

pub(crate) struct Asm<'a> {
    pub(crate) c: &'a Ctx,
    pub(crate) sc: School,
    pub(crate) mono: Mono,
    pub(crate) a128: T,
    pub(crate) b128: T,
    pub(crate) zbb: T,
    pub(crate) one_w: T,
    pub(crate) sa: S,
    pub(crate) sb: S,
    pub(crate) sz: S,
    pub(crate) sone: S,
    pub(crate) vap: S,
    pub(crate) vh: S,
    pub(crate) vp: S,
    pub(crate) k0: S,
    pub(crate) refl: S,
}

pub(crate) struct Ds {
    pub(crate) e0: S,
    pub(crate) u0: S,
    pub(crate) q0w: T,
    pub(crate) r0w: T,
    pub(crate) yw: T,
    pub(crate) zq0: T,
    pub(crate) zr0: T,
    pub(crate) zyp: T,
    pub(crate) uq: S,
    /// `(cl (or (not (= P Z)) (= Q Z)))`: a zero product has quotient zero.
    pub(crate) zero: S,
}

fn w(p: &mut Proof, t: T) -> T {
    let b = p.t.bits(t);
    p.t.bb(&b)
}

impl<'a> Asm<'a> {
    pub(crate) fn new(p: &mut Proof, c: &'a Ctx, sc: School, mono: Mono) -> Option<Self> {
        let r = &c.row;
        let nn = 4 * r.m;
        let l0 = p.t.lit(bits::zero(nn));
        let ff = p.t.ff;
        let zero = p.t.bb(&vec![ff; nn as usize]);
        let k0 = eq_step(p, l0, zero, "bitblast_const", &[]);
        let mut bl = Blaster::new(&[r.a_lo, r.a_hi, r.b_lo, r.b_hi, r.p, r.h, r.ap, r.q], &[]);
        let (ab, sa) = bl.blast(p, r.a)?;
        let (bb_, sb) = bl.blast(p, r.b)?;
        let (zb, sz) = bl.blast(p, r.z)?;
        let (ob, sone) = bl.blast(p, r.one)?;
        let (a128, b128, zbb, one_w) = (p.t.bb(&ab), p.t.bb(&bb_), p.t.bb(&zb), p.t.bb(&ob));
        let (wap, wh, wp) = (w(p, r.ap), w(p, r.h), w(p, r.p));
        let vap = eq_step(p, r.ap, wap, "bitblast_var", &[]);
        let vh = eq_step(p, r.h, wh, "bitblast_var", &[]);
        let vp = eq_step(p, r.p, wp, "bitblast_var", &[]);
        let fe = p.t.eq(ff, ff);
        let refl = p.emit(&[fe], "eq_reflexive", &[], &[]);
        Some(Asm {
            c,
            sc,
            mono,
            a128,
            b128,
            zbb,
            one_w,
            sa: sa?,
            sb: sb?,
            sz: sz?,
            sone: sone?,
            vap,
            vh,
            vp,
            k0,
            refl,
        })
    }

    fn yz(&self, p: &mut Proof) -> T {
        let ff = p.t.ff;
        let apb = p.t.bits(self.c.row.ap);
        let eqs: Vec<T> = apb.iter().map(|&b| p.t.eq(b, ff)).collect();
        p.t.and(&eqs)
    }

    /// `(= Ap ONE)` under `az`, `(= Ap A)` under `(not az)`, as `@bbterm` words.
    fn ap_value(&self, p: &mut Proof, val: bool, h: S) -> Option<S> {
        let r = &self.c.row;
        let cv = if val { p.t.tt } else { p.t.ff };
        let e = p.t.eq(r.az, cv);
        let mut prem = p.gate(e);
        prem.extend(p.gate(cv));
        prem.push(Prem::Step(h));
        let ec = p.derive(&[e], &prem, &[])?;
        let it = p.t.ite(cv, r.one, r.a);
        let s1 = eq_step(p, r.ap, it, "cong", &[ec]);
        let v = if val { r.one } else { r.a };
        let s2 = eq_step(p, it, v, "ite_simplify", &[]);
        let vs = symm(p, self.vap);
        Some(trans(
            p,
            &[vs, s1, s2, if val { self.sone } else { self.sa }],
        ))
    }

    /// `(cl (not yz))`: the divisor `A'` is never zero.
    fn nonzero(&self, p: &mut Proof) -> Option<S> {
        let r = &self.c.row;
        let yz = self.yz(p);
        let apb = p.t.bits(r.ap);
        let mut cases = Vec::new();
        for val in [true, false] {
            let a = p.anchor(&[]);
            let lit = if val { r.az } else { p.t.not(r.az) };
            let h = p.assume(lit);
            let s3 = self.ap_value(p, val, h)?;
            let tw = if val { self.one_w } else { self.a128 };
            let tb = p.t.bits(tw);
            let mut prem: Vec<Prem> = bit_facts(p, s3)?.into_iter().map(Prem::Step).collect();
            prem.extend(p.gate(yz));
            let (ff, tt) = (p.t.ff, p.t.tt);
            prem.extend(p.gate(ff));
            prem.extend(p.gate(tt));
            for (i, &b) in apb.iter().enumerate() {
                let (e1, e2) = (p.t.eq(b, ff), p.t.eq(b, tb[i]));
                prem.extend(p.gate(e1));
                prem.extend(p.gate(e2));
            }
            if !val {
                let eqz = p.t.eq(self.a128, self.zbb);
                let ce = eq_step(p, r.az, eqz, "cong", &[self.sa, self.sz]);
                let zbits = p.t.bits(self.zbb);
                let cj = bb_equal(&mut p.t, &tb, &zbits);
                let be = eq_step(p, eqz, cj, "bitblast_equal", &[]);
                let tr = trans(p, &[ce, be]);
                prem.push(Prem::Step(transfer(p, tr, h)?));
                prem.extend(p.gate(cj));
                for &c in p.t.args(cj).to_vec().iter() {
                    prem.extend(p.gate(c));
                }
            }
            let nyz = p.t.not(yz);
            p.derive(&[nyz], &prem, &[])?;
            let nl = p.t.not(lit);
            cases.push(p.close(a, &[nl, nyz], "subproof", &[h]));
        }
        let nyz = p.t.not(yz);
        let prems: Vec<Prem> = cases.iter().map(|&s| Prem::Step(s)).collect();
        p.derive(&[nyz], &prems, &[])
    }
}

impl<'a> Asm<'a> {
    /// The division spec for `(bvudiv P A')`, connected to the schoolbook's words.
    fn ds(&self, p: &mut Proof, dl: &DivLemma, nyz: S) -> Option<Ds> {
        let r = &self.c.row;
        let n = r.n();
        let split = dl.split_instance(p, r.p, r.ap)?;
        let [e, u, _, zero] = DivLemma::conjuncts(p, split, nyz)?;
        let rem = p.t.mk(Op::Urem, &[r.p, r.ap]);
        let (q0w, r0w, yw) = (w(p, r.q), w(p, rem), w(p, r.ap));
        let uq = eq_step(p, r.q, q0w, "bitblast_var", &[]);
        let vr = eq_step(p, rem, r0w, "bitblast_var", &[]);
        let (zq0, zr0, zyp) = (z(p, n, q0w), z(p, n, r0w), z(p, n, yw));
        let (zq, zy, zr, zx) = (z(p, n, r.q), z(p, n, r.ap), z(p, n, rem), z(p, n, r.p));
        let cq = eq_step(p, zq, zq0, "cong", &[uq]);
        let cy = eq_step(p, zy, zyp, "cong", &[self.vap]);
        let cr = eq_step(p, zr, zr0, "cong", &[vr]);
        let (m1, m0) = (p.t.mul(zq, zy), p.t.mul(zq0, zyp));
        let cm = eq_step(p, m1, m0, "cong", &[cq, cy]);
        let (s1, s0) = (p.t.add(&[m1, zr]), p.t.add(&[m0, zr0]));
        let cs = eq_step(p, s1, s0, "cong", &[cm, cr]);
        let css = symm(p, cs);
        let wp = w(p, r.p);
        let zwp = z(p, n, wp);
        let cx = eq_step(p, zx, zwp, "cong", &[self.vp]);
        let mut bz = Blaster::new(&[], &[]);
        let (zpb, zps) = bz.blast(p, zwp)?;
        if p.t.bb(&zpb) != self.sc.zp {
            return None;
        }
        let e0 = trans(p, &[css, e, cx, zps?]);
        let u1 = p.t.ult(rem, r.ap);
        let u0w = p.t.ult(r0w, yw);
        let cu = eq_step(p, u1, u0w, "cong", &[vr, self.vap]);
        let u0 = transfer(p, cu, u)?;
        Some(Ds {
            e0,
            u0,
            q0w,
            r0w,
            yw,
            zq0,
            zr0,
            zyp,
            uq,
            zero,
        })
    }

    /// `(cl hz)` from `(cl (= (bvmul 2^n ZH)-shifted ZERO))` over the shifted word `s1`.
    pub(crate) fn hz_from_shifted(&self, p: &mut Proof, s1z: S) -> Option<S> {
        let r = &self.c.row;
        let n = r.n() as usize;
        let bf = bit_facts(p, s1z)?;
        let wh = w(p, r.h);
        let we = word_eq(p, wh, self.zbb, &bf[n..])?;
        let szs = symm(p, self.sz);
        Some(trans(p, &[self.vh, we, szs]))
    }

    /// (F1) `az => hz`.
    fn f1(&self, p: &mut Proof, sh1: S) -> Option<S> {
        let r = &self.c.row;
        let (n, nn) = (r.n(), 4 * r.m);
        let a = p.anchor(&[]);
        let haz = p.assume(r.az);
        let eqz = p.t.eq(self.a128, self.zbb);
        let ce = eq_step(p, r.az, eqz, "cong", &[self.sa, self.sz]);
        let za = transfer(p, ce, haz)?;
        let mut bfa = bit_facts(p, za)?;
        bfa.resize(nn as usize, self.refl);
        let zero = p.t.args(p.unit(self.k0))[1];
        let l0 = p.t.args(p.unit(self.k0))[0];
        let za_w = word_eq(p, self.c.za, zero, &bfa)?;
        let k0s = symm(p, self.k0);
        let eza = trans(p, &[za_w, k0s]);
        let l0n = p.t.lit(bits::zero(n));
        let kz = eq_step(p, l0n, self.zbb, "bitblast_const", &[]);
        let kzs = symm(p, kz);
        let zl = trans(p, &[self.sz, kzs]);
        let zb_ = p.t.mul(r.z, r.b);
        let pa = eq_step(p, r.p, zb_, "cong", &[haz]);
        let lb = p.t.mul(l0n, r.b);
        let pb = eq_step(p, zb_, lb, "cong", &[zl]);
        let pc = eq_step(p, lb, l0n, "poly_simp", &[]);
        let vps = symm(p, self.vp);
        let pz = trans(p, &[vps, pa, pb, pc, kz]);
        let mut bfp = bit_facts(p, pz)?;
        bfp.resize(nn as usize, self.refl);
        let zp_w = word_eq(p, self.sc.zp, zero, &bfp)?;
        let ezp = trans(p, &[zp_w, k0s]);
        let cn = lit_pow(p, n, nn);
        let lhs = p.t.mul(cn, self.sc.zh);
        let m1 = lit_minus1(p, nn);
        let e2n = lincomb(
            p,
            lhs,
            l0,
            &[
                (self.sc.s, Some(m1)),
                (eza, Some(self.c.zb)),
                (ezp, Some(m1)),
            ],
        )?;
        let sh1s = symm(p, sh1);
        let s1z = trans(p, &[sh1s, e2n, self.k0]);
        self.hz_from_shifted(p, s1z)?;
        let naz = p.t.not(r.az);
        Some(p.close(a, &[naz, r.hz], "subproof", &[haz]))
    }

    /// Under `(not az)`: `(= ZYp ZA)` and `(= W(Ap) A128)`.
    pub(crate) fn ap_eq_a(&self, p: &mut Proof, ds: &Ds, hn: S) -> Option<(S, S)> {
        let n = self.c.row.n();
        let s3 = self.ap_value(p, false, hn)?;
        let za = z(p, n, self.a128);
        let cz = eq_step(p, ds.zyp, za, "cong", &[s3]);
        let mut bz = Blaster::new(&[], &[]);
        let (zab, zas) = bz.blast(p, za)?;
        if p.t.bb(&zab) != self.c.za {
            return None;
        }
        Some((trans(p, &[cz, zas?]), s3))
    }
}

impl<'a> Asm<'a> {
    /// (F2) `(not az), qb => hz`.
    fn f2(&self, p: &mut Proof, ds: &Ds, sh1: S) -> Option<S> {
        let r = &self.c.row;
        let (n, nn) = (r.n(), 4 * r.m);
        let a = p.anchor(&[]);
        let naz = p.t.not(r.az);
        let hn = p.assume(naz);
        let hq = p.assume(r.qb);
        let (ya, _) = self.ap_eq_a(p, ds, hn)?;
        let uqs = symm(p, ds.uq);
        let qbw = trans(p, &[uqs, hq, self.sb]);
        let zb128 = z(p, n, self.b128);
        let cqb = eq_step(p, ds.zq0, zb128, "cong", &[qbw]);
        let mut bz = Blaster::new(&[], &[]);
        let (zbb, zbs) = bz.blast(p, zb128)?;
        if p.t.bb(&zbb) != self.c.zb {
            return None;
        }
        let qb = trans(p, &[cqb, zbs?]);
        let (m_l, m_r) = (p.t.mul(ds.zq0, ds.zyp), p.t.mul(self.c.zb, self.c.za));
        let c1 = eq_step(p, m_l, m_r, "cong", &[qb, ya]);
        let (a_l, a_r) = (p.t.add(&[m_l, ds.zr0]), p.t.add(&[m_r, ds.zr0]));
        let c2 = eq_step(p, a_l, a_r, "cong", &[c1]);
        let c2s = symm(p, c2);
        let e0p = trans(p, &[c2s, ds.e0]);
        let cn = lit_pow(p, n, nn);
        let zhs = p.t.mul(cn, self.sc.zh);
        let lhs = p.t.add(&[zhs, ds.zr0]);
        let l0 = p.t.args(p.unit(self.k0))[0];
        let m1 = lit_minus1(p, nn);
        let e2 = lincomb(p, lhs, l0, &[(e0p, None), (self.sc.s, Some(m1))])?;
        let s1 = p.t.args(p.unit(sh1))[1];
        let s1r = p.t.add(&[s1, ds.zr0]);
        let c3 = eq_step(p, lhs, s1r, "cong", &[sh1]);
        let c3s = symm(p, c3);
        let e3 = trans(p, &[c3s, e2]);
        let zero = p.t.args(p.unit(self.k0))[1];
        let t = p.t.eq(s1, zero);
        let s1z = lin1(
            p,
            &[e3],
            t,
            &LinOpts {
                opaque_leaves: true,
                ..LinOpts::default()
            },
        )?;
        self.hz_from_shifted(p, s1z)?;
        let (n1, n2) = (p.t.not(naz), p.t.not(r.qb));
        Some(p.close(a, &[n1, n2, r.hz], "subproof", &[hn, hq]))
    }

    pub(crate) fn run(
        &self,
        p: &mut Proof,
        dl: &DivLemma,
        h0: Option<S>,
        final_id: Option<&str>,
    ) -> Option<S> {
        let r = &self.c.row;
        let (xys, _) = self.equivalence(p, dl)?;
        let lr = match final_id {
            Some(id) => {
                let e = p.t.eq(r.l, r.r);
                p.emit_named(id, &[e], "cong", &[xys])
            }
            None => eq_step(p, r.l, r.r, "cong", &[xys]),
        };
        if let Some(h0) = h0 {
            return Some(p.emit(&[], "resolution", &[h0, lr], &[]));
        }
        Some(lr)
    }

    /// `(cl (= (not hz) (and (not az) (not qb))))` (F1, F2, F3 combined) and
    /// `(cl (or (not (= P Z)) (= Q Z)))` from the division lemma's instance.
    pub(crate) fn equivalence(&self, p: &mut Proof, dl: &DivLemma) -> Option<(S, S)> {
        let r = &self.c.row;
        let nyz = self.nonzero(p)?;
        let ds = self.ds(p, dl, nyz)?;
        let zhb = p.t.bits(self.sc.zh);
        let sh1 = self.c.shift_nn_n(p, &zhb)?;
        let f1 = self.f1(p, sh1)?;
        let f2 = self.f2(p, &ds, sh1)?;
        let f3 = self.f3(p, &ds)?;
        let x = p.t.not(r.hz);
        let (naz, nqb) = (p.t.not(r.az), p.t.not(r.qb));
        let y = p.t.and(&[naz, nqb]);
        let xy = p.t.eq(x, y);
        let (nx, ny) = (p.t.not(x), p.t.not(y));
        let n1 = p.emit(&[xy, nx, ny], "equiv_neg1", &[], &[]);
        let n2 = p.emit(&[xy, x, y], "equiv_neg2", &[], &[]);
        let mut prem = vec![
            Prem::Step(n1),
            Prem::Step(n2),
            Prem::Step(f1),
            Prem::Step(f2),
            Prem::Step(f3),
        ];
        prem.extend(p.gate(y));
        Some((p.derive(&[xy], &prem, &[])?, ds.zero))
    }
}
