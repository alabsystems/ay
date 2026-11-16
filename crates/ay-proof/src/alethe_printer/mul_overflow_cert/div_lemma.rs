// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The checker's divider as one quantified lemma over `n`-bit words:
//!
//! ```text
//! (forall ((x (_ BitVec n)) (y (_ BitVec n)))
//!   (or (not (not YZ))
//!       (and (= (bvadd (bvmul (concat 0 Q) (concat 0 y)) (concat 0 R)) (concat 0 x))
//!            (bvult R y)
//!            (or (not (= ((_ extract n-1 n-1) Q) #b1))
//!                (and (= y ONE) (= ((_ extract n-1 n-1) x) #b1)))
//!            (or (not (= x Z)) (= Q Z)))))
//! ```
//!
//! with `Q = (bvudiv x y)`, `R = (bvurem x y)` and `YZ` the divider's own
//! zero test of `y`'s bits. Its proof bit-blasts the divider once, follows it
//! stage by stage through the stage lemma, and reads the top quotient bit off
//! the deepest stage, which compares the dividend's top bit alone against the
//! divisor; a zero dividend falls short of the divisor already at the first
//! stage, so every quotient bit is false. Every use is an instance, so the divider circuit is printed once
//! in the whole certificate — the pinned checker normalizes every term of the
//! document within a fixed work budget. `Z` and `ONE` are spelled as the rows
//! spell them (`(concat 0 0)` and `(concat 0 1)` of `m`-bit limbs), so an
//! instance speaks of the row's own atoms.

use super::bits;
use super::clean::{udiv_stage, udiv_stages};
use super::div::{z, DivStage};
use super::div_spec::division_spec;
use super::helpers::{
    conjoin, eq_step, forall_lemma, instantiate, project, split_or, symm, trans, transfer, word_eq,
};
use super::horner::body_from_clause;
use super::lin::{atom_bits, Blaster};
use super::local::under;
use super::proof::{Prem, Proof, S};
use super::term::{Op, Sort, T};

pub(crate) struct DivLemma {
    /// `(cl (forall (x y) BODY))`.
    pub(crate) fact: S,
}

/// The row's zero and one words of `2m` bits.
pub(crate) fn zero_one(p: &mut Proof<'_>, m: u32) -> (T, T) {
    let zm = p.t.lit(bits::zero(m));
    let onem = p.t.lit(bits::from_u64(1, m));
    (p.t.concat(&[zm, zm]), p.t.concat(&[zm, onem]))
}

/// `(= ((_ extract n-1 n-1) w) #b1)`.
pub(crate) fn top_set(p: &mut Proof<'_>, w: T) -> T {
    let n = p.t.width(w);
    let x = p.t.extract(n - 1, n - 1, w);
    let b1 = p.t.lit(vec![true]);
    p.t.eq(x, b1)
}

/// The zero test of `y`'s bits as the checker's divider spells it.
pub(crate) fn zero_test(p: &mut Proof<'_>, y: T) -> T {
    let ff = p.t.ff;
    let tests: Vec<T> = p.t.bits(y).iter().map(|&b| p.t.eq(b, ff)).collect();
    p.t.and(&tests)
}

/// The lemma's terms over the words `x`, `y`.
struct Words {
    x: T,
    y: T,
    q: T,
    r: T,
    yz: T,
    u: T,
    qt: T,
    yone: T,
    xt: T,
    both: T,
    top: T,
    xz: T,
    qz: T,
    zero_div: T,
    conj: T,
}

impl Words {
    fn new(p: &mut Proof<'_>, m: u32, x: T, y: T) -> Self {
        let n = 2 * m;
        let q = p.t.mk(Op::Udiv, &[x, y]);
        let r = p.t.mk(Op::Urem, &[x, y]);
        let yz = zero_test(p, y);
        let (zq, zy, zr, zx) = (z(p, n, q), z(p, n, y), z(p, n, r), z(p, n, x));
        let prod = p.t.mul(zq, zy);
        let sum = p.t.add(&[prod, zr]);
        let e = p.t.eq(sum, zx);
        let u = p.t.ult(r, y);
        let (zero, one) = zero_one(p, m);
        let qt = top_set(p, q);
        let yone = p.t.eq(y, one);
        let xt = top_set(p, x);
        let both = p.t.and(&[yone, xt]);
        let nqt = p.t.not(qt);
        let top = p.t.or(&[nqt, both]);
        let xz = p.t.eq(x, zero);
        let qz = p.t.eq(q, zero);
        let nxz = p.t.not(xz);
        let zero_div = p.t.or(&[nxz, qz]);
        let conj = p.t.and(&[e, u, top, zero_div]);
        Words {
            x,
            y,
            q,
            r,
            yz,
            u,
            qt,
            yone,
            xt,
            both,
            top,
            xz,
            qz,
            zero_div,
            conj,
        }
    }
}

impl DivLemma {
    pub(crate) fn new(p: &mut Proof<'_>, m: u32, dstage: &DivStage, prefix: &str) -> Option<Self> {
        let n = 2 * m;
        let x = p.t.var(&format!("{prefix}x"), Sort::Bv(n));
        let y = p.t.var(&format!("{prefix}y"), Sort::Bv(n));
        let w = Words::new(p, m, x, y);
        let nyz = p.t.not(w.yz);
        let nnyz = p.t.not(nyz);
        let body = p.t.or(&[nnyz, w.conj]);
        let fact = forall_lemma(p, &[x, y], |p| {
            let sp = p.anchor(&[]);
            let h = p.assume(nyz);
            prove(p, dstage, &w, h)?;
            let spc = p.close(sp, &[nnyz, w.conj], "subproof", &[h]);
            Some((body, body_from_clause(p, body, spc)?))
        })?;
        Some(DivLemma { fact })
    }

    /// The instance at the words `x`, `y` split into its clause
    /// `(cl (not (not YZ)) (and E U TOP ZERO))`.
    pub(crate) fn split_instance(&self, p: &mut Proof<'_>, x: T, y: T) -> Option<S> {
        let i = instantiate(p, self.fact, &[x, y])?;
        Some(split_or(p, i))
    }

    /// The conjuncts `(cl E)`, `(cl U)`, `(cl TOP)`, `(cl ZERO)` of a split
    /// instance given the step `(cl (not YZ))` of its divisor's zero test.
    pub(crate) fn conjuncts(p: &mut Proof<'_>, split: S, nz: S) -> Option<[S; 4]> {
        let conj = *p.clause(split).last()?;
        let c = p.derive(&[conj], &[Prem::Step(split), Prem::Step(nz)], &[])?;
        Some([
            project(p, c, 0)?,
            project(p, c, 1)?,
            project(p, c, 2)?,
            project(p, c, 3)?,
        ])
    }
}

/// Under `(not YZ)` (the step `h`), the step `(cl (and E U TOP ZERO))`.
fn prove(p: &mut Proof<'_>, dstage: &DivStage, w: &Words, h: S) -> Option<S> {
    let n = dstage.n;
    let tt = p.t.tt;
    let (xb, yb) = (p.t.bits(w.x), p.t.bits(w.y));
    let (q0, r0, inv0) = division_spec(p, dstage, &xb, &yb, h)?;
    let quot: Vec<T> = q0.iter().map(|&b| p.t.ite(w.yz, tt, b)).collect();
    let rem: Vec<T> = r0
        .iter()
        .zip(&xb)
        .map(|(&b, &x)| p.t.ite(w.yz, x, b))
        .collect();
    let (qw, rw) = (p.t.bb(&quot), p.t.bb(&rem));
    let bq = eq_step(p, w.q, qw, "bitblast_udiv", &[]);
    let br = eq_step(p, w.r, rw, "bitblast_urem", &[]);
    // under `(not YZ)` the divider's words are the stage-0 words
    let (q0w, r0w) = (p.t.bb(&q0), p.t.bb(&r0));
    let same = |p: &mut Proof<'_>, out: &[T], stage: &[T]| -> Option<Vec<S>> {
        (0..n as usize)
            .map(|i| {
                let e = p.t.eq(out[i], stage[i]);
                let mut prem = p.gate(out[i]);
                prem.extend(p.gate(e));
                prem.push(Prem::Step(h));
                p.derive(&[e], &prem, &[])
            })
            .collect()
    };
    let qf = same(p, &quot, &q0)?;
    let rf = same(p, &rem, &r0)?;
    let qq = word_eq(p, qw, q0w, &qf)?;
    let rr = word_eq(p, rw, r0w, &rf)?;
    let uq = trans(p, &[bq, qq]);
    let ur = trans(p, &[br, rr]);
    // E and U over the lemma's own words, from the stage-0 invariant
    let (xw, yw) = (p.t.bb(&xb), p.t.bb(&yb));
    let vx = eq_step(p, w.x, xw, "bitblast_var", &[]);
    let vy = eq_step(p, w.y, yw, "bitblast_var", &[]);
    let e0 = project(p, inv0, 0)?;
    let u0 = project(p, inv0, 1)?;
    let (zq, zy, zr, zx) = (z(p, n, w.q), z(p, n, w.y), z(p, n, w.r), z(p, n, w.x));
    let (zq0, zyw, zr0, zxw) = (z(p, n, q0w), z(p, n, yw), z(p, n, r0w), z(p, n, xw));
    let cq = eq_step(p, zq, zq0, "cong", &[uq]);
    let cy = eq_step(p, zy, zyw, "cong", &[vy]);
    let cr = eq_step(p, zr, zr0, "cong", &[ur]);
    let cx = eq_step(p, zx, zxw, "cong", &[vx]);
    let (m1, m0) = (p.t.mul(zq, zy), p.t.mul(zq0, zyw));
    let cm = eq_step(p, m1, m0, "cong", &[cq, cy]);
    let (s1, s0) = (p.t.add(&[m1, zr]), p.t.add(&[m0, zr0]));
    let cs = eq_step(p, s1, s0, "cong", &[cm, cr]);
    let cxs = symm(p, cx);
    let e = trans(p, &[cs, e0, cxs]);
    let u0w = p.t.ult(r0w, yw);
    let cu = eq_step(p, w.u, u0w, "cong", &[ur, vy]);
    let u = transfer(p, cu, u0)?;
    let top = top_bit(p, w, &quot, bq, h)?;
    let zero = zero_dividend(p, w, &quot, bq, h)?;
    conjoin(p, w.conj, &[e, u, top, zero])
}

/// Under `(not YZ)`: `(cl (or (not XZ) QZ))`. With every dividend bit false,
/// the first stage's comparison `x < y` holds (the divisor is not zero), and
/// that stage's quotient is `(ite xlt false ..)` bit for bit.
fn zero_dividend(p: &mut Proof<'_>, w: &Words, quot: &[T], bq: S, h: S) -> Option<S> {
    let (tt, ff) = (p.t.tt, p.t.ff);
    let (xb, yb) = (p.t.bits(w.x), p.t.bits(w.y));
    let stages = udiv_stages(&mut p.t, &xb, &yb);
    let st = udiv_stage(&mut p.t, &xb, &yb, &stages[1].0, &stages[1].1);
    if stages[0].0 != st.quot {
        return None;
    }
    let inner = under(p, &[w.xz], w.qz, |p, hs| {
        let mut b = Blaster::new(&[], &[(w.q, quot.to_vec(), bq)]);
        let mut prem = vec![Prem::Step(h), Prem::Step(hs[0])];
        prem.extend(p.gate(w.yz));
        for c in p.t.args(w.yz).to_vec() {
            prem.extend(p.gate(c));
        }
        for a in [w.xz, w.qz] {
            let (eqs, circ, _) = atom_bits(p, &mut b, a)?;
            let e = p.unit(eqs);
            prem.push(Prem::Step(eqs));
            prem.extend(p.gate(e));
            prem.extend(p.gate(circ));
            for c in p.t.args(circ).to_vec() {
                prem.extend(p.gate(c));
            }
        }
        for (&q, &s) in quot.iter().zip(&st.quot) {
            prem.extend(p.gate(q));
            prem.extend(p.gate(s));
        }
        for &c in &st.c_lt {
            prem.extend(p.gate(c));
            for a in p.t.args(c).to_vec() {
                prem.extend(p.gate(a));
                for g in p.t.args(a).to_vec() {
                    if matches!(p.t.op(g), Op::Xor) {
                        prem.extend(p.gate(g));
                    }
                }
            }
        }
        prem.extend(p.gate(tt));
        prem.extend(p.gate(ff));
        let lt = p.derive(&[st.xlt], &prem, &[])?;
        prem.push(Prem::Step(lt));
        p.derive(&[w.qz], &prem, &[])
    })?;
    let mut prem = p.gate(w.zero_div);
    prem.push(Prem::Step(inner));
    p.derive(&[w.zero_div], &prem, &[])
}

/// Under `(not YZ)`: `(cl (or (not QT) (and YONE XT)))`. The top quotient bit
/// is `(ite xlt false ..)` at every stage down to the deepest, whose
/// comparison of `[x_{n-1}, 0..]` with `y` succeeds only for `y <= x_{n-1}`.
fn top_bit(p: &mut Proof<'_>, w: &Words, quot: &[T], bq: S, h: S) -> Option<S> {
    let n = quot.len();
    let (tt, ff) = (p.t.tt, p.t.ff);
    let (xb, yb) = (p.t.bits(w.x), p.t.bits(w.y));
    let stages = udiv_stages(&mut p.t, &xb, &yb);
    let mut top = vec![ff; n];
    top[0] = xb[n - 1];
    let zeros = vec![ff; n];
    let st = udiv_stage(&mut p.t, &top, &yb, &zeros, &zeros);
    if stages[n - 1].0 != st.quot {
        return None;
    }
    let inner = under(p, &[w.qt], w.both, |p, hs| {
        let mut b = Blaster::new(&[], &[(w.q, quot.to_vec(), bq)]);
        let mut prem = vec![Prem::Step(h), Prem::Step(hs[0])];
        prem.extend(p.gate(w.yz));
        for c in p.t.args(w.yz).to_vec() {
            prem.extend(p.gate(c));
        }
        for a in [w.qt, w.yone, w.xt] {
            let (eqs, circ, _) = atom_bits(p, &mut b, a)?;
            let e = p.unit(eqs);
            prem.push(Prem::Step(eqs));
            prem.extend(p.gate(e));
            prem.extend(p.gate(circ));
            if matches!(p.t.op(circ), Op::And) {
                for c in p.t.args(circ).to_vec() {
                    prem.extend(p.gate(c));
                }
            }
        }
        // the top quotient bit down to the deepest stage: each stage's bit
        // is `(ite xlt false q1)`, its `q1` the next stage's bit one lower
        prem.extend(p.gate(quot[n - 1]));
        for (k, stage) in stages.iter().enumerate().take(n) {
            prem.extend(p.gate(stage.0[n - 1 - k]));
        }
        for &c in &st.c_lt {
            prem.extend(p.gate(c));
            for a in p.t.args(c).to_vec() {
                prem.extend(p.gate(a));
                for g in p.t.args(a).to_vec() {
                    if matches!(p.t.op(g), Op::Xor) {
                        prem.extend(p.gate(g));
                    }
                }
            }
        }
        prem.extend(p.gate(tt));
        prem.extend(p.gate(ff));
        let nxlt = p.t.not(st.xlt);
        let lt = p.derive(&[nxlt], &prem, &[])?;
        prem.push(Prem::Step(lt));
        prem.extend(p.gate(w.both));
        p.derive(&[w.both], &prem, &[])
    })?;
    let mut prem = p.gate(w.top);
    prem.push(Prem::Step(inner));
    p.derive(&[w.top], &prem, &[])
}
