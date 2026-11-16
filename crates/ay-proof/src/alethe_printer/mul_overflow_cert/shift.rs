// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(bvmul 2^k W) = W shifted by k`, proved once per width as quantified
//! lemmas: a doubling step (an adder fact), then shifts built from it.

use super::bits;
use super::helpers::{eq_step, forall_lemma, instantiate, trans};
use super::lin::{lin1, LinOpts};
use super::proof::{Proof, S};
use super::term::{Sort, T};

/// A proved `(forall w (= (bvmul 2^k bb(w)) bb(F*k ++ w)))` (k = 1 is the doubling `bvadd`).
pub(crate) struct ShiftLemma {
    pub(crate) w: u32,
    pub(crate) k: u32,
    fact: S,
}

fn vars(p: &mut Proof<'_>, prefix: &str, w: u32) -> Vec<T> {
    (0..w)
        .map(|i| p.t.var(&format!("{prefix}{i}"), Sort::Bool))
        .collect()
}

fn shifted(p: &Proof<'_>, bits: &[T], k: u32) -> Vec<T> {
    let mut out = vec![p.t.ff; k as usize];
    out.extend(&bits[..bits.len() - k as usize]);
    out
}

impl ShiftLemma {
    /// `(forall w (= (bvadd W W) (W << 1)))`.
    pub(crate) fn doubling(p: &mut Proof<'_>, w: u32, prefix: &str) -> Option<Self> {
        let v = vars(p, prefix, w);
        let ww = p.t.bb(&v);
        let sh = shifted(p, &v, 1);
        let ws = p.t.bb(&sh);
        let sum = p.t.add(&[ww, ww]);
        let body = p.t.eq(sum, ws);
        let fact = forall_lemma(p, &v, |p| {
            Some((body, lin1(p, &[], body, &LinOpts::default())?))
        })?;
        Some(ShiftLemma { w, k: 1, fact })
    }

    /// `(forall w (= (bvmul 2^(k*steps) W) (W << k*steps)))` from a proved `base` shift by `k`.
    pub(crate) fn power(
        p: &mut Proof<'_>,
        base: &ShiftLemma,
        steps: u32,
        prefix: &str,
    ) -> Option<Self> {
        let v = vars(p, prefix, base.w);
        let k = base.k * steps;
        let ww = p.t.bb(&v);
        let c = p.t.lit(bits::pow2(k, base.w));
        let lhs = p.t.mul(c, ww);
        let sh = shifted(p, &v, k);
        let rhs = p.t.bb(&sh);
        let body = p.t.eq(lhs, rhs);
        let fact = forall_lemma(p, &v, |p| Some((body, base.chain(p, &v, steps)?)))?;
        Some(ShiftLemma { w: base.w, k, fact })
    }

    /// One instance: `(cl (= (bvmul 2^k bb(bits)) bb(bits << k)))` (or the doubling `bvadd` form).
    pub(crate) fn inst(&self, p: &mut Proof<'_>, b: &[T]) -> Option<S> {
        instantiate(p, self.fact, b)
    }

    /// `(= (bvmul 2^(k*steps) bb(b)) bb(b << k*steps))` by `steps` chained instances.
    pub(crate) fn chain(&self, p: &mut Proof<'_>, b: &[T], steps: u32) -> Option<S> {
        let w = self.w;
        let wb = p.t.bb(b);
        let mut cur = b.to_vec();
        let mut prev: Option<S> = None;
        for j in 0..steps {
            let wj = p.t.bb(&cur);
            let d = self.inst(p, &cur)?;
            let wn = p.t.args(p.unit(d))[1];
            let step = if self.k == 1 {
                self.doubling_step(p, wb, wj, wn, j, prev, d)
            } else {
                self.power_step(p, wb, wj, wn, j, prev, d)
            };
            prev = Some(step);
            cur = p.t.bits(wn);
        }
        let _ = w;
        prev
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the bit-shift recurrence terms and proof premises are positional by construction"
    )]
    fn doubling_step(
        &self,
        p: &mut Proof<'_>,
        wb: T,
        wj: T,
        wn: T,
        j: u32,
        prev: Option<S>,
        d: S,
    ) -> S {
        let w = self.w;
        let two = p.t.lit(bits::pow2(1, w));
        let target_c = p.t.lit(bits::pow2(j + 1, w));
        let lhs = p.t.mul(target_c, wb);
        match prev {
            None => {
                let sum = p.t.add(&[wb, wb]);
                let p1 = eq_step(p, lhs, sum, "poly_simp", &[]);
                trans(p, &[p1, d])
            }
            Some(prev) => {
                let cj = p.t.lit(bits::pow2(j, w));
                let a = p.t.mul(cj, wb);
                let ta = p.t.mul(two, a);
                let p1 = eq_step(p, lhs, ta, "poly_simp", &[]);
                let tw = p.t.mul(two, wj);
                let c1 = eq_step(p, ta, tw, "cong", &[prev]);
                let sum = p.t.add(&[wj, wj]);
                let p2 = eq_step(p, tw, sum, "poly_simp", &[]);
                let _ = wn;
                trans(p, &[p1, c1, p2, d])
            }
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the bit-shift recurrence terms and proof premises are positional by construction"
    )]
    fn power_step(
        &self,
        p: &mut Proof<'_>,
        wb: T,
        wj: T,
        wn: T,
        j: u32,
        prev: Option<S>,
        d: S,
    ) -> S {
        let (w, s) = (self.w, self.k);
        let _ = wn;
        match prev {
            None => d,
            Some(prev) => {
                let base_c = p.t.lit(bits::pow2(s, w));
                let lhs_c = p.t.lit(bits::pow2(s * (j + 1), w));
                let cj = p.t.lit(bits::pow2(s * j, w));
                let lhs = p.t.mul(lhs_c, wb);
                let a = p.t.mul(cj, wb);
                let ba = p.t.mul(base_c, a);
                let p1 = eq_step(p, lhs, ba, "poly_simp", &[]);
                let bw = p.t.mul(base_c, wj);
                let c1 = eq_step(p, ba, bw, "cong", &[prev]);
                trans(p, &[p1, c1, d])
            }
        }
    }
}

/// A shift by `2*k` as two chained instances of a shift by `k`.
pub(crate) fn double_shift(p: &mut Proof<'_>, sh: &ShiftLemma, b: &[T]) -> Option<S> {
    let (k, w) = (sh.k, sh.w);
    let s1 = sh.inst(p, b)?;
    let wb = p.t.bb(b);
    let b1 = p.t.args(p.unit(s1))[1];
    let b1bits = p.t.bits(b1);
    let s2 = sh.inst(p, &b1bits)?;
    let ck = p.t.lit(bits::pow2(k, w));
    let c2k = p.t.lit(bits::pow2(2 * k, w));
    let lhs = p.t.mul(c2k, wb);
    let inner = p.t.mul(ck, wb);
    let outer = p.t.mul(ck, inner);
    let p1 = eq_step(p, lhs, outer, "poly_simp", &[]);
    let kb1 = p.t.mul(ck, b1);
    let c = eq_step(p, outer, kb1, "cong", &[s1]);
    Some(trans(p, &[p1, c, s2]))
}
