// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The signed checked multiplication overflow identity of `2m`-bit operands
//! over `m`-bit limbs (external-codegen's i128 `checked_mul` lowering for `m = 64`,
//! with `bvsdiv` expanded by its SMT-LIB definition):
//!
//! ```text
//! (= (ite (or (not (= H Z)) (bvult LIM (bvmul |A| |B|))) #b1 #b0)
//!    (ite (or (and (not (= B Z)) (not (= SDIV A))) (and (= A MIN) (= B -1))) #b1 #b0))
//! ```
//!
//! `|A|` is `(ite (= A[n-1] #b1) (bvneg A) A)`, `H` the schoolbook high half
//! of `|A| * |B|` over the magnitudes' limbs, `LIM` the largest magnitude a
//! product of those signs may have (`MIN` when the signs differ, `MAX`
//! otherwise), and `SDIV` the four-case `bvsdiv` expansion of
//! `(bvmul A B) / D` with `D = (ite (or (= B Z) (and (= A MIN) (= B -1))) ONE B)`.
//!
//! The certificate reuses the unsigned identity over the magnitudes, with
//! `|B|` as the divisor: `H != 0` exactly when `|B| != 0` and
//! `(|A| * |B| mod 2^n) / |B| != |A|`. Every `bvsdiv` case then either IS that
//! unsigned quotient (the product's sign bit agrees with the operands' signs)
//! or cannot give back `A` (the top bit of a quotient is set only by a
//! divisor of one, and the dividend's magnitude never exceeds `MIN`).

use super::bits;
use super::row::{Order, Row};
use super::term::{Op, Terms, T};

/// The schoolbook spelling of the signed lowering over `(|B|, |A|)`'s limbs:
/// every product but `phl` is spelled with the magnitude of `A` first, and
/// the middle sum adds `plh` first.
pub(crate) const SIGNED_ORDER: Order = Order {
    swap: [true, false, true, true],
    plh_first: true,
};

pub(crate) struct Signed {
    pub(crate) m: u32,
    pub(crate) a: T,
    pub(crate) b: T,
    pub(crate) z: T,
    pub(crate) one: T,
    pub(crate) minw: T,
    pub(crate) maxw: T,
    pub(crate) neg1: T,
    pub(crate) sa: T,
    pub(crate) sb: T,
    pub(crate) na: T,
    pub(crate) nb: T,
    pub(crate) xa: T,
    pub(crate) xb: T,
    pub(crate) lo: T,
    pub(crate) lim: T,
    pub(crate) ss: T,
    pub(crate) ovl: T,
    pub(crate) ov: T,
    pub(crate) l: T,
    pub(crate) pp: T,
    pub(crate) np: T,
    pub(crate) bz: T,
    pub(crate) amin: T,
    pub(crate) bneg1: T,
    pub(crate) spec: T,
    pub(crate) dc: T,
    pub(crate) d: T,
    pub(crate) nd: T,
    pub(crate) p0: T,
    pub(crate) p1: T,
    pub(crate) d0: T,
    pub(crate) d1: T,
    pub(crate) c: [T; 3],
    /// `bvudiv` of `(P, D)`, `(-P, D)`, `(P, -D)`, `(-P, -D)`.
    pub(crate) q: [T; 4],
    /// The four `bvsdiv` case results: `q1`, `-q2`, `-q3`, `q4`.
    pub(crate) res: [T; 4],
    /// `(ite c1 q1 r2)`, `(ite c2 -q2 r3)`, `(ite c3 -q3 q4)`.
    pub(crate) ites: [T; 3],
    pub(crate) sda: T,
    pub(crate) first: T,
    pub(crate) rv: T,
    pub(crate) r: T,
}

impl Signed {
    /// The identity over the four `m`-bit limb leaves `[a_lo, a_hi, b_lo, b_hi]`,
    /// and the unsigned core row over the magnitudes' limbs.
    pub(crate) fn new(t: &mut Terms, m: u32, leaves: [T; 4]) -> (Self, Row) {
        let [a_lo, a_hi, b_lo, b_hi] = leaves;
        let a = t.concat(&[a_hi, a_lo]);
        let b = t.concat(&[b_hi, b_lo]);
        let [z, one, minw, maxw, neg1] = words(t, m);
        let (b1, b0) = (t.lit(vec![true]), t.lit(vec![false]));
        let sa = sign(t, a, b1);
        let sb = sign(t, b, b1);
        let (na, nb) = (t.neg(a), t.neg(b));
        let xa = t.ite(sa, na, a);
        let xb = t.ite(sb, nb, b);
        let core = magnitudes(t, m, xa, xb);
        let lo = t.mul(xa, xb);
        let ss = t.eq(sa, sb);
        let nss = t.not(ss);
        let lim = t.ite(nss, minw, maxw);
        let ovl = t.ult(lim, lo);
        let hz = core.hz;
        let nhz = t.not(hz);
        let ov = t.or(&[nhz, ovl]);
        let l = t.ite(ov, b1, b0);
        let pp = t.mul(a, b);
        let np = t.neg(pp);
        let bz = t.eq(b, z);
        let amin = t.eq(a, minw);
        let bneg1 = t.eq(b, neg1);
        let spec = t.and(&[amin, bneg1]);
        let dc = t.or(&[bz, spec]);
        let d = t.ite(dc, one, b);
        let nd = t.neg(d);
        let (p0, p1) = (sign(t, pp, b0), sign(t, pp, b1));
        let (d0, d1) = (sign(t, d, b0), sign(t, d, b1));
        let c = [t.and(&[p0, d0]), t.and(&[p1, d0]), t.and(&[p0, d1])];
        let q = [
            t.mk(Op::Udiv, &[pp, d]),
            t.mk(Op::Udiv, &[np, d]),
            t.mk(Op::Udiv, &[pp, nd]),
            t.mk(Op::Udiv, &[np, nd]),
        ];
        let res = [q[0], t.neg(q[1]), t.neg(q[2]), q[3]];
        let i3 = t.ite(c[2], res[2], res[3]);
        let i2 = t.ite(c[1], res[1], i3);
        let i1 = t.ite(c[0], res[0], i2);
        let sda = t.eq(i1, a);
        let (nbz, nsda) = (t.not(bz), t.not(sda));
        let first = t.and(&[nbz, nsda]);
        let rv = t.or(&[first, spec]);
        let r = t.ite(rv, b1, b0);
        let signed = Signed {
            m,
            a,
            b,
            z,
            one,
            minw,
            maxw,
            neg1,
            sa,
            sb,
            na,
            nb,
            xa,
            xb,
            lo,
            lim,
            ss,
            ovl,
            ov,
            l,
            pp,
            np,
            bz,
            amin,
            bneg1,
            spec,
            dc,
            d,
            nd,
            p0,
            p1,
            d0,
            d1,
            c,
            q,
            res,
            ites: [i1, i2, i3],
            sda,
            first,
            rv,
            r,
        };
        (signed, core)
    }

    pub(crate) fn n(&self) -> u32 {
        2 * self.m
    }
}

/// The row's constant words `[Z, ONE, MIN, MAX, -1]` of `2m` bits, each a
/// concatenation of two `m`-bit literals as the corpus spells it.
fn words(t: &mut Terms, m: u32) -> [T; 5] {
    let zm = t.lit(bits::zero(m));
    let z = t.concat(&[zm, zm]);
    let onem = t.lit(bits::from_u64(1, m));
    let one = t.concat(&[zm, onem]);
    let top = t.lit(bits::pow2(m - 1, m));
    let minw = t.concat(&[top, zm]);
    let below = t.lit(bits::mask(m - 1, m));
    let ones = t.lit(bits::mask(m, m));
    let maxw = t.concat(&[below, ones]);
    let neg1 = t.concat(&[ones, ones]);
    [z, one, minw, maxw, neg1]
}

/// `(= ((_ extract n-1 n-1) w) v)`: the sign bit of the word `w` is `v`.
fn sign(t: &mut Terms, w: T, v: T) -> T {
    let n = t.width(w);
    let x = t.extract(n - 1, n - 1, w);
    t.eq(x, v)
}

/// The unsigned core over the magnitudes' limbs: its divisor `a` is `|B|`,
/// its multiplicand `b` is `|A|`.
fn magnitudes(t: &mut Terms, m: u32, xa: T, xb: T) -> Row {
    let n = 2 * m;
    let x_lo = t.extract(m - 1, 0, xa);
    let x_hi = t.extract(n - 1, m, xa);
    let y_lo = t.extract(m - 1, 0, xb);
    let y_hi = t.extract(n - 1, m, xb);
    Row::new_ordered(t, m, [y_lo, y_hi, x_lo, x_hi], SIGNED_ORDER)
}
