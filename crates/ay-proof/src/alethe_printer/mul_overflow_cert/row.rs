// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The term shape of a checked `2m`-bit unsigned multiplication overflow test
//! over `m`-bit limbs (external-codegen's u128 `checked_mul` lowering for `m = 64`):
//!
//! ```text
//! (= (ite (not (= H 0)) #b1 #b0)
//!    (ite (and (not (= A 0)) (not (= (bvudiv (bvmul A B) A') B))) #b1 #b0))
//! ```
//!
//! where `H` is the schoolbook high half of `A * B` with its middle carry.

use super::bits;
use super::term::{Op, Sort, Terms, T};

/// How a lowering spells the schoolbook: `swap[k]` puts the `b` limb first in
/// product `k` (`pll, phl, plh, phh`), and `plh_first` adds `plh` before `phl`
/// in the middle sum, whose carry compares against `xt` plus the LATER summand.
/// The default is external-codegen's unsigned `checked_mul` spelling.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Order {
    pub(crate) swap: [bool; 4],
    pub(crate) plh_first: bool,
}

pub(crate) struct Row {
    pub(crate) m: u32,
    pub(crate) order: Order,
    pub(crate) a_lo: T,
    pub(crate) a_hi: T,
    pub(crate) b_lo: T,
    pub(crate) b_hi: T,
    pub(crate) a: T,
    pub(crate) b: T,
    pub(crate) z: T,
    pub(crate) one: T,
    pub(crate) p: T,
    pub(crate) az: T,
    pub(crate) ap: T,
    pub(crate) q: T,
    pub(crate) pll: T,
    pub(crate) phl: T,
    pub(crate) plh: T,
    pub(crate) phh: T,
    pub(crate) xt: T,
    pub(crate) mid: T,
    pub(crate) c: T,
    pub(crate) cb: T,
    pub(crate) shamt: T,
    pub(crate) sh: T,
    pub(crate) h: T,
    pub(crate) hz: T,
    pub(crate) qb: T,
    pub(crate) l: T,
    pub(crate) r: T,
}

impl Row {
    /// Build the shape over the four limb leaves (each of sort `(_ BitVec m)`).
    pub(crate) fn new(t: &mut Terms, m: u32, leaves: [T; 4]) -> Self {
        Self::new_ordered(t, m, leaves, Order::default())
    }

    /// [`Row::new`] with the products and the middle sum spelled in `order`.
    pub(crate) fn new_ordered(t: &mut Terms, m: u32, leaves: [T; 4], order: Order) -> Self {
        let [a_lo, a_hi, b_lo, b_hi] = leaves;
        let n = 2 * m;
        let xl = |t: &mut Terms, v: T| t.zext(m, v);
        let a = t.concat(&[a_hi, a_lo]);
        let b = t.concat(&[b_hi, b_lo]);
        let zm = t.lit(bits::zero(m));
        let z = t.concat(&[zm, zm]);
        let onem = t.lit(bits::from_u64(1, m));
        let one = t.concat(&[zm, onem]);
        let p = t.mul(a, b);
        let az = t.eq(a, z);
        let ap = t.ite(az, one, a);
        let q = t.mk(Op::Udiv, &[p, ap]);
        let (xal, xah, xbl, xbh) = (xl(t, a_lo), xl(t, a_hi), xl(t, b_lo), xl(t, b_hi));
        let prod = |t: &mut Terms, k: usize, x: T, y: T| {
            if order.swap[k] {
                t.mul(y, x)
            } else {
                t.mul(x, y)
            }
        };
        let pll = prod(t, 0, xal, xbl);
        let phl = prod(t, 1, xah, xbl);
        let plh = prod(t, 2, xal, xbh);
        let phh = prod(t, 3, xah, xbh);
        let tt = t.extract(n - 1, m, pll);
        let xt = xl(t, tt);
        let (first, second) = if order.plh_first {
            (plh, phl)
        } else {
            (phl, plh)
        };
        let s1 = t.add(&[xt, first]);
        let mid = t.add(&[s1, second]);
        let mid0 = t.add(&[xt, second]);
        let c = t.ult(mid, mid0);
        let (b1, b0) = (t.lit(bits::from_u64(1, 1)), t.lit(bits::zero(1)));
        let cb = t.ite(c, b1, b0);
        let mlit = t.lit(bits::from_u64(u64::from(m), m));
        let shamt = t.zext(m, mlit);
        let cbx = t.zext(n - 1, cb);
        let sh = t.mk(Op::Shl, &[cbx, shamt]);
        let xhe = t.extract(n - 1, m, mid);
        let xh = xl(t, xhe);
        let h1 = t.add(&[xh, phh]);
        let h = t.add(&[h1, sh]);
        let hz = t.eq(h, z);
        let qb = t.eq(q, b);
        let nhz = t.not(hz);
        let l = t.ite(nhz, b1, b0);
        let naz = t.not(az);
        let nqb = t.not(qb);
        let cond = t.and(&[naz, nqb]);
        let r = t.ite(cond, b1, b0);
        Row {
            m,
            order,
            a_lo,
            a_hi,
            b_lo,
            b_hi,
            a,
            b,
            z,
            one,
            p,
            az,
            ap,
            q,
            pll,
            phl,
            plh,
            phh,
            xt,
            mid,
            c,
            cb,
            shamt,
            sh,
            h,
            hz,
            qb,
            l,
            r,
        }
    }

    pub(crate) fn n(&self) -> u32 {
        2 * self.m
    }

    /// The middle sum's two cross products, in the order they are added.
    pub(crate) fn cross(&self) -> (T, T) {
        if self.order.plh_first {
            (self.plh, self.phl)
        } else {
            (self.phl, self.plh)
        }
    }

    /// Leaves of sort `(_ BitVec m)` named as they print in the document.
    pub(crate) fn leaves(t: &mut Terms, m: u32, names: [&str; 4]) -> [T; 4] {
        names.map(|nm| t.var(nm, Sort::Bv(m)))
    }
}
