// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact replicas of the pinned checker's bit-blasting constructions
//! (`ripple_carry_adder`, `bitblast_ult`, `bitblast_udiv_urem_rec`,
//! `bitblast_shift_op`), so the terms this lane prints are the terms the
//! checker builds.

use super::term::{Terms, T};

pub(crate) struct Adder {
    pub(crate) sum: Vec<T>,
    pub(crate) carries: Vec<T>,
}

impl Adder {
    pub(crate) fn carry_out(&self) -> T {
        self.carries[self.carries.len() - 1]
    }
}

pub(crate) fn rca(t: &mut Terms, x: &[T], y: &[T], carry: Option<T>) -> Adder {
    let size = x.len();
    let mut carries = vec![carry.unwrap_or(t.ff)];
    for i in 1..=size {
        let a = t.and(&[x[i - 1], y[i - 1]]);
        let xy = t.xor(x[i - 1], y[i - 1]);
        let b = t.and(&[xy, carries[i - 1]]);
        carries.push(t.or(&[a, b]));
    }
    let sum = (0..size)
        .map(|i| {
            let xy = t.xor(x[i], y[i]);
            t.xor(xy, carries[i])
        })
        .collect();
    Adder { sum, carries }
}

/// `bitblast_neg`: the bits of `(bvneg x)` and the carries (`carries[0]` is
/// `true`; there is no carry out).
pub(crate) fn neg_bits(t: &mut Terms, x: &[T]) -> (Vec<T>, Vec<T>) {
    let ff = t.ff;
    let mut carries = vec![t.tt];
    for i in 1..x.len() {
        let nx = t.not(x[i - 1]);
        let a = t.and(&[nx, ff]);
        let xr = t.xor(nx, ff);
        let b = t.and(&[xr, carries[i - 1]]);
        carries.push(t.or(&[a, b]));
    }
    let bits = (0..x.len())
        .map(|i| {
            let nx = t.not(x[i]);
            let xr = t.xor(nx, ff);
            t.xor(xr, carries[i])
        })
        .collect();
    (bits, carries)
}

/// `bitblast_ult`: the result and the comparator over bits `0..=i` for each `i`.
pub(crate) fn ult_bits(t: &mut Terms, x: &[T], y: &[T]) -> Vec<T> {
    let nx = t.not(x[0]);
    let mut res = t.and(&[nx, y[0]]);
    let mut chain = vec![res];
    for i in 1..x.len() {
        let e = t.eq(x[i], y[i]);
        let a = t.and(&[e, res]);
        let nxi = t.not(x[i]);
        let b = t.and(&[nxi, y[i]]);
        res = t.or(&[a, b]);
        chain.push(res);
    }
    chain
}

pub(crate) struct Stage {
    pub(crate) quot: Vec<T>,
    pub(crate) rem: Vec<T>,
    pub(crate) q1_0: T,
    pub(crate) r1sa: Vec<T>,
    pub(crate) rmy: Vec<T>,
    pub(crate) r1sa2: Vec<T>,
    pub(crate) c_sa: Vec<T>,
    pub(crate) c_my: Vec<T>,
    pub(crate) c_lt: Vec<T>,
    pub(crate) co1: T,
    pub(crate) xlt: T,
}

/// One level of `bitblast_udiv_urem_rec` given the result `(q2, r2)` for `x >> 1`.
pub(crate) fn udiv_stage(t: &mut Terms, x: &[T], y: &[T], q2: &[T], r2: &[T]) -> Stage {
    let n = x.len();
    let mut q1: Vec<T> = std::iter::once(t.ff)
        .chain(q2[..n - 1].iter().copied())
        .collect();
    let r1: Vec<T> = std::iter::once(t.ff)
        .chain(r2[..n - 1].iter().copied())
        .collect();
    let tt = t.tt;
    let e0 = t.eq(x[0], tt);
    let odd = t.ite(e0, tt, t.ff);
    let zeros = vec![t.ff; n];
    let sa = rca(t, &r1, &zeros, Some(odd));
    let ny: Vec<T> = y.iter().map(|&b| t.not(b)).collect();
    let my = rca(t, &sa.sum, &ny, Some(tt));
    let co1 = my.carry_out();
    let sign = t.not(co1);
    q1[0] = t.ite(sign, q1[0], tt);
    let r1sa2: Vec<T> = (0..n).map(|i| t.ite(sign, sa.sum[i], my.sum[i])).collect();
    let lt = rca(t, x, &ny, Some(tt));
    let xlt = t.not(lt.carry_out());
    let ff = t.ff;
    let quot = (0..n).map(|i| t.ite(xlt, ff, q1[i])).collect();
    let rem = (0..n).map(|i| t.ite(xlt, x[i], r1sa2[i])).collect();
    Stage {
        quot,
        rem,
        q1_0: q1[0],
        r1sa: sa.sum,
        rmy: my.sum,
        r1sa2,
        c_sa: sa.carries,
        c_my: my.carries,
        c_lt: lt.carries,
        co1,
        xlt,
    }
}

/// `bitblast_udiv_urem_rec`: the quotient/remainder of `x >> k` for every stage `k`.
pub(crate) fn udiv_stages(t: &mut Terms, x: &[T], y: &[T]) -> Vec<(Vec<T>, Vec<T>)> {
    let n = x.len();
    let mut shifted = vec![x.to_vec()];
    for k in 1..=n {
        let mut s: Vec<T> = x[k.min(n)..].to_vec();
        s.resize(n, t.ff);
        shifted.push(s);
    }
    // the recursion bottoms out when every bit is `false`
    let mut q = vec![t.ff; n];
    let mut r = vec![t.ff; n];
    let mut stages = vec![(q.clone(), r.clone()); n + 1];
    for k in (0..n).rev() {
        if shifted[k].iter().all(|&b| b == t.ff) {
            continue;
        }
        let st = udiv_stage(t, &shifted[k], y, &q, &r);
        q = st.quot;
        r = st.rem;
        stages[k] = (q.clone(), r.clone());
    }
    stages
}

/// `(and (= x_i y_i) ..)` as `bitblast_equal` builds it.
pub(crate) fn bb_equal(t: &mut Terms, x: &[T], y: &[T]) -> T {
    let eqs: Vec<T> = x.iter().zip(y).map(|(&a, &b)| t.eq(a, b)).collect();
    if eqs.len() == 1 {
        eqs[0]
    } else {
        t.and(&eqs)
    }
}

pub(crate) fn const_bits(t: &Terms, v: &[bool]) -> Vec<T> {
    v.iter().map(|&b| if b { t.tt } else { t.ff }).collect()
}

/// `bitblast_shift_op` for `bvshl` on operand bits `x`, amount bits `y` and the
/// checker's `(bvult y size)` comparator over `size`'s `@bit_of` projections.
pub(crate) fn shl_bits(t: &mut Terms, x: &[T], y: &[T], size_bits: &[T]) -> Vec<T> {
    let size = x.len();
    let yu = ult_bits(t, y, size_bits);
    let y_ult = yu[yu.len() - 1];
    let k = size.ilog2() as usize + usize::from(!size.is_power_of_two());
    let mut res = x.to_vec();
    for (s, &ys) in y.iter().enumerate().take(k) {
        let prev = res.clone();
        let th = 1usize << s;
        for i in 0..size {
            let ff = t.ff;
            res[i] = if i < th {
                t.ite(ys, ff, prev[i])
            } else {
                t.ite(ys, prev[i - th], prev[i])
            };
        }
    }
    let ff = t.ff;
    res.iter().map(|&b| t.ite(y_ult, b, ff)).collect()
}
