// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The divider's specification: the base stage and the chain of quantified
//! stage instances from the most significant bit down to the dividend itself.

use super::bits;
use super::clean::{udiv_stages, ult_bits};
use super::div::{gates_rec, inv, z, DivStage};
use super::helpers::{eq_step, instantiate, split_or, symm, trans, transfer};
use super::horner::{and_from, ground};
use super::proof::{Prem, Proof, S};
use super::term::T;

/// The base invariant (stage `n`: everything zero, bound 0) and the chain of
/// stage instances down to `x` itself; returns `(quotient bits, remainder bits, step)`.
pub(crate) fn division_spec(
    p: &mut Proof<'_>,
    ds: &DivStage,
    xb: &[T],
    yb: &[T],
    nz: S,
) -> Option<(Vec<T>, Vec<T>, S)> {
    let stages = udiv_stages(&mut p.t, xb, yb);
    division_spec_over(p, ds, xb, yb, nz, &stages)
}

/// [`division_spec`] along the given stage values (`stages[k]` the quotient
/// and remainder bits of `x >> k`), each carried to the next by one instance
/// of the quantified stage lemma. A stage that is not the checker's divider
/// step from the one above it carries no invariant: `None`.
pub(crate) fn division_spec_over(
    p: &mut Proof<'_>,
    ds: &DivStage,
    xb: &[T],
    yb: &[T],
    nz: S,
    stages: &[(Vec<T>, Vec<T>)],
) -> Option<(Vec<T>, Vec<T>, S)> {
    let n = ds.n;
    if stages.len() != n as usize + 1 {
        return None;
    }
    let ff = p.t.ff;
    let ck = |k: u32| bits::mask(n - k, n);
    let c_n = p.t.lit(ck(n));
    let mut fact = base(p, n, yb, c_n, nz)?;
    for k in (0..n).rev() {
        let (qk1, rk1) = &stages[k as usize + 1];
        let mut xk: Vec<T> = xb[k as usize..].to_vec();
        xk.resize(n as usize, ff);
        let mut args = qk1.clone();
        args.extend(rk1);
        args.extend(&xk);
        args.extend(yb);
        args.push(p.t.lit(ck(k)));
        args.push(p.t.lit(ck(k + 1)));
        let inst = instantiate(p, ds.fact, &args)?;
        let parts = split_or(p, inst);
        let ia = p.t.args(p.unit(inst)).to_vec();
        let kt = p.t.args(ia[1])[0];
        let kf = ground(p, kt)?;
        fact = p.derive(
            &[ia[3]],
            &[
                Prem::Step(parts),
                Prem::Step(nz),
                Prem::Step(kf),
                Prem::Step(fact),
            ],
            &[],
        )?;
    }
    let (q0, r0) = stages[0].clone();
    Some((q0, r0, fact))
}

fn base(p: &mut Proof<'_>, n: u32, yb: &[T], c_n: T, nz: S) -> Option<S> {
    let nn = 2 * n;
    let ff = p.t.ff;
    let zeros = vec![ff; n as usize];
    let inv0 = inv(p, n, &zeros, &zeros, &zeros, yb, c_n);
    let parts = p.t.args(inv0).to_vec();
    let zw = p.t.bb(&zeros);
    let yw = p.t.bb(yb);
    let (zz, zy) = (z(p, n, zw), z(p, n, yw));
    let l0 = p.t.lit(bits::zero(nn));
    let zze = eq_step(p, zz, l0, "evaluate", &[]);
    let (ml, mr) = (p.t.mul(zz, zy), p.t.mul(l0, zy));
    let c1 = eq_step(p, ml, mr, "cong", &[zze]);
    let (al, ar) = (p.t.add(&[ml, zz]), p.t.add(&[mr, l0]));
    let c2 = eq_step(p, al, ar, "cong", &[c1, zze]);
    let c3 = eq_step(p, ar, l0, "poly_simp", &[]);
    let zzes = symm(p, zze);
    let eb = trans(p, &[c2, c3, zzes]);
    let ch = ult_bits(&mut p.t, &zeros, yb);
    let bu = eq_step(p, parts[1], ch[ch.len() - 1], "bitblast_ult", &[]);
    let mut prem = Vec::new();
    for &g in &ch {
        prem.extend(gates_rec(p, g, 3));
    }
    let yeqs: Vec<T> = yb.iter().map(|&b| p.t.eq(b, ff)).collect();
    let yz = p.t.and(&yeqs);
    prem.extend(p.gate(yz));
    for &e in &yeqs {
        prem.extend(p.gate(e));
    }
    let tt = p.t.tt;
    prem.extend(p.gate(ff));
    prem.extend(p.gate(tt));
    prem.push(Prem::Step(nz));
    let ub0 = p.derive(&[ch[ch.len() - 1]], &prem, &[])?;
    let ub = transfer(p, bu, ub0)?;
    let nu = ground_not(p, parts[2])?;
    let nq = ground_not(p, parts[3])?;
    and_from(p, inv0, &[eb, ub, nu, nq])
}

/// `(cl (not u))` for a ground comparison `u` that evaluates to false; `lit` is `(not u)`.
fn ground_not(p: &mut Proof<'_>, lit: T) -> Option<S> {
    let u = p.t.args(lit)[0];
    let ff = p.t.ff;
    let e = p.t.eq(u, ff);
    let ev = p.emit(&[e], "evaluate", &[], &[]);
    let mut prem = vec![Prem::Step(ev)];
    prem.extend(p.gate(e));
    prem.extend(p.gate(ff));
    p.derive(&[lit], &prem, &[])
}
