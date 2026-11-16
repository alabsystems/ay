// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pieces shared by the Horner-stage lemmas (one bit of the multiplier per
//! stage): the low-bit word of a stage as the constant 1 or 0, the ground
//! side condition of an instance, and subproof plumbing.

use super::bits;
use super::helpers::{eq_step, symm, trans, word_eq};
use super::proof::{Arg, Prem, Proof, S};
use super::term::T;

/// Under the assumption step `asm` (`e0` or `(not e0)`), `(= (bvmul other wd) other)`
/// or `(= (bvmul other wd) 0)` where `wd = bb(e0, false, ..)`.
pub(crate) fn bit_times(
    p: &mut Proof<'_>,
    e0: T,
    positive: bool,
    asm: S,
    wd: T,
    word: T,
) -> Option<(S, T)> {
    let width = p.t.width(wd);
    let cv = if positive { p.t.tt } else { p.t.ff };
    let e = p.t.eq(e0, cv);
    let mut prem = p.gate(e);
    prem.extend(p.gate(cv));
    prem.push(Prem::Step(asm));
    let b0 = p.derive(&[e], &prem, &[])?;
    let ff = p.t.ff;
    let fe = p.t.eq(ff, ff);
    let refl = p.emit(&[fe], "eq_reflexive", &[], &[]);
    let mut tgt = vec![cv];
    tgt.resize(width as usize, ff);
    let mut facts = vec![b0];
    facts.resize(width as usize, refl);
    let tw = p.t.bb(&tgt);
    let w = word_eq(p, wd, tw, &facts)?;
    let l = p.t.lit(if positive {
        bits::from_u64(1, width)
    } else {
        bits::zero(width)
    });
    let kc = eq_step(p, l, tw, "bitblast_const", &[]);
    let kcs = symm(p, kc);
    let wl = trans(p, &[w, kcs]);
    let other = p.t.args(word)[0];
    let ol = p.t.mul(other, l);
    let cv2 = eq_step(p, word, ol, "cong", &[wl]);
    let res = if positive { other } else { l };
    let pv = eq_step(p, ol, res, "poly_simp", &[]);
    Some((trans(p, &[cv2, pv]), res))
}

/// `(cl K)` for a ground side condition `K` by evaluation.
pub(crate) fn ground(p: &mut Proof<'_>, k: T) -> Option<S> {
    let tt = p.t.tt;
    let e = p.t.eq(k, tt);
    let ev = p.emit(&[e], "evaluate", &[], &[]);
    let mut prem = vec![Prem::Step(ev)];
    prem.extend(p.gate(e));
    prem.extend(p.gate(tt));
    p.derive(&[k], &prem, &[])
}

/// Close a lemma body `(or (not A_1) .. (not A_k) C)` proved as the clause `spc`.
pub(crate) fn body_from_clause(p: &mut Proof<'_>, body: T, spc: S) -> Option<S> {
    let args = p.t.args(body).to_vec();
    let mut prem = vec![Prem::Step(spc)];
    for (i, &d) in args.iter().enumerate() {
        let nd = p.t.not(d);
        prem.push(Prem::Step(p.emit(
            &[body, nd],
            "or_neg",
            &[],
            &[Arg::Int(i)],
        )));
    }
    p.derive(&[body], &prem, &[])
}

/// `(cl c)` for the conjunction `c` from facts for its conjuncts.
pub(crate) fn and_from(p: &mut Proof<'_>, c: T, facts: &[S]) -> Option<S> {
    super::helpers::conjoin(p, c, facts)
}
