// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Word-level glue: bit equalities to word equalities, equivalence transfer,
//! ring combinations through `poly_simp`, and quantified generic lemmas.

use super::clean::bb_equal;
use super::proof::{Arg, Prem, Proof, S};
use super::term::{Op, T};
use ay_core::kani_compat::DetHashMap as HashMap;

pub(crate) fn symm(p: &mut Proof<'_>, s: S) -> S {
    let e = p.unit(s);
    let (a, b) = (p.t.args(e)[0], p.t.args(e)[1]);
    let f = p.t.eq(b, a);
    p.emit(&[f], "symm", &[s], &[])
}

/// `(= first last)` from a chain of equalities.
pub(crate) fn trans(p: &mut Proof<'_>, chain: &[S]) -> S {
    let first = p.t.args(p.unit(chain[0]))[0];
    let last = p.t.args(p.unit(chain[chain.len() - 1]))[1];
    let e = p.t.eq(first, last);
    p.emit(&[e], "trans", chain, &[])
}

pub(crate) fn eq_step(p: &mut Proof<'_>, a: T, b: T, rule: &str, prem: &[S]) -> S {
    let e = p.t.eq(a, b);
    p.emit(&[e], rule, prem, &[])
}

/// `(cl (= W1 W2))` for `@bbterm` words from per-bit `(cl (= a_i b_i))` facts.
pub(crate) fn word_eq(p: &mut Proof<'_>, w1: T, w2: T, bits: &[S]) -> Option<S> {
    let (b1, b2) = (p.t.bits(w1), p.t.bits(w2));
    if b1.is_empty() || b1.len() != b2.len() || bits.len() != b1.len() {
        return None;
    }
    let conj = bb_equal(&mut p.t, &b1, &b2);
    let weq = p.t.eq(w1, w2);
    let be = eq_step(p, weq, conj, "bitblast_equal", &[]);
    // The bit-blast equality rule omits `and` for a one-bit word. Its
    // already-proved single equality transfers directly; emitting and_neg
    // for that equality would be an invalid certificate rule.
    if let [bit] = bits {
        return transfer(p, be, *bit);
    }
    let mut an = vec![conj];
    for (&x, &y) in b1.iter().zip(&b2) {
        let e = p.t.eq(x, y);
        an.push(p.t.not(e));
    }
    let an_s = p.emit(&an, "and_neg", &[], &[]);
    let ne = {
        let x = p.t.eq(weq, conj);
        p.t.not(x)
    };
    let nconj = p.t.not(conj);
    let ep = p.emit(&[ne, weq, nconj], "equiv_pos1", &[], &[]);
    let mut prem = vec![Prem::Step(ep), Prem::Step(be), Prem::Step(an_s)];
    prem.extend(bits.iter().map(|&s| Prem::Step(s)));
    p.derive(&[weq], &prem, &[])
}

/// From `(cl (= A B))` (Boolean) and a unit fact about `A` or `B`, the same fact about the other.
pub(crate) fn transfer(p: &mut Proof<'_>, eq: S, fact: S) -> Option<S> {
    let e = p.unit(eq);
    let (a, b) = (p.t.args(e)[0], p.t.args(e)[1]);
    let lit = p.unit(fact);
    let (atom, pol) = p.t.lit_of(lit);
    let other = if atom == a {
        b
    } else if atom == b {
        a
    } else {
        return None;
    };
    let tgt = if pol { other } else { p.t.not(other) };
    let ne = p.t.not(e);
    let (na, nb) = (p.t.not(a), p.t.not(b));
    let e1 = p.emit(&[ne, a, nb], "equiv_pos1", &[], &[]);
    let e2 = p.emit(&[ne, na, b], "equiv_pos2", &[], &[]);
    p.derive(
        &[tgt],
        &[
            Prem::Step(e1),
            Prem::Step(e2),
            Prem::Step(eq),
            Prem::Step(fact),
        ],
        &[],
    )
}

/// Project conjunct `i` of a unit conjunction fact.
pub(crate) fn project(p: &mut Proof<'_>, fact: S, i: usize) -> Option<S> {
    let c = p.unit(fact);
    let x = *p.t.args(c).get(i)?;
    let nc = p.t.not(c);
    let ap = p.emit(&[nc, x], "and_pos", &[], &[Arg::Int(i)]);
    p.derive(&[x], &[Prem::Step(ap), Prem::Step(fact)], &[])
}

/// `(and c_0 ..)` from facts for each conjunct.
pub(crate) fn conjoin(p: &mut Proof<'_>, conj: T, facts: &[S]) -> Option<S> {
    let mut l = vec![conj];
    for &c in p.t.args(conj).to_vec().iter() {
        l.push(p.t.not(c));
    }
    let an = p.emit(&l, "and_neg", &[], &[]);
    let mut prem = vec![Prem::Step(an)];
    prem.extend(facts.iter().map(|&s| Prem::Step(s)));
    p.derive(&[conj], &prem, &[])
}

/// `(= lhs rhs)` given unit equalities `(= u_i v_i)` with optional multipliers,
/// where `lhs - rhs` and `sum c_i (u_i - v_i)` are the same polynomial.
pub(crate) fn lincomb(p: &mut Proof<'_>, lhs: T, rhs: T, eqs: &[(S, Option<T>)]) -> Option<S> {
    let mut d_terms = vec![rhs];
    let mut z_terms = vec![rhs];
    let mut prem = Vec::new();
    for &(s, c) in eqs {
        let e = p.unit(s);
        let (u, v) = (p.t.args(e)[0], p.t.args(e)[1]);
        let d = p.t.sub(u, v);
        let z = p.t.sub(v, v);
        let mut cs = eq_step(p, d, z, "cong", &[s]);
        let (dd, zz) = match c {
            None => (d, z),
            Some(c) => {
                let (dm, zm) = (p.t.mul(c, d), p.t.mul(c, z));
                cs = eq_step(p, dm, zm, "cong", &[cs]);
                (dm, zm)
            }
        };
        d_terms.push(dd);
        z_terms.push(zz);
        prem.push(cs);
    }
    let rhs1 = p.t.add(&d_terms);
    let rhs2 = p.t.add(&z_terms);
    let s1 = eq_step(p, lhs, rhs1, "poly_simp", &[]);
    let big = eq_step(p, rhs1, rhs2, "cong", &prem);
    let s3 = eq_step(p, rhs2, rhs, "poly_simp", &[]);
    Some(trans(p, &[s1, big, s3]))
}

/// Prove `(forall vars BODY)` where `body` runs inside the `bind` context and
/// returns `(BODY, step (cl BODY))`.
pub(crate) fn forall_lemma(
    p: &mut Proof<'_>,
    vars: &[T],
    body: impl FnOnce(&mut Proof<'_>) -> Option<(T, S)>,
) -> Option<S> {
    let a = p.anchor(vars);
    let (b, bs) = body(p)?;
    let tt = p.t.tt;
    let t = p.emit(&[tt], "true", &[], &[]);
    let be = p.t.eq(b, tt);
    let (nb, ntt) = (p.t.not(b), p.t.not(tt));
    let e = p.emit(&[be, nb, ntt], "equiv_neg1", &[], &[]);
    p.derive(&[be], &[Prem::Step(e), Prem::Step(bs), Prem::Step(t)], &[])?;
    let fa = p.t.forall(vars, b);
    let ft = p.t.forall(vars, tt);
    let fe = p.t.eq(fa, ft);
    let bnd = p.close(a, &[fe], "bind", &[]);
    let rm = eq_step(p, ft, tt, "qnt_rm_unused", &[]);
    let tr = trans(p, &[bnd, rm]);
    let t2 = p.emit(&[tt], "true", &[], &[]);
    let fat = p.t.eq(fa, tt);
    let nfat = p.t.not(fat);
    let ep = p.emit(&[nfat, fa, ntt], "equiv_pos1", &[], &[]);
    p.derive(
        &[fa],
        &[Prem::Step(ep), Prem::Step(tr), Prem::Step(t2)],
        &[],
    )
}

/// Instantiate the proved `(forall vars BODY)` at `args`: the step `(cl BODY[args])`.
pub(crate) fn instantiate(p: &mut Proof<'_>, fa_step: S, args: &[T]) -> Option<S> {
    let fa = p.unit(fa_step);
    let fargs = p.t.args(fa).to_vec();
    let (vars, body) = fargs.split_at(fargs.len() - 1);
    let mut map = HashMap::default();
    for (&v, &a) in vars.iter().zip(args) {
        map.insert(v, a);
    }
    let inst = substitute(p, body[0], &map);
    let nfa = p.t.not(fa);
    let orl = p.t.or(&[nfa, inst]);
    let targs: Vec<Arg> = args.iter().map(|&a| Arg::Term(a)).collect();
    let fi = p.emit(&[orl], "forall_inst", &[], &targs);
    let o = p.emit(&[nfa, inst], "or", &[fi], &[]);
    p.derive(&[inst], &[Prem::Step(o), Prem::Step(fa_step)], &[])
}

/// Split a unit `(cl (or d_1 .. d_k))` into `(cl d_1 .. d_k)`.
pub(crate) fn split_or(p: &mut Proof<'_>, s: S) -> S {
    let disj = p.t.args(p.unit(s)).to_vec();
    p.emit(&disj, "or", &[s], &[])
}

pub(crate) fn substitute(p: &mut Proof<'_>, t: T, map: &HashMap<T, T>) -> T {
    let mut memo: HashMap<T, T> = HashMap::default();
    let mut stack = vec![(t, false)];
    while let Some((u, done)) = stack.pop() {
        if memo.contains_key(&u) {
            continue;
        }
        if let Some(&r) = map.get(&u) {
            memo.insert(u, r);
            continue;
        }
        let args = p.t.args(u).to_vec();
        if !done {
            stack.push((u, true));
            stack.extend(args.iter().map(|&a| (a, false)));
            continue;
        }
        let na: Vec<T> = args
            .iter()
            .map(|a| memo.get(a).copied().unwrap_or(*a))
            .collect();
        let r = if na == args {
            u
        } else {
            let (op, sort) = (p.t.op(u).clone(), p.t.sort(u));
            if matches!(op, Op::Forall) {
                u
            } else {
                p.t.mk_sorted(op, &na, sort)
            }
        };
        memo.insert(u, r);
    }
    memo.get(&t).copied().unwrap_or(t)
}
