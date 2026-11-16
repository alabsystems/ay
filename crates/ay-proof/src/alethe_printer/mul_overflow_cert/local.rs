// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Local facts for the signed row: a clause proved under assumptions, a bit-level
//! clause over bit-blasted word atoms, and an `ite` resolved by its condition.

use super::div::gates_rec;
use super::helpers::{eq_step, trans};
use super::lin::{atom_bits, Blaster};
use super::proof::{Prem, Proof, S};
use super::term::{Op, T};
use ay_core::kani_compat::DetHashSet as HashSet;

/// `(cl (not h_1) .. (not h_k) c)` from `body`, run under the assumptions
/// `hyps` (their steps in order), whose last step must conclude `(cl c)`.
pub(crate) fn under(
    p: &mut Proof<'_>,
    hyps: &[T],
    c: T,
    body: impl FnOnce(&mut Proof<'_>, &[S]) -> Option<S>,
) -> Option<S> {
    let a = p.anchor(&[]);
    let hs: Vec<S> = hyps.iter().map(|&h| p.assume(h)).collect();
    let last = body(p, &hs)?;
    if p.clause(last) != [c] {
        return None;
    }
    let mut cl: Vec<T> = hyps.iter().map(|&h| p.t.not(h)).collect();
    cl.push(c);
    Some(p.close(a, &cl, "subproof", &hs))
}

fn word_atom(p: &Proof<'_>, a: T) -> bool {
    matches!(p.t.op(a), Op::Eq | Op::Ult) && p.t.width(p.t.args(a)[0]) > 0
}

/// `(cl target..)` from the clause steps `hyps`: every word atom (an equality
/// or `bvult` of words) of the hypotheses and the target is bit-blasted the
/// way the checker does it, words the blaster does not open standing for
/// their own `@bit_of` projections, and the local refuter derives the clause
/// from the circuits' defining clauses.
pub(crate) fn bitfact(p: &mut Proof<'_>, hyps: &[S], target: &[T]) -> Option<S> {
    bitfact_with(p, hyps, target, &[])
}

/// [`bitfact`] with the words `opaque` kept closed (standing for their own
/// `@bit_of` projections), as the schoolbook sees its limbs.
pub(crate) fn bitfact_with(p: &mut Proof<'_>, hyps: &[S], target: &[T], opaque: &[T]) -> Option<S> {
    let mut b = Blaster::new(opaque, &[]);
    let mut prem: Vec<Prem> = hyps.iter().map(|&s| Prem::Step(s)).collect();
    let mut atoms = Vec::new();
    for &h in hyps {
        for l in p.clause(h).to_vec() {
            atoms.push(p.t.lit_of(l).0);
        }
    }
    for &l in target {
        atoms.push(p.t.lit_of(l).0);
    }
    let mut seen = HashSet::default();
    while let Some(a) = atoms.pop() {
        if !seen.insert(a) {
            continue;
        }
        if word_atom(p, a) {
            let (eqs, circ, _) = atom_bits(p, &mut b, a)?;
            let e = p.unit(eqs);
            prem.push(Prem::Step(eqs));
            prem.extend(p.gate(e));
            prem.extend(gates_rec(p, circ, usize::MAX));
        } else if p.t.is_gate(a) {
            prem.extend(p.gate(a));
            for x in p.t.args(a).to_vec() {
                atoms.push(p.t.lit_of(x).0);
            }
        } else if matches!(p.t.op(a), Op::True | Op::False) {
            prem.extend(p.gate(a));
        }
    }
    let (tt, ff) = (p.t.tt, p.t.ff);
    prem.extend(p.gate(tt));
    prem.extend(p.gate(ff));
    p.derive(target, &prem, &[])
}

/// `(= c v)` for the Boolean value `v` of the condition `c` (an atom or a
/// negation of one) given the literal step `lit` of the same atom.
pub(crate) fn truth(p: &mut Proof<'_>, c: T, lit: S) -> Option<(S, bool)> {
    let (atom, pol) = p.t.lit_of(p.unit(lit));
    let (catom, cpol) = p.t.lit_of(c);
    if atom != catom {
        return None;
    }
    let pol = pol == cpol;
    let cv = if pol { p.t.tt } else { p.t.ff };
    let e = p.t.eq(c, cv);
    let mut prem = p.gate(e);
    prem.extend(p.gate(cv));
    prem.push(Prem::Step(lit));
    Some((p.derive(&[e], &prem, &[])?, pol))
}

/// `(= (ite c x y) x)` or `(= (ite c x y) y)` from the literal step of `c`.
pub(crate) fn branch(p: &mut Proof<'_>, ite: T, lit: S) -> Option<S> {
    let [c, x, y] = p.t.args(ite).to_vec()[..] else {
        return None;
    };
    let (ec, pol) = truth(p, c, lit)?;
    let cv = if pol { p.t.tt } else { p.t.ff };
    let it = p.t.ite(cv, x, y);
    let s1 = eq_step(p, ite, it, "cong", &[ec]);
    let v = if pol { x } else { y };
    let s2 = eq_step(p, it, v, "ite_simplify", &[]);
    Some(trans(p, &[s1, s2]))
}
