// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Definitions of the interpreted arithmetic operators the simplex treats as
//! opaque variables: `div` and `mod` by a non-zero numeral, and `abs`
//! (design K4: "a conservative definition of a kernel-introduced symbol ...
//! an ite/div/mod definition"; roadmap AL, divisibility reasoning).
//!
//! When an atom that mentions one of them is internalized, the arithmetic
//! plug-in adds its defining clauses to the running search, once per term:
//!
//! - `q = (div x k)`, `r = (mod x k)`, `k` a non-zero integer numeral:
//!   `x = k·q + r`, `r ≥ 0` and `r ≤ |k| − 1`. These pin `q` and `r` to
//!   SMT-LIB's Euclidean quotient and remainder of every integral `x`, so
//!   branch and bound over the opaque `q` and `r` is complete for them, and
//!   divisibility (`x = 3q`, `x mod 3 = 0`) is linear integer reasoning in
//!   the one search.
//! - `a = (abs x)`: `x ≥ 0 → a = x` and `x < 0 → a = −x`.
//!
//! Every clause is T-valid, and `Definitional` (K5): the simplex never
//! re-derives them.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, TermData, TermId, TermStore, TheoryLemmaKind, TheoryLit};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::atoms::eq_atom;
use crate::linear::{defined_leaf, Defined, Linearizer};
use crate::plugin::{Ctx, Lemma, LemmaTier, ProofHint};

/// Arithmetic subterms of `atom` that need a definition and have none yet.
fn undefined_leaves(terms: &TermStore, atom: TermId, defined: &HashSet<TermId>) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![atom];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                if defined_leaf(terms, term).is_some() && !defined.contains(&term) {
                    out.push(term);
                }
                stack.extend(args.iter().copied());
            }
            TermData::Ite(_, t, e) => stack.extend([*t, *e]),
            _ => {}
        }
    }
    out
}

fn unit(clause: Vec<TheoryLit>, kind: TheoryLemmaKind) -> Lemma {
    Lemma {
        clause,
        tier: LemmaTier::Definitional,
        hint: ProofHint::kind(kind),
    }
}

/// Add the definitions of every `div`/`mod`/`abs` below `atom` not yet
/// defined, recording each defined term (both `div` and `mod` of a pair).
pub(crate) fn define_operators(ctx: &mut Ctx<'_>, atom: TermId, defined: &mut HashSet<TermId>) {
    for term in undefined_leaves(ctx.terms(), atom, defined) {
        if defined.contains(&term) {
            continue; // defined as the partner of an earlier div/mod
        }
        let Some((kind, x, divisor)) = defined_leaf(ctx.terms(), term) else {
            continue;
        };
        match (kind, divisor) {
            (Defined::Div | Defined::Mod, Some(k)) => {
                let k_term = match ctx.terms().get(term) {
                    TermData::App(_, args) => args.get(1).copied(),
                    _ => None,
                };
                let Some(k_term) = k_term else { continue };
                // The term itself fills its own role; its partner may fold
                // (`(mod x 1)` is 0), which leaves the definition exact.
                let terms = ctx.terms_mut();
                let (q, r) = if kind == Defined::Div {
                    (term, terms.mk_mod(x, k_term))
                } else {
                    (terms.mk_intdiv(x, k_term), term)
                };
                defined.insert(q);
                defined.insert(r);
                defined.insert(term);
                for lemma in div_mod_definition(terms, x, &k, k_term, q, r) {
                    ctx.lemma(lemma);
                }
            }
            (Defined::Abs, _) => {
                defined.insert(term);
                for lemma in abs_definition(ctx.terms_mut(), x, term) {
                    ctx.lemma(lemma);
                }
            }
            _ => {}
        }
    }
}

/// `x = k·q + r`, `0 ≤ r`, `r ≤ |k| − 1`.
fn div_mod_definition(
    terms: &mut TermStore,
    x: TermId,
    k: &BigInt,
    k_term: TermId,
    q: TermId,
    r: TermId,
) -> Vec<Lemma> {
    let kq = terms.mk_mul(vec![k_term, q]);
    let sum = terms.mk_add(vec![kq, r]);
    let split = eq_atom(terms, x, sum);
    let zero = terms.mk_int(BigInt::zero());
    let nonneg = terms.mk_le(zero, r);
    let top = terms.mk_int(k.abs() - 1);
    let below = terms.mk_le(r, top);
    vec![
        unit(
            vec![TheoryLit::new(split, true)],
            TheoryLemmaKind::LiaGeneric,
        ),
        unit(
            vec![TheoryLit::new(nonneg, true)],
            TheoryLemmaKind::LiaGeneric,
        ),
        unit(
            vec![TheoryLit::new(below, true)],
            TheoryLemmaKind::LiaGeneric,
        ),
    ]
}

/// `x ≥ 0 → a = x`, `x < 0 → a = −x` (over Int or Real).
fn abs_definition(terms: &mut TermStore, x: TermId, a: TermId) -> Vec<Lemma> {
    let zero = if *terms.sort(x) == Sort::Int {
        terms.mk_int(BigInt::zero())
    } else {
        terms.mk_rational(BigRational::zero())
    };
    let nonneg = terms.mk_le(zero, x);
    let same = eq_atom(terms, a, x);
    let minus = terms.mk_neg(x);
    let flipped = eq_atom(terms, a, minus);
    vec![
        unit(
            vec![TheoryLit::new(nonneg, false), TheoryLit::new(same, true)],
            TheoryLemmaKind::Generic,
        ),
        unit(
            vec![TheoryLit::new(nonneg, true), TheoryLit::new(flipped, true)],
            TheoryLemmaKind::Generic,
        ),
    ]
}

/// The GCD test on an integer equality, once, when it is internalized:
/// `Σ aᵢ·xᵢ = c` over Int with `gcd(aᵢ) ∤ c` has no solution, so the atom is
/// false in every model (the lane's `gcd_test`). The unit `¬atom` is T-valid
/// over Int; it is `Definitional` because nothing would derive it again, and
/// branch and bound alone never refutes an unbounded one.
pub(crate) fn gcd_refutes_equality(
    terms: &TermStore,
    lin: &mut Linearizer,
    atom: TermId,
) -> Option<Lemma> {
    let TermData::App(sym, args) = terms.get(atom) else {
        return None;
    };
    let (&[a, b], "=") = (args.as_slice(), sym.name()) else {
        return None;
    };
    if *terms.sort(a) != Sort::Int {
        return None;
    }
    let mut form = lin.linearize(terms, a).ok()?;
    let rhs = lin.linearize(terms, b).ok()?;
    form.add_scaled(&rhs, &-BigRational::one());
    if form.coeffs.is_empty()
        || form
            .coeffs
            .keys()
            .any(|&leaf| *terms.sort(leaf) != Sort::Int)
    {
        return None;
    }
    let lcm = form
        .coeffs
        .values()
        .chain(std::iter::once(&form.constant))
        .fold(BigInt::one(), |acc, c| acc.lcm(c.denom()));
    let scale = BigRational::from_integer(lcm);
    let gcd = form
        .coeffs
        .values()
        .map(|c| (c * &scale).to_integer())
        .fold(BigInt::zero(), |acc, c| acc.gcd(&c));
    let constant = (&form.constant * &scale).to_integer();
    if gcd.is_zero() || (constant % &gcd).is_zero() {
        return None;
    }
    Some(Lemma {
        clause: vec![TheoryLit::new(atom, false)],
        tier: LemmaTier::Definitional,
        hint: ProofHint::kind(TheoryLemmaKind::LiaGeneric),
    })
}
