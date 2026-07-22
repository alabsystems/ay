// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `nnf` preprocessing pass: negation normal form over the Boolean skeleton.
//!
//! Rewrites each assertion into **negation normal form** (Z3's `nnf` tactic):
//! negations are pushed inward until they sit only on *atoms*, and every
//! non-`and`/`or` Boolean connective — `=>` (implies), `<->`/`=`-over-Bool
//! (iff), `xor`, and `ite`-over-Bool — is eliminated in favour of `and`/`or`.
//! The result is built exclusively from literals (atoms and negated atoms)
//! combined with `and`, `or` and quantifiers.
//!
//! # Algorithm (polarity-driven)
//!
//! A single recursion `nnf(t, pos)` returns the NNF of `t` when `pos` is true,
//! and the NNF of `¬t` when `pos` is false. It never constructs an intermediate
//! `Not` around a compound: a negation is threaded down as the `pos` flag and
//! only materializes (via [`TermStore::mk_not`]) at an atom.
//!
//! The eliminations use Z3's **conjunctive** expansions (cross-checked against
//! `z3 4.15.4`'s `(apply nnf)`), so the printed goal matches Z3's shape after
//! the surrounding tactic splits the resulting top-level `and`:
//!
//! * `a → b`        ⇒ `¬a ∨ b`                       (n-ary: `¬a₁ ∨ … ∨ ¬aₙ₋₁ ∨ aₙ`)
//! * `a ↔ b`        ⇒ `(¬a ∨ b) ∧ (a ∨ ¬b)`
//! * `a ⊕ b`        ⇒ `(a ∨ b) ∧ (¬a ∨ ¬b)`
//! * `ite c t e`    ⇒ `(¬c ∨ t) ∧ (c ∨ e)`
//!
//! and their negations dually. n-ary `xor`/`=` recurse structurally (Z3 nests
//! `xor` as `a ⊕ (rest)` and reads `=` as a chain of consecutive iffs).
//!
//! # Divergences from Z3 (both sound)
//!
//! * **Quantifiers.** Z3's `nnf` additionally *skolemizes* the existentials it
//!   exposes (e.g. `¬∀x. φ` becomes a Skolem-constant goal). AY keeps the
//!   quantifier and pushes the negation through the binder (`¬∀x. φ ⇒ ∃x. ¬φ`),
//!   which is strictly *equivalence*-preserving rather than merely
//!   equisatisfiable — a cleaner (stronger) transform.
//! * **`distinct`.** Like Z3, AY treats `distinct` as an atom (Z3's `nnf` leaves
//!   `(distinct a b)` untouched), so it is carried through as a literal.
//! * **Idempotent tidying.** AY's `mk_and`/`mk_or` dedup and sort their
//!   arguments, so AY may drop a duplicate literal Z3 keeps verbatim; the two
//!   goals stay logically equivalent.
//!
//! # Soundness (HARD requirement)
//!
//! NNF is **equivalence-preserving**: each rewrite replaces a subformula with a
//! logically equivalent one (De Morgan, the propositional identities above, and
//! quantifier-negation duality are all equivalences), so the transformed goal
//! has exactly the same models as the input. This is stronger than the
//! equisatisfiability a tactic surface requires.

use super::PreprocessingPass;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

/// Rewrite every assertion into negation normal form (see the module docs).
pub(crate) struct Nnf {
    /// Whether any assertion actually changed during the current `apply`.
    progress: bool,
}

impl Nnf {
    pub(crate) fn new() -> Self {
        Self { progress: false }
    }
}

impl Default for Nnf {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for Nnf {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        self.progress = false;
        // Memoize by (subterm, polarity): `nnf(t, pos)` is a pure function of its
        // arguments over the hash-consed DAG, so each distinct (node, polarity)
        // pair is computed once per `apply`.
        let mut cache: HashMap<(TermId, bool), TermId> = HashMap::default();
        for a in assertions.iter_mut() {
            let out = nnf(terms, *a, true, &mut cache);
            if out != *a {
                self.progress = true;
            }
            *a = out;
        }
        self.progress
    }

    fn reset(&mut self) {
        self.progress = false;
    }
}

/// The NNF of `term` when `pos`, or the NNF of `¬term` when `!pos`.
fn nnf(
    terms: &mut TermStore,
    term: TermId,
    pos: bool,
    cache: &mut HashMap<(TermId, bool), TermId>,
) -> TermId {
    if let Some(&cached) = cache.get(&(term, pos)) {
        return cached;
    }
    let result = nnf_inner(terms, term, pos, cache);
    cache.insert((term, pos), result);
    result
}

/// Uncached body of [`nnf`]: dispatch on the term's shape.
fn nnf_inner(
    terms: &mut TermStore,
    term: TermId,
    pos: bool,
    cache: &mut HashMap<(TermId, bool), TermId>,
) -> TermId {
    match terms.get(term).clone() {
        // A Boolean constant flips with the polarity; any other constant is an
        // atom (should not appear at a formula position, but is carried soundly).
        TermData::Const(ay_core::term::Constant::Bool(b)) => {
            terms.mk_bool(if pos { b } else { !b })
        }
        TermData::Const(_) => literal(terms, term, pos),

        // A Boolean variable is an atom.
        TermData::Var(_, _) => literal(terms, term, pos),

        // Push the negation through: `¬t` in polarity `pos` is `t` in `!pos`.
        TermData::Not(inner) => nnf(terms, inner, !pos, cache),

        // `ite` used as a *formula* (Bool-sorted) is a connective and must be
        // eliminated; an `ite` inside an atom is never reached (we do not recurse
        // into atom arguments).
        TermData::Ite(c, t, e) if terms.sort(term) == &Sort::Bool => {
            nnf_ite(terms, c, t, e, pos, cache)
        }
        TermData::Ite(_, _, _) => literal(terms, term, pos),

        TermData::App(sym, args) => nnf_app(terms, term, sym.name(), &args, pos, cache),

        // Push polarity through the binder; a negated quantifier flips kind
        // (`¬∀ ≡ ∃¬`, `¬∃ ≡ ∀¬`). Equivalence-preserving (no skolemization).
        TermData::Forall(vars, body, _) => {
            let nbody = nnf(terms, body, pos, cache);
            if pos {
                terms.mk_forall(vars, nbody)
            } else {
                terms.mk_exists(vars, nbody)
            }
        }
        TermData::Exists(vars, body, _) => {
            let nbody = nnf(terms, body, pos, cache);
            if pos {
                terms.mk_exists(vars, nbody)
            } else {
                terms.mk_forall(vars, nbody)
            }
        }

        // A `let` should have been expanded before solving; treat it as an
        // opaque atom rather than risk descending through a binder.
        TermData::Let(_, _) => literal(terms, term, pos),

        // `TermData` is `#[non_exhaustive]`: any future node kind is treated as an
        // atom (sound: a literal is always valid NNF), never silently rewritten.
        _ => literal(terms, term, pos),
    }
}

/// NNF of an `App` node named `name` with arguments `args`.
fn nnf_app(
    terms: &mut TermStore,
    term: TermId,
    name: &str,
    args: &[TermId],
    pos: bool,
    cache: &mut HashMap<(TermId, bool), TermId>,
) -> TermId {
    match name {
        // De Morgan: `¬(⋀ aᵢ) ≡ ⋁ ¬aᵢ`, `¬(⋁ aᵢ) ≡ ⋀ ¬aᵢ`.
        "and" => {
            let sub = map_nnf(terms, args, pos, cache);
            if pos {
                terms.mk_and(sub)
            } else {
                terms.mk_or(sub)
            }
        }
        "or" => {
            let sub = map_nnf(terms, args, pos, cache);
            if pos {
                terms.mk_or(sub)
            } else {
                terms.mk_and(sub)
            }
        }
        // Rare desugaring guards: `not`/`ite` occasionally survive as an `App`.
        "not" if args.len() == 1 => nnf(terms, args[0], !pos, cache),
        "ite" if args.len() == 3 && terms.sort(term) == &Sort::Bool => {
            nnf_ite(terms, args[0], args[1], args[2], pos, cache)
        }
        // `a₁ → … → aₙ ≡ ¬a₁ ∨ … ∨ ¬aₙ₋₁ ∨ aₙ`; its negation is the dual conjunction.
        "=>" if args.len() >= 2 => nnf_implies(terms, args, pos, cache),
        // Parity connective (see [`nnf_xor`]).
        "xor" if args.len() >= 2 => nnf_xor(terms, args, pos, cache),
        // `=` over Bool is iff (a chain for n arguments); over any other sort it
        // is an atom.
        "=" if args.len() >= 2 && terms.sort(args[0]) == &Sort::Bool => {
            nnf_iff_chain(terms, args, pos, cache)
        }
        // Everything else — comparisons, `=` over non-Bool, `distinct`,
        // uninterpreted predicates, Bool-valued UF applications — is an atom.
        _ => literal(terms, term, pos),
    }
}

/// NNF of `ite c t e` (Bool result) in polarity `pos`.
///
/// `ite c t e ≡ (¬c ∨ t) ∧ (c ∨ e)`; the negation is `(¬c ∨ ¬t) ∧ (c ∨ ¬e)`.
fn nnf_ite(
    terms: &mut TermStore,
    c: TermId,
    t: TermId,
    e: TermId,
    pos: bool,
    cache: &mut HashMap<(TermId, bool), TermId>,
) -> TermId {
    let c_pos = nnf(terms, c, true, cache);
    let c_neg = nnf(terms, c, false, cache);
    let t_side = nnf(terms, t, pos, cache);
    let e_side = nnf(terms, e, pos, cache);
    let left = terms.mk_or(vec![c_neg, t_side]);
    let right = terms.mk_or(vec![c_pos, e_side]);
    terms.mk_and(vec![left, right])
}

/// NNF of `a₁ → a₂ → … → aₙ` (right-nested implication) in polarity `pos`.
fn nnf_implies(
    terms: &mut TermStore,
    args: &[TermId],
    pos: bool,
    cache: &mut HashMap<(TermId, bool), TermId>,
) -> TermId {
    let (last, init) = args.split_last().expect("caller guarantees len >= 2");
    if pos {
        // ¬a₁ ∨ … ∨ ¬aₙ₋₁ ∨ aₙ
        let mut disj: Vec<TermId> = init.iter().map(|&a| nnf(terms, a, false, cache)).collect();
        disj.push(nnf(terms, *last, true, cache));
        terms.mk_or(disj)
    } else {
        // a₁ ∧ … ∧ aₙ₋₁ ∧ ¬aₙ
        let mut conj: Vec<TermId> = init.iter().map(|&a| nnf(terms, a, true, cache)).collect();
        conj.push(nnf(terms, *last, false, cache));
        terms.mk_and(conj)
    }
}

/// NNF of an n-ary `xor a₁ … aₙ`, nested as `a₁ ⊕ (a₂ ⊕ … ⊕ aₙ)`.
///
/// `x ⊕ y ≡ (x ∨ y) ∧ (¬x ∨ ¬y)` and `¬(x ⊕ y) ≡ (¬x ∨ y) ∧ (x ∨ ¬y)`, applied
/// with the tail `y = (a₂ ⊕ … ⊕ aₙ)` expanded recursively in both polarities —
/// matching Z3's nested shape.
fn nnf_xor(
    terms: &mut TermStore,
    args: &[TermId],
    pos: bool,
    cache: &mut HashMap<(TermId, bool), TermId>,
) -> TermId {
    match args {
        [] => terms.mk_bool(!pos), // xor of nothing is false
        [only] => nnf(terms, *only, pos, cache),
        [head, rest @ ..] => {
            let head_pos = nnf(terms, *head, true, cache);
            let head_neg = nnf(terms, *head, false, cache);
            let rest_pos = nnf_xor(terms, rest, true, cache);
            let rest_neg = nnf_xor(terms, rest, false, cache);
            if pos {
                // (head ∨ rest) ∧ (¬head ∨ ¬rest)
                let left = terms.mk_or(vec![head_pos, rest_pos]);
                let right = terms.mk_or(vec![head_neg, rest_neg]);
                terms.mk_and(vec![left, right])
            } else {
                // (¬head ∨ rest) ∧ (head ∨ ¬rest)
                let left = terms.mk_or(vec![head_neg, rest_pos]);
                let right = terms.mk_or(vec![head_pos, rest_neg]);
                terms.mk_and(vec![left, right])
            }
        }
    }
}

/// NNF of a Bool `=` chain `a₁ = a₂ = … = aₙ`, read as `⋀ᵢ (aᵢ ↔ aᵢ₊₁)`.
///
/// Positive: the conjunction of the consecutive iffs. Negative: its De Morgan
/// dual, `⋁ᵢ ¬(aᵢ ↔ aᵢ₊₁)` = `⋁ᵢ (aᵢ ⊕ aᵢ₊₁)`.
fn nnf_iff_chain(
    terms: &mut TermStore,
    args: &[TermId],
    pos: bool,
    cache: &mut HashMap<(TermId, bool), TermId>,
) -> TermId {
    let pairs: Vec<TermId> = args
        .windows(2)
        .map(|w| iff_pair(terms, w[0], w[1], pos, cache))
        .collect();
    if pos {
        terms.mk_and(pairs)
    } else {
        terms.mk_or(pairs)
    }
}

/// The NNF of `a ↔ b` when `want_equal`, or of `a ⊕ b` when `!want_equal`.
///
/// `a ↔ b ≡ (¬a ∨ b) ∧ (a ∨ ¬b)`; `a ⊕ b ≡ (a ∨ b) ∧ (¬a ∨ ¬b)`.
fn iff_pair(
    terms: &mut TermStore,
    a: TermId,
    b: TermId,
    want_equal: bool,
    cache: &mut HashMap<(TermId, bool), TermId>,
) -> TermId {
    let a_pos = nnf(terms, a, true, cache);
    let a_neg = nnf(terms, a, false, cache);
    let b_pos = nnf(terms, b, true, cache);
    let b_neg = nnf(terms, b, false, cache);
    if want_equal {
        let left = terms.mk_or(vec![a_neg, b_pos]);
        let right = terms.mk_or(vec![a_pos, b_neg]);
        terms.mk_and(vec![left, right])
    } else {
        let left = terms.mk_or(vec![a_pos, b_pos]);
        let right = terms.mk_or(vec![a_neg, b_neg]);
        terms.mk_and(vec![left, right])
    }
}

/// NNF each of `args` in polarity `pos`.
fn map_nnf(
    terms: &mut TermStore,
    args: &[TermId],
    pos: bool,
    cache: &mut HashMap<(TermId, bool), TermId>,
) -> Vec<TermId> {
    args.iter().map(|&a| nnf(terms, a, pos, cache)).collect()
}

/// Emit an atom as a literal: `term` itself when positive, `¬term` when
/// negative. `mk_not` on an atom yields `Not(atom)` (a literal), so the result
/// stays in NNF.
fn literal(terms: &mut TermStore, term: TermId, pos: bool) -> TermId {
    if pos {
        term
    } else {
        terms.mk_not(term)
    }
}

#[cfg(test)]
#[path = "nnf_tests.rs"]
mod tests;
