// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Boolean `=` arm of the NNF Skolemizer (#iff-split).
//!
//! Verus asserts a quantified claim as `(= tmp%k (exists ...))` and states
//! every extensional-equality axiom as
//! `(= (ext_eq ...) (and ... (forall ...)))`. Kept as a leaf, the quantifier
//! has no polarity: an existential is never Skolemized and never instantiated
//! (E-matching refuses existentials), and a universal is only ever a proxy the
//! ground solver guesses (Verus fix queue, row D). The equality is split into
//! the two implications it is equivalent to, so each copy of the quantifier
//! takes the polarity it has there:
//!
//! ```text
//! positive:  (a = b)  ≡ (or ¬a b) ∧ (or a ¬b)
//! negative: ¬(a = b)  ≡ (and a ¬b) ∨ (and ¬a b)
//! ```
//!
//! The split is an equivalence, so Skolemizing the copies preserves
//! satisfiability exactly as for any other connective: each positive
//! existential (negative universal) copy gets its own fresh witness, a Skolem
//! function of the enclosing universals it mentions.
//!
//! A universal whose whole body is a predicate definition `(= (p x̄) φ)` is not
//! split (#iff-split-definition, [`is_quantified_definition`]): its witness
//! would be a Skolem function no proof record binds. A solve that publishes
//! without a proof (competition shedding, e.g. `--z3-mode`) needs no such
//! record and splits it too ([`scoped_definition_split`]).

use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId, TermStore};

use super::{rewrite_nnf_with_skolem, ForallSkolemProvenance};

thread_local! {
    /// Whether a predicate definition is split like any other Boolean `=`.
    static SPLIT_DEFINITIONS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Restores the predecessor [`SPLIT_DEFINITIONS`] value on drop (and unwind).
pub(crate) struct DefinitionSplitScope(bool);

impl Drop for DefinitionSplitScope {
    fn drop(&mut self) {
        SPLIT_DEFINITIONS.with(|c| c.set(self.0));
    }
}

/// Split predicate definitions too while the returned guard lives. Only a
/// solve whose UNSAT is published without a proof may ask for it: the split
/// is an equivalence, so the refutation it enables is sound, but the proof
/// lanes cannot cite the Skolem function it introduces.
pub(crate) fn scoped_definition_split(enabled: bool) -> DefinitionSplitScope {
    DefinitionSplitScope(SPLIT_DEFINITIONS.with(|c| c.replace(enabled)))
}

/// `true` when a predicate definition is left whole in the current scope.
pub(super) fn keeps_definitions_whole() -> bool {
    !SPLIT_DEFINITIONS.with(std::cell::Cell::get)
}

/// `true` when `(sym args)` is a Boolean `=` of two terms, one of which holds
/// a quantifier. A ground Boolean `=` stays a leaf.
pub(super) fn splits(terms: &TermStore, sym: &Symbol, args: &[TermId]) -> bool {
    sym.name() == "="
        && args.len() == 2
        && matches!(terms.sort(args[0]), Sort::Bool)
        && (crate::ematching::contains_quantifier(terms, args[0])
            || crate::ematching::contains_quantifier(terms, args[1]))
}

/// (#iff-split-alternation) `true` when the Boolean `=` is split: [`splits`]
/// holds and neither side nests a quantifier inside another.
///
/// A nested quantifier gives one of the two copies an alternation, such as
/// `∀y. ∃x. x > y` in `(= b (∀y. ∃x. x > y))`, whose witness is a Skolem
/// FUNCTION of the inner universal's binder. Split, such a query loses the
/// lanes that refuted it with the equality whole (the forall-exists probes went
/// from `unsat` to `unknown`), so the equality stays a leaf, exactly as before
/// the split existed. The Verus shapes the split is for, `(= tmp%k (exists
/// ...))` and `(= (ext_eq ...) (and ... (forall ...)))`, nest no quantifier.
pub(super) fn splits_without_alternation(terms: &TermStore, sym: &Symbol, args: &[TermId]) -> bool {
    splits(terms, sym, args)
        && !nests_quantifier(terms, args[0])
        && !nests_quantifier(terms, args[1])
}

/// `true` when some quantifier in `term` holds another in its body.
fn nests_quantifier(terms: &TermStore, term: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                if crate::ematching::contains_quantifier(terms, *body) {
                    return true;
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, x, y) => stack.extend([*c, *x, *y]),
            _ => {}
        }
    }
    false
}

/// (#iff-split-definition) `true` when `body`, the whole body of a universal
/// binding `vars`, is a predicate definition `(= (p t̄) φ)`: one side is an
/// application of a declared (non-builtin) symbol that holds no quantifier and
/// mentions every binder, and the other side holds a quantifier. The
/// universal is then left exactly as it was before the split existed.
///
/// Split, such a definition becomes a universal whose body applies a Skolem
/// FUNCTION of the binders, and a refutation resting on its instances cites a
/// witness no proof record binds (`ForallSkolemProvenance` covers only
/// dependency-free witnesses). The native posture then declines to publish
/// it: all three readings of the extensional-equality definition in
/// `quantifier_under_boolean_equality.rs` went from `unsat` to `unknown`.
/// Unsplit, the universal is instantiated exactly as before the split
/// existed, and the lanes that refuted those readings then refute them again.
/// A Boolean `=` that is not such a definition, such as Verus's asserted
/// `(= tmp%k (exists ...))`, is split.
pub(super) fn is_quantified_definition(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
) -> bool {
    let TermData::App(sym, args) = terms.get(body) else {
        return false;
    };
    if !splits(terms, sym, args) {
        return false;
    }
    let (a, b) = (args[0], args[1]);
    let defines = |head: TermId, value: TermId| {
        crate::ematching::contains_quantifier(terms, value)
            && !crate::ematching::contains_quantifier(terms, head)
            && matches!(terms.get(head), TermData::App(Symbol::Named(name), _)
                if !crate::features::is_builtin_symbol_name(name))
            && vars.iter().all(|(name, _)| mentions_var(terms, head, name))
    };
    defines(a, b) || defines(b, a)
}

/// `true` when `term` contains a variable named `name`.
fn mentions_var(terms: &TermStore, term: TermId, name: &str) -> bool {
    let mut stack = vec![term];
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(var, _) if var == name => return true,
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, x, y) => stack.extend([*c, *x, *y]),
            _ => {}
        }
    }
    false
}

/// The NNF of `(= a b)` at `positive` polarity, split as the module doc says.
pub(super) fn rewrite(
    terms: &mut TermStore,
    a: TermId,
    b: TermId,
    positive: bool,
    universal_env: &[String],
    provenance: &mut Vec<ForallSkolemProvenance>,
) -> TermId {
    let a_true = rewrite_nnf_with_skolem(terms, a, true, universal_env, provenance);
    let a_false = rewrite_nnf_with_skolem(terms, a, false, universal_env, provenance);
    let b_true = rewrite_nnf_with_skolem(terms, b, true, universal_env, provenance);
    let b_false = rewrite_nnf_with_skolem(terms, b, false, universal_env, provenance);
    if positive {
        let forward = terms.mk_or(vec![a_false, b_true]);
        let backward = terms.mk_or(vec![a_true, b_false]);
        terms.mk_and(vec![forward, backward])
    } else {
        let left = terms.mk_and(vec![a_true, b_false]);
        let right = terms.mk_and(vec![a_false, b_true]);
        terms.mk_or(vec![left, right])
    }
}

#[cfg(test)]
mod tests;
