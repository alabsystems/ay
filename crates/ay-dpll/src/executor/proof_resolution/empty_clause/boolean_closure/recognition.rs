// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural recognition helpers for the Boolean-closure route.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Constant, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

/// The leaves a closer may resolve against: `assume` steps and the premiseless
/// unit `trust` steps that later repair lanes turn back into derivations.
///
/// Identical to the set [`super::super::derive_empty_via_trust_lemma`] collects,
/// so this route and the trust closer see the same proof.
pub(super) fn collect_leaves(proof: &Proof) -> Vec<(ProofId, TermId)> {
    proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(idx, step)| match step {
            ProofStep::Assume(term) => Some((ProofId(idx as u32), *term)),
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } if clause.len() == 1 && premises.is_empty() => Some((ProofId(idx as u32), clause[0])),
            _ => None,
        })
        .collect()
}

/// The atom under a literal.
pub(super) fn atom_of(terms: &TermStore, lit: TermId) -> TermId {
    match terms.get(lit) {
        TermData::Not(inner) => *inner,
        _ => lit,
    }
}

/// Decode `(or D1 .. Dn)`.
pub(super) fn decode_or(terms: &TermStore, term: TermId) -> Option<Vec<TermId>> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "or" && args.len() >= 2 => {
            Some(args.clone())
        }
        _ => None,
    }
}

/// A numeric expression the LRA rows and the `la_generic` checker accept.
fn numeric_expr(terms: &TermStore, t: TermId) -> bool {
    match terms.get(t) {
        TermData::Const(Constant::Int(_) | Constant::Rational(_)) => true,
        TermData::Var(..) => matches!(terms.sort(t), Sort::Int | Sort::Real),
        TermData::App(Symbol::Named(name), args) => {
            matches!(name.as_str(), "+" | "-" | "*" | "/")
                && args.iter().all(|&a| numeric_expr(terms, a))
        }
        _ => false,
    }
}

/// A pure arithmetic inequality literal over numeric leaves.
///
/// Equalities are excluded on purpose: they are discharged by the triangle
/// arm, whose certificate is a checked schema rather than a Farkas row.
pub(super) fn arith_inequality(terms: &TermStore, lit: TermId) -> bool {
    matches!(
        terms.get(atom_of(terms, lit)),
        TermData::App(Symbol::Named(name), args)
            if args.len() == 2
                && matches!(name.as_str(), "<" | "<=" | ">" | ">=")
                && args.iter().all(|&a| numeric_expr(terms, a))
    )
}

/// Decode `(not (= a b))` over a shared arithmetic sort.
pub(super) fn decode_negated_arith_equality(
    terms: &TermStore,
    lit: TermId,
) -> Option<(TermId, TermId, TermId)> {
    let TermData::Not(inner) = terms.get(lit) else {
        return None;
    };
    let eq = *inner;
    let TermData::App(Symbol::Named(name), args) = terms.get(eq) else {
        return None;
    };
    if name != "=" || args.len() != 2 {
        return None;
    }
    let (lhs, rhs) = (args[0], args[1]);
    let sort = terms.sort(lhs);
    if sort != terms.sort(rhs) || !matches!(sort, Sort::Int | Sort::Real) {
        return None;
    }
    Some((eq, lhs, rhs))
}

/// Find the leaf spelling `(<= lhs rhs)`, without interning anything.
///
/// Two reasons, and only the second is soundness. Interning on a speculative
/// path would grow the store for a candidate this closer may go on to decline;
/// and the triangle is only useful if BOTH bounds are leaves the chain can
/// resolve it against, which `discharge_to_unit` re-checks. The two together
/// are what enforce "every resolved literal cites an existing leaf" — see the
/// parent's `GUARD_MUTATION_LEDGER`, which records that neither alone does.
pub(super) fn find_le_leaf(
    terms: &TermStore,
    units: &HashMap<TermId, ProofId>,
    lhs: TermId,
    rhs: TermId,
) -> Option<TermId> {
    units.keys().copied().find(|&candidate| {
        matches!(
            terms.get(candidate),
            TermData::App(Symbol::Named(name), args)
                if name == "<=" && args.len() == 2 && args[0] == lhs && args[1] == rhs
        )
    })
}

/// The leaf spelling the exact complement of `lit`, if the proof carries one.
///
/// Nothing is interned: for a positive `lit` the complement can only be the
/// already-interned `(not lit)`, and interning is injective, so at most one
/// leaf can match and the answer is deterministic.
pub(super) fn find_complement_leaf(
    terms: &TermStore,
    units: &HashMap<TermId, ProofId>,
    lit: TermId,
) -> Option<(TermId, ProofId)> {
    if let TermData::Not(inner) = terms.get(lit) {
        let inner = *inner;
        return units.get(&inner).map(|&id| (inner, id));
    }
    units
        .iter()
        .find(|(&leaf, _)| matches!(terms.get(leaf), TermData::Not(inner) if *inner == lit))
        .map(|(&leaf, &id)| (leaf, id))
}
