// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict validation for certified quantifier proof steps.

mod bundle;
mod forall_inst;
mod neg_exists;
mod skolem;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore};
pub(crate) use bundle::{authenticate_bundle_skolems, validate_sko_forall_uniqueness};
use forall_inst::matches_single_substitution;
pub(crate) use forall_inst::validate_forall_inst;
pub(crate) use neg_exists::validate_qnt_neg_exists;

use super::ProofCheckError;

fn invalid(step: ProofId, reason: impl Into<String>) -> ProofCheckError {
    invalid_rule(step, "sko_forall", reason)
}

fn invalid_rule(
    step: ProofId,
    rule: impl Into<String>,
    reason: impl Into<String>,
) -> ProofCheckError {
    ProofCheckError::InvalidBooleanRule {
        step,
        rule: rule.into(),
        reason: reason.into(),
    }
}

/// Validate the exact implication from an authored negated existential to its
/// universal NNF dual.
pub(crate) fn validate_negated_exists_dual(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let [not_source, dual] = clause else {
        return Err(invalid_rule(
            step,
            "quantifier_negated_exists_dual",
            "clause must contain exactly the negated source and its dual",
        ));
    };
    let TermData::Not(source) = terms.get(*not_source) else {
        return Err(invalid_rule(
            step,
            "quantifier_negated_exists_dual",
            "first literal must negate the source assertion",
        ));
    };
    let TermData::Not(exists) = terms.get(*source) else {
        return Err(invalid_rule(
            step,
            "quantifier_negated_exists_dual",
            "source assertion must be a negated existential",
        ));
    };
    let TermData::Exists(bindings, body, triggers) = terms.get(*exists) else {
        return Err(invalid_rule(
            step,
            "quantifier_negated_exists_dual",
            "source assertion must negate an existential",
        ));
    };
    let TermData::Forall(dual_bindings, dual_body, dual_triggers) = terms.get(*dual) else {
        return Err(invalid_rule(
            step,
            "quantifier_negated_exists_dual",
            "second literal must be the universal dual",
        ));
    };
    if bindings.is_empty()
        || bindings != dual_bindings
        || triggers != dual_triggers
        || terms.sort(*not_source) != &Sort::Bool
        || terms.sort(*dual) != &Sort::Bool
    {
        return Err(invalid_rule(
            step,
            "quantifier_negated_exists_dual",
            "dual must preserve the non-empty binder list, triggers, and Boolean sorts",
        ));
    }
    let body_matches = match terms.get(*body) {
        TermData::Not(inner) => *dual_body == *inner,
        _ => matches!(terms.get(*dual_body), TermData::Not(inner) if *inner == *body),
    };
    if !body_matches {
        return Err(invalid_rule(
            step,
            "quantifier_negated_exists_dual",
            "dual body must be the exact raw negation (with one double negation eliminated)",
        ));
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum SkolemWitnessAuthority {
    /// The live solver's Skolemizer registered the symbol at its creation site.
    TermStoreRegistry,
    /// An offline proof bundle is authenticating the symbol from proof shape,
    /// freshness, uniqueness, and an acyclic dependency graph instead.
    ProofBundle,
}

fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

const SKOLEM_TERM_WORK_LIMIT: usize = 100_000;

fn term_contains(
    terms: &TermStore,
    root: TermId,
    needle: TermId,
    work: &mut usize,
) -> Option<bool> {
    let mut visited = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if term == needle {
            return Some(true);
        }
        if !visited.insert(term) {
            continue;
        }
        if *work >= SKOLEM_TERM_WORK_LIMIT {
            return None;
        }
        *work += 1;
        match terms.get(term) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.extend([*condition, *then_branch, *else_branch]);
            }
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            _ => {}
        }
    }
    Some(false)
}

/// Validate the internal flat representation of Alethe `sko_forall`.
///
/// Shape: a premiseless unit equality
/// `forall ((x S)) phi(x) = phi(sk)` with exactly one argument `sk`.
/// The argument must be a registered fresh Skolem constant of sort `S`, absent
/// from the quantified source, and the right side must be the exact structural
/// substitution of `sk` for `x`. The printer expands this one flat step into
/// Carcara's required assignment anchor, inner `refl`, and outer `sko_forall`.
fn validate_sko_forall_with_authority(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
    authority: SkolemWitnessAuthority,
    work: &mut usize,
) -> Result<(), ProofCheckError> {
    if premise_count != 0 {
        return Err(invalid(step, "must not have premises"));
    }
    let [equality] = clause else {
        return Err(invalid(step, "conclusion must be one equality literal"));
    };
    let Some((quantified, instance)) = decode_eq(terms, *equality) else {
        return Err(invalid(step, "conclusion must be a binary equality"));
    };
    let [witness] = args else {
        return Err(invalid(
            step,
            "must carry exactly one Skolem witness argument",
        ));
    };
    let (bindings, body, source_is_exists) = match terms.get(quantified) {
        TermData::Forall(bindings, body, _) => (bindings, body, false),
        // The positive-`exists` flat form `(= (exists x. B) B[sk])` is the
        // `sko_ex` reading: `sk` is definitionally the Hilbert choice
        // `(choice x. B)`. It is admitted only with the live TermStore
        // registry as authority AND only when the registry's recorded choice
        // (binder, sort, UNNEGATED body) matches this exact quantifier, so a
        // witness minted for a different quantifier can never be borrowed.
        TermData::Exists(bindings, body, _) => (bindings, body, true),
        _ => return Err(invalid(step, "equality left side must be a quantifier")),
    };
    let [(binder, binder_sort)] = bindings.as_slice() else {
        return Err(invalid(
            step,
            "only a single quantifier binding is supported",
        ));
    };
    let body = *body;
    skolem::validate_witness_authority(
        terms,
        step,
        *witness,
        skolem::WitnessAuthorityCheck {
            binder,
            binder_sort,
            body,
            source_is_exists,
            authority,
        },
    )?;
    skolem::validate_fresh_substitution(
        terms,
        step,
        skolem::FreshSubstitutionCheck {
            quantified,
            body,
            instance,
            binder,
            witness: *witness,
        },
        work,
    )
}

/// Validate one `sko_forall` step against the live solver's authenticated
/// Skolem-symbol registry.
pub(crate) fn validate_sko_forall(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    let mut work = 0usize;
    validate_sko_forall_with_authority(
        terms,
        step,
        clause,
        premise_count,
        args,
        SkolemWitnessAuthority::TermStoreRegistry,
        &mut work,
    )
}

#[cfg(test)]
mod local_lane_tests;
#[cfg(test)]
mod tests;
