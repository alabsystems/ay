// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict validation for certified quantifier proof steps.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

fn invalid(step: ProofId, reason: impl Into<String>) -> ProofCheckError {
    ProofCheckError::InvalidBooleanRule {
        step,
        rule: "sko_forall".to_string(),
        reason: reason.into(),
    }
}

fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Exact, capture-safe single-binder substitution matcher.
///
/// The dedicated producer is intentionally restricted to a quantifier-free
/// body, so encountering any nested binder/let fails closed instead of trying
/// to approximate shadowing or alpha-renaming.
fn matches_single_substitution(
    terms: &TermStore,
    pattern: TermId,
    instance: TermId,
    binder: &str,
    witness: TermId,
) -> bool {
    match terms.get(pattern) {
        TermData::Var(name, _) if name == binder => instance == witness,
        TermData::Var(..) | TermData::Const(..) => pattern == instance,
        TermData::Not(inner) => matches!(
            terms.get(instance),
            TermData::Not(actual)
                if matches_single_substitution(terms, *inner, *actual, binder, witness)
        ),
        TermData::Ite(c, t, e) => matches!(
            terms.get(instance),
            TermData::Ite(ac, at, ae)
                if matches_single_substitution(terms, *c, *ac, binder, witness)
                    && matches_single_substitution(terms, *t, *at, binder, witness)
                    && matches_single_substitution(terms, *e, *ae, binder, witness)
        ),
        TermData::App(symbol, args) => {
            let TermData::App(actual_symbol, actual_args) = terms.get(instance) else {
                return false;
            };
            symbol == actual_symbol
                && args.len() == actual_args.len()
                && args.iter().zip(actual_args).all(|(&expected, &actual)| {
                    matches_single_substitution(terms, expected, actual, binder, witness)
                })
        }
        TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => false,
        _ => false,
    }
}

fn term_contains(terms: &TermStore, root: TermId, needle: TermId) -> bool {
    if root == needle {
        return true;
    }
    match terms.get(root) {
        TermData::App(_, args) => args.iter().any(|&arg| term_contains(terms, arg, needle)),
        TermData::Not(inner) => term_contains(terms, *inner, needle),
        TermData::Ite(c, t, e) => {
            term_contains(terms, *c, needle)
                || term_contains(terms, *t, needle)
                || term_contains(terms, *e, needle)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| term_contains(terms, *value, needle))
                || term_contains(terms, *body, needle)
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            term_contains(terms, *body, needle)
                || triggers
                    .iter()
                    .flatten()
                    .any(|&term| term_contains(terms, term, needle))
        }
        _ => false,
    }
}

/// Validate the internal flat representation of Alethe `sko_forall`.
///
/// Shape: a premiseless unit equality
/// `forall ((x S)) phi(x) = phi(sk)` with exactly one argument `sk`.
/// The argument must be a registered fresh Skolem constant of sort `S`, absent
/// from the quantified source, and the right side must be the exact structural
/// substitution of `sk` for `x`. The printer expands this one flat step into
/// Carcara's required assignment anchor, inner `refl`, and outer `sko_forall`.
pub(crate) fn validate_sko_forall(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
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
    let TermData::Forall(bindings, body, _) = terms.get(quantified) else {
        return Err(invalid(step, "equality left side must be a forall"));
    };
    let [(binder, binder_sort)] = bindings.as_slice() else {
        return Err(invalid(step, "only a single forall binding is supported"));
    };
    let TermData::Var(witness_name, _) = terms.get(*witness) else {
        return Err(invalid(step, "witness must be an atomic fresh constant"));
    };
    if !terms.is_skolem_symbol(witness_name) {
        return Err(invalid(
            step,
            "witness is not registered as a Skolem symbol",
        ));
    }
    if terms.sort(*witness) != binder_sort {
        return Err(invalid(
            step,
            "witness sort does not match the forall binding",
        ));
    }
    if term_contains(terms, quantified, *witness) {
        return Err(invalid(
            step,
            "fresh witness occurs in the quantified source",
        ));
    }
    if terms.sort(instance) != &Sort::Bool {
        return Err(invalid(step, "instantiated body must be Boolean"));
    }
    if !matches_single_substitution(terms, *body, instance, binder, *witness) {
        return Err(invalid(
            step,
            "right side is not the exact registered-witness substitution",
        ));
    }
    Ok(())
}

/// Enforce the whole-proof one-to-one provenance invariant for flat Skolem
/// steps.
///
/// A witness is rendered as one concrete Hilbert-choice term by the Alethe
/// printer. Reusing it for another `forall` would give the same internal
/// constant two incompatible external definitions; duplicating a source with
/// another witness would likewise cease to represent the skolemizer's exact
/// source-to-witness mapping. The per-step checker validates the substitution;
/// this pass validates that the mapping is globally a partial bijection.
pub(crate) fn validate_sko_forall_uniqueness(
    proof: &Proof,
    terms: &TermStore,
) -> Result<(), ProofCheckError> {
    let mut source_to_witness: HashMap<TermId, (TermId, ProofId)> = HashMap::default();
    let mut witness_to_source: HashMap<TermId, (TermId, ProofId)> = HashMap::default();

    for (index, proof_step) in proof.steps.iter().enumerate() {
        let ProofStep::Step {
            rule: AletheRule::Skolem,
            clause,
            args,
            ..
        } = proof_step
        else {
            continue;
        };
        let step = ProofId(index as u32);
        // Per-step validation runs before this whole-proof pass in every strict
        // entry point. Decode defensively anyway so this helper also fails
        // closed when exercised directly by its mutation tests.
        validate_sko_forall(terms, step, clause, 0, args)?;
        let [equality] = clause.as_slice() else {
            unreachable!("validated one-literal Skolem clause")
        };
        let Some((source, _)) = decode_eq(terms, *equality) else {
            unreachable!("validated Skolem equality")
        };
        let [witness] = args.as_slice() else {
            unreachable!("validated one-witness Skolem arguments")
        };

        if let Some((prior_witness, prior_step)) =
            source_to_witness.insert(source, (*witness, step))
        {
            return Err(invalid(
                step,
                format!(
                    "forall source was already bound to witness {prior_witness} at {prior_step}"
                ),
            ));
        }
        if let Some((prior_source, prior_step)) = witness_to_source.insert(*witness, (source, step))
        {
            return Err(invalid(
                step,
                format!(
                    "Skolem witness was already bound to forall {prior_source} at {prior_step}"
                ),
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ay_core::{Sort, Symbol};

    use super::*;

    fn fixture() -> (TermStore, TermId, TermId, TermId) {
        let mut terms = TermStore::new();
        let x = terms.mk_var("sko_x", Sort::Int);
        let body = terms.mk_app(Symbol::named("sko_p"), [x], Sort::Bool);
        let quant = terms.mk_forall(vec![("sko_x".to_string(), Sort::Int)], body);
        let witness = terms.mk_var("sk!sko_x_test", Sort::Int);
        terms.mark_skolem_symbol("sk!sko_x_test");
        let instance = terms.mk_app(Symbol::named("sko_p"), [witness], Sort::Bool);
        let equality = terms.mk_eq(quant, instance);
        (terms, equality, witness, quant)
    }

    #[test]
    fn exact_registered_single_substitution_is_valid() {
        let (terms, equality, witness, _) = fixture();
        validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness])
            .expect("exact registered Skolem substitution must validate");
    }

    #[test]
    fn unregistered_witness_is_rejected() {
        let (mut terms, _, _, quant) = fixture();
        let forged = terms.mk_var("ordinary_constant", Sort::Int);
        let instance = terms.mk_app(Symbol::named("sko_p"), [forged], Sort::Bool);
        let equality = terms.mk_eq(quant, instance);
        assert!(validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[forged]).is_err());
    }

    #[test]
    fn wrong_instantiated_body_is_rejected() {
        let (mut terms, _, witness, quant) = fixture();
        let wrong = terms.mk_app(Symbol::named("different_predicate"), [witness], Sort::Bool);
        let equality = terms.mk_eq(quant, wrong);
        assert!(validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness]).is_err());
    }

    #[test]
    fn premises_and_extra_args_are_rejected() {
        let (terms, equality, witness, _) = fixture();
        assert!(validate_sko_forall(&terms, ProofId(0), &[equality], 1, &[witness]).is_err());
        assert!(
            validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness, witness]).is_err()
        );
    }

    #[test]
    fn one_witness_cannot_certify_two_incompatible_foralls() {
        let (mut terms, equality1, witness, _) = fixture();
        let y = terms.mk_var("sko_y", Sort::Int);
        let body2 = terms.mk_app(Symbol::named("sko_q"), [y], Sort::Bool);
        let quant2 = terms.mk_forall(vec![("sko_y".to_string(), Sort::Int)], body2);
        let instance2 = terms.mk_app(Symbol::named("sko_q"), [witness], Sort::Bool);
        let equality2 = terms.mk_app(Symbol::named("="), [quant2, instance2], Sort::Bool);

        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::Skolem, vec![equality1], vec![], vec![witness]);
        proof.add_rule_step(AletheRule::Skolem, vec![equality2], vec![], vec![witness]);
        let err = validate_sko_forall_uniqueness(&proof, &terms)
            .expect_err("one witness must not acquire two choice definitions");
        assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
    }
}
