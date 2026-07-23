// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict validation for certified quantifier proof steps.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

fn invalid(step: ProofId, reason: impl Into<String>) -> ProofCheckError {
    ProofCheckError::InvalidBooleanRule {
        step,
        rule: "sko_forall".to_string(),
        reason: reason.into(),
    }
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
    work: &mut usize,
) -> Option<bool> {
    let mut visited = HashSet::default();
    let mut stack = vec![(pattern, instance)];
    while let Some((expected, actual)) = stack.pop() {
        if !visited.insert((expected, actual)) {
            continue;
        }
        if *work >= SKOLEM_TERM_WORK_LIMIT {
            return None;
        }
        *work += 1;
        if terms.sort(expected) != terms.sort(actual) {
            return Some(false);
        }
        match terms.get(expected) {
            TermData::Var(name, _) if name == binder => {
                if actual != witness {
                    return Some(false);
                }
            }
            TermData::Var(..) | TermData::Const(..) => {
                if expected != actual {
                    return Some(false);
                }
            }
            TermData::Not(inner) => {
                let TermData::Not(actual_inner) = terms.get(actual) else {
                    return Some(false);
                };
                stack.push((*inner, *actual_inner));
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                let TermData::Ite(actual_condition, actual_then, actual_else) = terms.get(actual)
                else {
                    return Some(false);
                };
                stack.extend([
                    (*condition, *actual_condition),
                    (*then_branch, *actual_then),
                    (*else_branch, *actual_else),
                ]);
            }
            TermData::App(symbol, args) => {
                let TermData::App(actual_symbol, actual_args) = terms.get(actual) else {
                    return Some(false);
                };
                if symbol != actual_symbol || args.len() != actual_args.len() {
                    return Some(false);
                }
                stack.extend(args.iter().copied().zip(actual_args.iter().copied()));
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {
                return Some(false);
            }
            _ => return Some(false),
        }
    }
    Some(true)
}

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
    let TermData::Forall(bindings, body, _) = terms.get(quantified) else {
        return Err(invalid(step, "equality left side must be a forall"));
    };
    let [(binder, binder_sort)] = bindings.as_slice() else {
        return Err(invalid(step, "only a single forall binding is supported"));
    };
    let TermData::Var(witness_name, _) = terms.get(*witness) else {
        return Err(invalid(step, "witness must be an atomic fresh constant"));
    };
    if matches!(authority, SkolemWitnessAuthority::TermStoreRegistry)
        && !terms.is_skolem_symbol(witness_name)
    {
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
    match term_contains(terms, quantified, *witness, work) {
        Some(true) => {
            return Err(invalid(
                step,
                "fresh witness occurs in the quantified source",
            ));
        }
        None => {
            return Err(invalid(
                step,
                format!(
                    "fresh-witness source scan exceeds {SKOLEM_TERM_WORK_LIMIT} distinct terms"
                ),
            ));
        }
        Some(false) => {}
    }
    if terms.sort(instance) != &Sort::Bool {
        return Err(invalid(step, "instantiated body must be Boolean"));
    }
    match matches_single_substitution(terms, *body, instance, binder, *witness, work) {
        Some(true) => {}
        Some(false) => {
            return Err(invalid(
                step,
                "right side is not the exact registered-witness substitution",
            ));
        }
        None => {
            return Err(invalid(
                step,
                format!(
                    "registered-witness substitution check exceeds {SKOLEM_TERM_WORK_LIMIT} distinct term pairs"
                ),
            ));
        }
    }
    Ok(())
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

#[derive(Clone)]
struct SkolemBinding {
    step: ProofId,
    source: TermId,
    witness: TermId,
    name: String,
}

fn collect_skolem_bindings(
    proof: &Proof,
    terms: &TermStore,
    authority: SkolemWitnessAuthority,
) -> Result<Vec<SkolemBinding>, ProofCheckError> {
    let mut source_to_witness: HashMap<TermId, (TermId, ProofId)> = HashMap::default();
    let mut witness_to_source: HashMap<TermId, (TermId, ProofId)> = HashMap::default();
    let mut bindings = Vec::new();
    let mut work = 0usize;

    for (index, proof_step) in proof.steps.iter().enumerate() {
        let ProofStep::Step {
            rule: AletheRule::Skolem,
            clause,
            premises,
            args,
        } = proof_step
        else {
            continue;
        };
        let step = ProofId(index as u32);
        validate_sko_forall_with_authority(
            terms,
            step,
            clause,
            premises.len(),
            args,
            authority,
            &mut work,
        )?;
        let [equality] = clause.as_slice() else {
            return Err(invalid(
                step,
                "validated Skolem step lost its single conclusion literal",
            ));
        };
        let Some((source, _)) = decode_eq(terms, *equality) else {
            return Err(invalid(
                step,
                "validated Skolem step lost its equality source",
            ));
        };
        let [witness] = args.as_slice() else {
            return Err(invalid(
                step,
                "validated Skolem step lost its single witness argument",
            ));
        };
        let TermData::Var(name, _) = terms.get(*witness) else {
            return Err(invalid(
                step,
                "validated Skolem witness is no longer atomic",
            ));
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
        bindings.push(SkolemBinding {
            step,
            source,
            witness: *witness,
            name: name.clone(),
        });
    }
    Ok(bindings)
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
    let _ = collect_skolem_bindings(proof, terms, SkolemWitnessAuthority::TermStoreRegistry)?;
    Ok(())
}

const BUNDLE_SKOLEM_DEPENDENCY_WORK_LIMIT: usize = 100_000;

fn push_children_and_collect_names(
    terms: &TermStore,
    term: TermId,
    candidate_names: &HashMap<String, TermId>,
    found: &mut HashSet<TermId>,
    stack: &mut Vec<TermId>,
) {
    let mut record_name = |name: &str| {
        if let Some(&witness) = candidate_names.get(name) {
            found.insert(witness);
        }
    };
    match terms.get(term) {
        TermData::Var(name, _) => record_name(name),
        TermData::App(symbol, args) => {
            record_name(symbol.name());
            stack.extend(args.iter().copied());
        }
        TermData::Let(bindings, body) => {
            for (name, value) in bindings {
                record_name(name);
                stack.push(*value);
            }
            stack.push(*body);
        }
        TermData::Not(inner) => stack.push(*inner),
        TermData::Ite(condition, then_branch, else_branch) => {
            stack.extend([*condition, *then_branch, *else_branch]);
        }
        TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
            for (name, _) in vars {
                record_name(name);
            }
            stack.push(*body);
            stack.extend(triggers.iter().flatten().copied());
        }
        _ => {}
    }
}

fn collect_candidate_witnesses(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
    candidate_names: &HashMap<String, TermId>,
    work: &mut usize,
) -> Result<HashSet<TermId>, ()> {
    let mut found = HashSet::default();
    let mut visited = HashSet::default();
    let mut stack: Vec<TermId> = roots.into_iter().collect();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if *work >= BUNDLE_SKOLEM_DEPENDENCY_WORK_LIMIT {
            return Err(());
        }
        *work += 1;
        push_children_and_collect_names(terms, term, candidate_names, &mut found, &mut stack);
    }
    Ok(found)
}

/// Authenticate the Skolem constants carried by an offline proof bundle from
/// proof content rather than trusting a serialized producer-side name list.
///
/// Each candidate must already satisfy the exact `sko_forall` substitution
/// schema. This pass additionally proves the conditions supplied by the live
/// solver's creation-site registry: one name and term per source, freshness
/// against the claimed problem/assumptions, unambiguous symbol identity in the
/// snapshot and serialized datatype declaration context, and acyclic
/// dependencies between multiple choice definitions. The returned names may
/// then be restored into a checker-only [`TermStore`].
pub(crate) fn authenticate_bundle_skolems(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    declaration_term_symbols: &HashMap<String, &'static str>,
) -> Result<Vec<String>, ProofCheckError> {
    let bindings = collect_skolem_bindings(proof, terms, SkolemWitnessAuthority::ProofBundle)?;
    let Some(fallback_step) = bindings.first().map(|binding| binding.step) else {
        return Ok(Vec::new());
    };

    let mut by_name: HashMap<String, TermId> = HashMap::default();
    let mut binding_by_witness: HashMap<TermId, &SkolemBinding> = HashMap::default();
    for binding in &bindings {
        if let Some(role) = declaration_term_symbols.get(&binding.name) {
            return Err(invalid(
                binding.step,
                format!(
                    "Skolem symbol `{}` collides with {role} in the serialized datatype declaration-owned term namespace",
                    binding.name,
                ),
            ));
        }
        if let Some(prior) = by_name.insert(binding.name.clone(), binding.witness) {
            return Err(invalid(
                binding.step,
                format!(
                    "Skolem symbol name `{}` is shared by witnesses {prior} and {}",
                    binding.name, binding.witness
                ),
            ));
        }
        binding_by_witness.insert(binding.witness, binding);
    }

    // A live Skolem name is globally fresh. Re-establish the equivalent
    // invariant for the untrusted snapshot: the name may identify only this
    // exact atomic witness, never another variable, function head, or binder.
    for index in 0..terms.len() {
        let term = TermId::new(index as u32);
        let check_name = |name: &str, role: &str| -> Result<(), ProofCheckError> {
            let Some(&witness) = by_name.get(name) else {
                return Ok(());
            };
            if term != witness || role != "atomic witness" {
                let Some(binding) = binding_by_witness.get(&witness).copied() else {
                    return Err(invalid(
                        fallback_step,
                        "Skolem name registry references an unknown witness",
                    ));
                };
                return Err(invalid(
                    binding.step,
                    format!(
                        "Skolem symbol `{name}` is not globally fresh: term {term} also uses it as {role}"
                    ),
                ));
            }
            Ok(())
        };
        match terms.get(term) {
            TermData::Var(name, _) => check_name(name, "atomic witness")?,
            TermData::App(symbol, _) => check_name(symbol.name(), "an application head")?,
            TermData::Let(bindings, _) => {
                for (name, _) in bindings {
                    check_name(name, "a let binder")?;
                }
            }
            TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) => {
                for (name, _) in vars {
                    check_name(name, "a quantifier binder")?;
                }
            }
            _ => {}
        }
    }

    // A Skolem choice is conservative only when the original obligation does
    // not already constrain its symbol. Assumptions are included defensively;
    // the context-bound checker separately requires every Assume to come from
    // the problem, but keeping the freshness condition local avoids relying on
    // validation order.
    let mut freshness_work = 0usize;
    let roots = problem_assertions
        .iter()
        .copied()
        .chain(proof.steps.iter().filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        }));
    let mentioned = collect_candidate_witnesses(terms, roots, &by_name, &mut freshness_work)
        .map_err(|()| {
            invalid(
                fallback_step,
                format!(
                    "Skolem freshness validation exceeds {BUNDLE_SKOLEM_DEPENDENCY_WORK_LIMIT} distinct term states"
                ),
            )
        })?;
    if let Some(witness) = mentioned.into_iter().next() {
        let Some(binding) = binding_by_witness.get(&witness).copied() else {
            return Err(invalid(
                fallback_step,
                "Skolem freshness scan references an unknown witness",
            ));
        };
        return Err(invalid(
            binding.step,
            format!(
                "Skolem witness `{}` is not fresh: it occurs in the claimed problem obligation or an Assume step",
                binding.name
            ),
        ));
    }

    // A source may depend on an earlier choice, but mutually recursive choices
    // need not have a joint fixed point. Build the witness dependency graph and
    // require a topological interpretation order, as for array diff witnesses.
    let mut dependency_work = 0usize;
    let mut indegree: HashMap<TermId, usize> = HashMap::default();
    let mut dependents: HashMap<TermId, Vec<TermId>> = HashMap::default();
    for binding in &bindings {
        let dependencies = collect_candidate_witnesses(
            terms,
            std::iter::once(binding.source),
            &by_name,
            &mut dependency_work,
        )
        .map_err(|()| {
            invalid(
                binding.step,
                format!(
                    "Skolem dependency validation exceeds {BUNDLE_SKOLEM_DEPENDENCY_WORK_LIMIT} distinct term states"
                ),
            )
        })?;
        if dependencies.contains(&binding.witness) {
            return Err(invalid(
                binding.step,
                format!(
                    "Skolem witness `{}` occurs in its own quantified source",
                    binding.name
                ),
            ));
        }
        indegree.insert(binding.witness, dependencies.len());
        for dependency in dependencies {
            dependents
                .entry(dependency)
                .or_default()
                .push(binding.witness);
        }
    }

    let mut ready: Vec<TermId> = indegree
        .iter()
        .filter_map(|(&witness, &degree)| (degree == 0).then_some(witness))
        .collect();
    let mut removed = 0usize;
    while let Some(witness) = ready.pop() {
        removed += 1;
        for &dependent in dependents.get(&witness).into_iter().flatten() {
            let Some(degree) = indegree.get_mut(&dependent) else {
                let step = binding_by_witness
                    .get(&witness)
                    .map_or(fallback_step, |binding| binding.step);
                return Err(invalid(
                    step,
                    "Skolem dependency graph references an unregistered witness",
                ));
            };
            let Some(next_degree) = degree.checked_sub(1) else {
                return Err(invalid(
                    fallback_step,
                    "Skolem dependency graph indegree underflow",
                ));
            };
            *degree = next_degree;
            if *degree == 0 {
                ready.push(dependent);
            }
        }
    }
    if removed != bindings.len() {
        let Some((&witness, _)) = indegree.iter().find(|(_, degree)| **degree != 0) else {
            return Err(invalid(
                fallback_step,
                "Skolem dependency graph residual is inconsistent",
            ));
        };
        let Some(binding) = binding_by_witness.get(&witness).copied() else {
            return Err(invalid(
                fallback_step,
                "Skolem dependency cycle references an unknown witness",
            ));
        };
        return Err(invalid(
            binding.step,
            format!(
                "Skolem witness `{}` participates in a cyclic choice dependency",
                binding.name
            ),
        ));
    }

    Ok(bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect())
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
