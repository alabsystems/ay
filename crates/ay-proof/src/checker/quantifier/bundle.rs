// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-proof Skolem freshness, uniqueness, and dependency authentication.

use super::*;

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

struct BundleRegistry<'a> {
    by_name: HashMap<String, TermId>,
    binding_by_witness: HashMap<TermId, &'a SkolemBinding>,
    fallback_step: ProofId,
}

fn build_bundle_registry<'a>(
    bindings: &'a [SkolemBinding],
    declaration_term_symbols: &HashMap<String, &'static str>,
) -> Result<BundleRegistry<'a>, ProofCheckError> {
    let Some(fallback_step) = bindings.first().map(|binding| binding.step) else {
        return Err(invalid(
            ProofId(0),
            "bundle registry requires at least one authenticated Skolem binding",
        ));
    };
    let mut registry = BundleRegistry {
        by_name: HashMap::default(),
        binding_by_witness: HashMap::default(),
        fallback_step,
    };
    for binding in bindings {
        if let Some(role) = declaration_term_symbols.get(&binding.name) {
            return Err(invalid(
                binding.step,
                format!(
                    "Skolem symbol `{}` collides with {role} in the serialized datatype declaration-owned term namespace",
                    binding.name,
                ),
            ));
        }
        if let Some(prior) = registry
            .by_name
            .insert(binding.name.clone(), binding.witness)
        {
            return Err(invalid(
                binding.step,
                format!(
                    "Skolem symbol name `{}` is shared by witnesses {prior} and {}",
                    binding.name, binding.witness
                ),
            ));
        }
        registry.binding_by_witness.insert(binding.witness, binding);
    }
    Ok(registry)
}

fn validate_global_name_freshness(
    terms: &TermStore,
    registry: &BundleRegistry<'_>,
) -> Result<(), ProofCheckError> {
    for index in 0..terms.len() {
        let term = TermId::new(index as u32);
        let check_name = |name: &str, role: &str| -> Result<(), ProofCheckError> {
            let Some(&witness) = registry.by_name.get(name) else {
                return Ok(());
            };
            if term != witness || role != "atomic witness" {
                let Some(binding) = registry.binding_by_witness.get(&witness).copied() else {
                    return Err(invalid(
                        registry.fallback_step,
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
    Ok(())
}

fn validate_problem_freshness(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    registry: &BundleRegistry<'_>,
) -> Result<(), ProofCheckError> {
    let mut work = 0usize;
    let roots = problem_assertions
        .iter()
        .copied()
        .chain(proof.steps.iter().filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        }));
    let mentioned = collect_candidate_witnesses(terms, roots, &registry.by_name, &mut work)
        .map_err(|()| {
            invalid(
                registry.fallback_step,
                format!(
                    "Skolem freshness validation exceeds {BUNDLE_SKOLEM_DEPENDENCY_WORK_LIMIT} distinct term states"
                ),
            )
        })?;
    let Some(witness) = mentioned.into_iter().next() else {
        return Ok(());
    };
    let Some(binding) = registry.binding_by_witness.get(&witness).copied() else {
        return Err(invalid(
            registry.fallback_step,
            "Skolem freshness scan references an unknown witness",
        ));
    };
    Err(invalid(
        binding.step,
        format!(
            "Skolem witness `{}` is not fresh: it occurs in the claimed problem obligation or an Assume step",
            binding.name
        ),
    ))
}

fn validate_acyclic_dependencies(
    terms: &TermStore,
    bindings: &[SkolemBinding],
    registry: &BundleRegistry<'_>,
) -> Result<(), ProofCheckError> {
    let mut work = 0usize;
    let mut indegree: HashMap<TermId, usize> = HashMap::default();
    let mut dependents: HashMap<TermId, Vec<TermId>> = HashMap::default();
    for binding in bindings {
        let dependencies = collect_candidate_witnesses(
            terms,
            std::iter::once(binding.source),
            &registry.by_name,
            &mut work,
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
    validate_dependency_topology(bindings, registry, indegree, &dependents)
}

fn validate_dependency_topology(
    bindings: &[SkolemBinding],
    registry: &BundleRegistry<'_>,
    mut indegree: HashMap<TermId, usize>,
    dependents: &HashMap<TermId, Vec<TermId>>,
) -> Result<(), ProofCheckError> {
    let mut ready: Vec<TermId> = indegree
        .iter()
        .filter_map(|(&witness, &degree)| (degree == 0).then_some(witness))
        .collect();
    let mut removed = 0usize;
    while let Some(witness) = ready.pop() {
        removed += 1;
        for &dependent in dependents.get(&witness).into_iter().flatten() {
            let Some(degree) = indegree.get_mut(&dependent) else {
                let step = registry
                    .binding_by_witness
                    .get(&witness)
                    .map_or(registry.fallback_step, |binding| binding.step);
                return Err(invalid(
                    step,
                    "Skolem dependency graph references an unregistered witness",
                ));
            };
            let Some(next_degree) = degree.checked_sub(1) else {
                return Err(invalid(
                    registry.fallback_step,
                    "Skolem dependency graph indegree underflow",
                ));
            };
            *degree = next_degree;
            if *degree == 0 {
                ready.push(dependent);
            }
        }
    }
    if removed == bindings.len() {
        return Ok(());
    }
    let Some((&witness, _)) = indegree.iter().find(|(_, degree)| **degree != 0) else {
        return Err(invalid(
            registry.fallback_step,
            "Skolem dependency graph residual is inconsistent",
        ));
    };
    let Some(binding) = registry.binding_by_witness.get(&witness).copied() else {
        return Err(invalid(
            registry.fallback_step,
            "Skolem dependency cycle references an unknown witness",
        ));
    };
    Err(invalid(
        binding.step,
        format!(
            "Skolem witness `{}` participates in a cyclic choice dependency",
            binding.name
        ),
    ))
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
    if bindings.is_empty() {
        return Ok(Vec::new());
    }
    let registry = build_bundle_registry(&bindings, declaration_term_symbols)?;
    validate_global_name_freshness(terms, &registry)?;
    validate_problem_freshness(proof, terms, problem_assertions, &registry)?;
    validate_acyclic_dependencies(terms, &bindings, &registry)?;

    Ok(bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect())
}
