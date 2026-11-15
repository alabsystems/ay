// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact candidate dependency graph and budgeted Kahn topological validation.

use super::meter::{add, id_map_entry, invalid_named};
use super::walk::collect_candidate_witnesses;
use super::*;

pub(super) fn validate_acyclic_dependencies(
    terms: &TermStore,
    bindings: &[SkolemBinding],
    registry: &BundleRegistry<'_>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    let mut indegree = HashMap::<TermId, usize>::default();
    let mut dependents = HashMap::<TermId, Vec<TermId>>::default();
    let mut edge_count = 0usize;
    for binding in bindings {
        let mut roots = Vec::new();
        meter.push(&mut roots, binding.source)?;
        let dependencies = collect_candidate_witnesses(terms, roots, &registry.by_name, meter)?;
        meter.lookup("", dependencies.len())?;
        if dependencies.contains(&binding.witness) {
            return Err(invalid_named(
                meter,
                binding.step,
                "Skolem witness occurs in its own quantified source",
                &[&binding.name],
            )?);
        }
        id_map_entry(meter, &indegree, binding.witness)?;
        indegree.insert(binding.witness, dependencies.len());
        meter.table_iteration(dependencies.len())?;
        for dependency in dependencies {
            // Bound the entire graph, not just each separate adjacency list.
            edge_count = add(edge_count, 1)?;
            if edge_count > SKOLEM_TERM_WORK_LIMIT {
                return Err(ProofCheckError::ResourceLimit);
            }
            id_map_entry(meter, &dependents, dependency)?;
            meter.push(dependents.entry(dependency).or_default(), binding.witness)?;
        }
    }
    validate_dependency_topology(bindings, registry, indegree, &dependents, meter)
}

fn validate_dependency_topology(
    bindings: &[SkolemBinding],
    registry: &BundleRegistry<'_>,
    mut indegree: HashMap<TermId, usize>,
    dependents: &HashMap<TermId, Vec<TermId>>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    let mut ready = Vec::new();
    meter.table_iteration(indegree.len())?;
    for (&witness, &degree) in &indegree {
        if degree == 0 {
            meter.push(&mut ready, witness)?;
        }
    }
    let mut removed = 0usize;
    while let Some(witness) = ready.pop() {
        meter.charge(1, 0)?;
        removed = add(removed, 1)?;
        meter.lookup("", dependents.len())?;
        for &dependent in dependents.get(&witness).into_iter().flatten() {
            meter.lookup("", indegree.len())?;
            let Some(degree) = indegree.get_mut(&dependent) else {
                return Err(
                    meter.invalid("Skolem dependency graph references an unregistered witness")?
                );
            };
            let Some(next_degree) = degree.checked_sub(1) else {
                return Err(meter.invalid("Skolem dependency graph indegree underflow")?);
            };
            *degree = next_degree;
            if *degree == 0 {
                meter.push(&mut ready, dependent)?;
            }
        }
    }
    if removed == bindings.len() {
        return meter.charge(0, 0);
    }
    meter.table_iteration(indegree.len())?;
    let Some((&witness, _)) = indegree.iter().find(|(_, degree)| **degree != 0) else {
        return Err(meter.invalid("Skolem dependency graph residual is inconsistent")?);
    };
    meter.lookup("", registry.binding_by_witness.len())?;
    let Some(binding) = registry.binding_by_witness.get(&witness).copied() else {
        return Err(meter.invalid("Skolem dependency cycle references an unknown witness")?);
    };
    Err(invalid_named(
        meter,
        binding.step,
        "Skolem witness participates in a cyclic choice dependency",
        &[&binding.name],
    )?)
}
