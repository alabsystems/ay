// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::sat_proof_manager::FragmentPropagationEnvironment;

const MAX_SEALED_DERIVATIONS: usize = 4096;

/// Seal the `PropagateValues` licensing environment for the c7 fragment
/// channel (#ppp-c7). Every entry and record is sealed and consumed through
/// its own epoch/stamp token; anything that fails to seal is silently
/// dropped (fail-closed: a missing map entry can only decline a plan).
pub(in super::super) fn sealed_propagation_environment(
    executor: &mut Executor,
) -> FragmentPropagationEnvironment {
    if !crate::quant_unit_authority::quant_unit_authority_enabled() {
        return FragmentPropagationEnvironment::default();
    }
    let mut environment = FragmentPropagationEnvironment::default();
    let entries = executor.propagated_value_provenance.entries.clone();
    for entry in entries.iter().take(MAX_SEALED_DERIVATIONS) {
        let Some(token) = CheckedPropagationEntry::seal(executor, entry) else {
            continue;
        };
        let Some((expr, licensed)) = token.into_current(executor) else {
            continue;
        };
        environment.entry_by_expr.entry(expr).or_insert(licensed);
    }
    let records = executor.propagated_value_provenance.rewrites.clone();
    for record in records.iter().take(MAX_SEALED_DERIVATIONS) {
        if environment.record_by_after.contains_key(&record.after) {
            continue;
        }
        let Some(token) = CheckedPropagationDerivation::seal(executor, record, &entries) else {
            continue;
        };
        let Some((after, bridge)) = token.into_current(executor) else {
            continue;
        };
        environment.record_by_after.entry(after).or_insert(bridge);
    }
    environment
}

/// Seal every qpf premise-forced instance root recorded for this query
/// (#ppp-c7).
pub(in super::super) fn sealed_instance_root_derivations(
    executor: &mut Executor,
) -> Vec<FragmentInstanceRootDerivation> {
    if !crate::quant_unit_authority::quant_unit_authority_enabled() {
        return Vec::new();
    }
    let records = executor.qpf_premise_forced_instance_records.clone();
    let mut derivations = Vec::new();
    for record in records.iter().take(MAX_SEALED_DERIVATIONS) {
        let Some(token) = CheckedInstanceRootDerivation::seal(executor, record) else {
            continue;
        };
        let Some(derivation) = token.into_current(executor) else {
            continue;
        };
        if !derivations.contains(&derivation) {
            derivations.push(derivation);
        }
    }
    derivations
}

/// Replay and seal every producer record that still belongs to this query.
pub(in super::super) fn sealed_fragment_derivation_maps(
    executor: &mut Executor,
) -> (
    HashMap<TermId, FragmentInstanceDerivation>,
    HashMap<TermId, FragmentSkolemDerivation>,
) {
    if !crate::quant_unit_authority::quant_unit_authority_enabled() {
        return (HashMap::default(), HashMap::default());
    }
    let mut instance_map = HashMap::default();
    let mut candidates: Vec<(TermId, Vec<TermId>, TermId, TermId)> = executor
        .ematching_proof_records
        .iter()
        .map(|record| {
            (
                record.quantifier,
                record.binding.clone(),
                record.instance,
                record.instance,
            )
        })
        .collect();
    for record in &executor.quant_expansion_records {
        candidates.extend(
            record
                .instances
                .iter()
                .map(|(values, instance)| (record.original, values.clone(), *instance, *instance)),
        );
    }
    for record in &executor.bv_mbqi_false_instance_records {
        candidates.push((
            record.quantifier,
            record.values.clone(),
            record.instance,
            record.asserted,
        ));
    }
    for (quantifier, values, instance, asserted) in
        candidates.into_iter().take(MAX_SEALED_DERIVATIONS)
    {
        if instance_map.contains_key(&asserted) {
            continue;
        }
        let Some(token) =
            CheckedInstanceDerivation::seal(executor, quantifier, &values, instance, asserted)
        else {
            continue;
        };
        let Some((key, derivation)) = token.into_current(executor) else {
            continue;
        };
        instance_map.insert(key, derivation);
    }
    let mut skolem_map = HashMap::default();
    let records = executor.skolem_instance_records.clone();
    for record in records.into_iter().take(MAX_SEALED_DERIVATIONS) {
        if skolem_map.contains_key(&record.asserted) {
            continue;
        }
        let Some(token) = CheckedSkolemDerivation::seal(executor, &record) else {
            continue;
        };
        let Some(derivation) = token.into_current(executor) else {
            continue;
        };
        skolem_map.insert(record.asserted, derivation);
    }
    (instance_map, skolem_map)
}
