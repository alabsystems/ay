// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authority and freshness checks for flat Skolem proof steps.

use super::*;

pub(super) struct WitnessAuthorityCheck<'a> {
    pub(super) binder: &'a str,
    pub(super) binder_sort: &'a Sort,
    pub(super) body: TermId,
    pub(super) source_is_exists: bool,
    pub(super) authority: SkolemWitnessAuthority,
}

pub(super) fn validate_witness_authority(
    terms: &TermStore,
    _step: ProofId,
    witness: TermId,
    check: WitnessAuthorityCheck<'_>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    let TermData::Var(witness_name, _) = meter.term(terms, witness)? else {
        return Err(meter.invalid("witness must be an atomic fresh constant")?);
    };
    if matches!(check.authority, SkolemWitnessAuthority::TermStoreRegistry) {
        meter.lookup(witness_name, registry_cardinality_bound(terms)?)?;
        if !terms.is_skolem_symbol(witness_name) {
            return Err(meter.invalid("witness is not registered as a Skolem symbol")?);
        }
    }
    if check.source_is_exists {
        if !matches!(check.authority, SkolemWitnessAuthority::TermStoreRegistry) {
            return Err(meter.invalid("sko_ex requires the live Skolem-registry authority")?);
        }
        meter.lookup("", registry_cardinality_bound(terms)?)?;
        let Some(choice) = terms.skolem_choice(witness) else {
            return Err(meter.invalid("sko_ex witness has no registered choice definition")?);
        };
        meter.name(&choice.binder)?;
        meter.name(check.binder)?;
        if choice.binder != check.binder
            || !meter.sort_equal(&choice.sort, check.binder_sort)?
            || choice.body != check.body
        {
            return Err(meter.invalid("registered choice does not match the existential source")?);
        }
    }
    let witness_sort = meter.sort(terms, witness)?;
    if !meter.sort_equal(witness_sort, check.binder_sort)? {
        return Err(meter.invalid("witness sort does not match the forall binding")?);
    }
    Ok(())
}

fn registry_cardinality_bound(terms: &TermStore) -> Result<usize, ProofCheckError> {
    // Both registries start empty. Every fresh key bumps this non-wrapping
    // counter; Clone copies it with the registries, and rollback/compaction
    // only prune/remap keys. Thus each completed store API state has registry
    // cardinality <= generation, even for ghost names absent from the arena.
    // Other metadata changes only make this read-only upper bound looser.
    usize::try_from(terms.checker_visible_metadata_generation())
        .map_err(|_| ProofCheckError::ResourceLimit)
}

pub(super) struct FreshSubstitutionCheck<'a> {
    pub(super) quantified: TermId,
    pub(super) body: TermId,
    pub(super) instance: TermId,
    pub(super) binder: &'a str,
    pub(super) witness: TermId,
}

pub(super) fn validate_fresh_substitution(
    terms: &TermStore,
    _step: ProofId,
    check: FreshSubstitutionCheck<'_>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    if scans::term_contains(terms, check.quantified, check.witness, meter)? {
        return Err(meter.invalid("fresh witness occurs in the quantified source")?);
    }
    let instance_sort = meter.sort(terms, check.instance)?;
    if !meter.sort_equal(instance_sort, &Sort::Bool)? {
        return Err(meter.invalid("instantiated body must be Boolean")?);
    }
    if !matches_single_substitution(
        terms,
        check.body,
        check.instance,
        check.binder,
        check.witness,
        meter,
    )? {
        return Err(meter.invalid("right side is not the exact registered-witness substitution")?);
    }
    Ok(())
}
