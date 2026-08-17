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
    step: ProofId,
    witness: TermId,
    check: WitnessAuthorityCheck<'_>,
) -> Result<(), ProofCheckError> {
    let TermData::Var(witness_name, _) = terms.get(witness) else {
        return Err(invalid(step, "witness must be an atomic fresh constant"));
    };
    if matches!(check.authority, SkolemWitnessAuthority::TermStoreRegistry)
        && !terms.is_skolem_symbol(witness_name)
    {
        return Err(invalid(
            step,
            "witness is not registered as a Skolem symbol",
        ));
    }
    if check.source_is_exists {
        if !matches!(check.authority, SkolemWitnessAuthority::TermStoreRegistry) {
            return Err(invalid(
                step,
                "sko_ex requires the live Skolem-registry authority",
            ));
        }
        let Some(choice) = terms.skolem_choice(witness) else {
            return Err(invalid(
                step,
                "sko_ex witness has no registered choice definition",
            ));
        };
        if choice.binder != check.binder
            || &choice.sort != check.binder_sort
            || choice.body != check.body
        {
            return Err(invalid(
                step,
                "registered choice does not match the existential source",
            ));
        }
    }
    if terms.sort(witness) != check.binder_sort {
        return Err(invalid(
            step,
            "witness sort does not match the forall binding",
        ));
    }
    Ok(())
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
    step: ProofId,
    check: FreshSubstitutionCheck<'_>,
    work: &mut usize,
) -> Result<(), ProofCheckError> {
    match term_contains(terms, check.quantified, check.witness, work) {
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
    if terms.sort(check.instance) != &Sort::Bool {
        return Err(invalid(step, "instantiated body must be Boolean"));
    }
    match matches_single_substitution(
        terms,
        check.body,
        check.instance,
        check.binder,
        check.witness,
        work,
    ) {
        Some(true) => Ok(()),
        Some(false) => Err(invalid(
            step,
            "right side is not the exact registered-witness substitution",
        )),
        None => Err(invalid(
            step,
            format!(
                "registered-witness substitution check exceeds {SKOLEM_TERM_WORK_LIMIT} distinct term pairs"
            ),
        )),
    }
}
