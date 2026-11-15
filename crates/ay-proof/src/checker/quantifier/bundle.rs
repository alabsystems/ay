// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-proof Skolem freshness, uniqueness, and dependency authentication.

use super::*;

mod collection;
mod dependencies;
mod meter;
mod registry;
mod walk;

use collection::collect_skolem_bindings;
use dependencies::validate_acyclic_dependencies;
use registry::{build_bundle_registry, validate_global_name_freshness};
use walk::validate_problem_freshness;

struct SkolemBinding {
    step: ProofId,
    source: TermId,
    witness: TermId,
    name: String,
}

struct BundleRegistry<'a> {
    by_name: HashMap<String, TermId>,
    binding_by_witness: HashMap<TermId, &'a SkolemBinding>,
    fallback_step: ProofId,
}

/// Compatibility wrapper for the whole-proof partial-bijection check.
pub(crate) fn validate_sko_forall_uniqueness(
    proof: &Proof,
    terms: &TermStore,
) -> Result<(), ProofCheckError> {
    validate_sko_forall_uniqueness_with_progress(proof, terms, &mut |_, _| true)
}

/// Revalidate every live Skolem step and enforce exact source/witness
/// uniqueness under one caller work/byte/cancellation envelope.
///
/// The substitution walk retains its proof-wide 100k local limit. Duplicate
/// proof roots and edges still cost caller work, and each owning registry and
/// queue is bounded before allocation. Refusal never authenticates a prefix.
pub(crate) fn validate_sko_forall_uniqueness_with_progress(
    proof: &Proof,
    terms: &TermStore,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    poll(progress)?;
    let _ = collect_skolem_bindings(
        proof,
        terms,
        SkolemWitnessAuthority::TermStoreRegistry,
        progress,
    )?;
    poll(progress)
}

/// Compatibility wrapper for content-authenticated offline Skolem authority.
#[cfg(test)]
pub(crate) fn authenticate_bundle_skolems(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    declaration_term_symbols: &HashMap<String, &'static str>,
) -> Result<Vec<String>, ProofCheckError> {
    authenticate_bundle_skolems_with_progress(
        proof,
        terms,
        problem_assertions,
        declaration_term_symbols,
        &mut |_, _| true,
    )
}

/// Authenticate the exact choice definitions before returning any names that
/// a caller may restore to a checker-only store.
///
/// No producer ledger is trusted: exact substitution, a partial bijection,
/// the complete (including unused) term namespace, serialized declarations,
/// authored assumptions, and an acyclic dependency graph all remain required.
/// Each phase shares the caller callback. The existing local distinct-term
/// limits remain phase-local; queue/registry and total dependency-edge caps
/// additionally prevent duplicate fan-out from bypassing the 100k envelope.
/// This API does not mutate the store or restore authority itself.
pub(crate) fn authenticate_bundle_skolems_with_progress(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    declaration_term_symbols: &HashMap<String, &'static str>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Vec<String>, ProofCheckError> {
    poll(progress)?;
    let bindings =
        collect_skolem_bindings(proof, terms, SkolemWitnessAuthority::ProofBundle, progress)?;
    if bindings.is_empty() {
        poll(progress)?;
        return Ok(Vec::new());
    }
    let mut registry_work = 0usize;
    let registry = {
        let mut meter =
            QuantifierMeter::new(ProofId(0), "sko_forall", &mut registry_work, progress);
        let registry = build_bundle_registry(&bindings, declaration_term_symbols, &mut meter)?;
        validate_global_name_freshness(terms, &registry, &mut meter)?;
        registry
    };
    let mut problem_work = 0usize;
    validate_problem_freshness(
        proof,
        terms,
        problem_assertions,
        &registry,
        &mut QuantifierMeter::new(
            registry.fallback_step,
            "sko_forall",
            &mut problem_work,
            progress,
        ),
    )?;
    let mut dependency_work = 0usize;
    validate_acyclic_dependencies(
        terms,
        &bindings,
        &registry,
        &mut QuantifierMeter::new(
            registry.fallback_step,
            "sko_forall",
            &mut dependency_work,
            progress,
        ),
    )?;
    drop(registry);
    let mut names = Vec::new();
    let mut output_work = 0usize;
    let mut meter = QuantifierMeter::new(ProofId(0), "sko_forall", &mut output_work, progress);
    for binding in bindings {
        // Move authenticated String ownership; do not clone names a third time.
        meter.push(&mut names, binding.name)?;
    }
    meter.charge(0, 0)?;
    Ok(names)
}

fn poll(progress: &mut dyn FnMut(usize, usize) -> bool) -> Result<(), ProofCheckError> {
    if progress(0, 0) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

#[cfg(test)]
mod tests;
