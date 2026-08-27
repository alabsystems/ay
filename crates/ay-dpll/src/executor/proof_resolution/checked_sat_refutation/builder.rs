// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordered construction stages for CheckedSatRefutation.

use ay_core::kani_compat::DetHashSet as HashSet;

use super::derivation_evidence::{
    sealed_context_derivations, sealed_fragment_derivation_maps, sealed_instance_root_derivations,
    sealed_propagation_environment,
};
use super::*;
use crate::sat_proof_manager::{
    FragmentContextDerivation, FragmentInstanceDerivation, FragmentInstanceRootDerivation,
    FragmentPropagationEnvironment, FragmentSkolemDerivation,
};

struct SealedAuthority {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    instance_derivations: HashMap<TermId, FragmentInstanceDerivation>,
    skolem_derivations: HashMap<TermId, FragmentSkolemDerivation>,
    propagation_environment: FragmentPropagationEnvironment,
    instance_root_derivations: Vec<FragmentInstanceRootDerivation>,
    context_derivations: HashMap<Vec<TermId>, FragmentContextDerivation>,
}

struct ReplayValidation {
    meter: CheckedRefutationMeter,
    assumption_sat_literals: Vec<Literal>,
    validated: ValidatedPremisedClauseTraceResolution,
}

struct AuthoredTerms {
    ordered_roots: Vec<TermId>,
    ordered_assumptions: Vec<TermId>,
    combined: Vec<TermId>,
}

struct StrictContext {
    datatype_decls: Vec<(String, Vec<String>)>,
    selector_decls: Vec<(String, Vec<String>)>,
    member_signatures: Vec<ay_proof::DatatypeMemberSignature>,
}

fn seal_authority(executor: &mut Executor) -> Result<SealedAuthority, CheckedSatRefutationError> {
    // Seal producer-recorded quantifier derivations FIRST: sealing may intern
    // terms, so it must precede every retained borrow of the proof bundle.
    let (instance_derivations, skolem_derivations) = sealed_fragment_derivation_maps(executor);
    let propagation_environment = sealed_propagation_environment(executor);
    let instance_root_derivations = sealed_instance_root_derivations(executor);
    let context_derivations = sealed_context_derivations(executor);
    let (query_epoch, source_context_stamp) = executor
        .checked_sat_refutation_query_scope()
        .ok_or_else(|| {
            if ay_core::misc_cli_flags().debug_cert {
                eprintln!("CERT/seal decline: scope accessor None");
            }
            CheckedSatRefutationError::UnsupportedQueryScope
        })?;
    let bound_assumptions = executor
        .checked_sat_refutation_query_assumptions()
        .ok_or_else(|| {
            if ay_core::misc_cli_flags().debug_cert {
                eprintln!("CERT/seal decline: assumptions accessor None");
            }
            CheckedSatRefutationError::UnsupportedQueryScope
        })?;
    let solver_assumptions_match = executor.last_assumptions.as_deref() == Some(bound_assumptions)
        || (bound_assumptions.is_empty() && executor.last_assumptions.is_none());
    if !solver_assumptions_match {
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!(
                "CERT/seal decline: solver assumptions mismatch: last={:?} bound={:?}",
                executor.last_assumptions.as_deref().map(<[TermId]>::len),
                bound_assumptions.len(),
            );
        }
        return Err(CheckedSatRefutationError::UnsupportedQueryScope);
    }
    Ok(SealedAuthority {
        query_epoch,
        source_context_stamp,
        instance_derivations,
        skolem_derivations,
        propagation_environment,
        instance_root_derivations,
        context_derivations,
    })
}

fn replay_trace(executor: &Executor) -> Result<ReplayValidation, CheckedSatRefutationError> {
    let bound_assumptions = executor
        .checked_sat_refutation_query_assumptions()
        .ok_or(CheckedSatRefutationError::UnsupportedQueryScope)?;

    // Snapshot controls before borrowing the retained trace. The replay and
    // every later stage resume this one aggregate meter.
    let limits = validation_limits(executor);
    let interrupt = executor.solve_interrupt.clone();
    let memory_limit = executor.memory_limit();
    let conversion_interrupt = interrupt.clone();
    let mut should_stop = move || {
        conversion_interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
            || crate::memory::memory_exceeded(memory_limit)
            || ay_sys::process_memory_exceeded()
    };

    let trace = executor
        .last_clause_trace
        .as_ref()
        .ok_or(CheckedSatRefutationError::MissingClauseTrace)?;
    let sat_num_vars = trace
        .solver_num_vars()
        .ok_or(CheckedSatRefutationError::MissingSatVariableNamespace)?;
    let var_to_term = executor
        .last_var_to_term
        .as_ref()
        .ok_or(CheckedSatRefutationError::MissingVariableMap)?;

    let mut meter = CheckedRefutationMeter::new(limits, interrupt, memory_limit)?;
    let assumption_sat_literals = exact_assumption_sat_literals(
        bound_assumptions,
        var_to_term,
        &executor.ctx.terms,
        sat_num_vars,
        &mut meter,
    )?;
    let scope_assumptions = trace
        .scope_assumptions()
        .ok_or(CheckedSatRefutationError::MissingScopeAuthority)?;
    validate_scope_assumptions(scope_assumptions, var_to_term, sat_num_vars, &mut meter)?;
    let structural_premises =
        metered_literal_concat(scope_assumptions, &assumption_sat_literals, &mut meter)?;
    let remaining_limits = meter.remaining_validation_limits()?;
    let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
        trace,
        sat_num_vars,
        structural_premises.as_slice(),
        &remaining_limits,
        &mut should_stop,
    )?;
    meter.absorb_validation(&validated)?;
    meter.charge(validated.unit_premises().len(), 0)?;
    if validated.unit_premises() != structural_premises {
        return Err(CheckedSatRefutationError::ValidatedAssumptionPremiseMismatch);
    }
    Ok(ReplayValidation {
        meter,
        assumption_sat_literals,
        validated,
    })
}

fn copy_authored_terms(
    executor: &Executor,
    meter: &mut CheckedRefutationMeter,
) -> Result<AuthoredTerms, CheckedSatRefutationError> {
    let ordered_roots = {
        let roots = executor
            .checked_sat_refutation_query_roots()
            .ok_or(CheckedSatRefutationError::UnsupportedQueryScope)?;
        metered_term_id_copy(roots, meter)?
    };
    let ordered_assumptions = {
        let assumptions = executor
            .checked_sat_refutation_query_assumptions()
            .ok_or(CheckedSatRefutationError::UnsupportedQueryScope)?;
        metered_term_id_copy(assumptions, meter)?
    };
    let combined = metered_term_id_concat(&ordered_roots, &ordered_assumptions, meter)?;
    let provenance = executor
        .proof_problem_assertion_provenance
        .as_ref()
        .ok_or(CheckedSatRefutationError::MissingAuthoredProvenance)?;
    meter.charge(ordered_roots.len(), 0)?;
    if provenance.original_problem_assertions != ordered_roots {
        return Err(CheckedSatRefutationError::AuthoredRootMismatch);
    }
    Ok(AuthoredTerms {
        ordered_roots,
        ordered_assumptions,
        combined,
    })
}

fn prepare_strict_context(
    executor: &Executor,
    meter: &mut CheckedRefutationMeter,
) -> Result<StrictContext, CheckedSatRefutationError> {
    let datatype_decls = metered_datatype_decls(executor, meter)?;
    let selector_decls = metered_selector_decls(executor, meter)?;
    let member_signatures = executor
        .datatype_member_signatures_for_strict_proof()
        .ok_or_else(
            || ay_proof::ProofCheckError::InvalidDatatypeSignatureContext {
                reason: "executor datatype registries lack an exact sticky member signature"
                    .to_string(),
            },
        )?;
    Ok(StrictContext {
        datatype_decls,
        selector_decls,
        member_signatures,
    })
}

/// The stable trace ids of every ORIGINAL clause in the empty-clause
/// hint-closure of the validated DAG (#cone-scoped-authority).
///
/// Walks derived rows' RUP hints transitively from the terminal empty clause.
/// Only cone originals are premises of the published refutation, so only they
/// need semantic authentication. Any structural inconsistency (an id outside
/// both namespaces, a derived index mismatch, a canonical id without a trace
/// mapping) returns `None`, which keeps the historical EXHAUSTIVE
/// authentication — strictly fail-closed.
fn original_cone_trace_ids(
    validated: &ValidatedPremisedClauseTraceResolution,
    meter: &mut CheckedRefutationMeter,
) -> Result<Option<HashSet<u64>>, CheckedSatRefutationError> {
    let dag = validated.dag();
    let originals_len = dag.original_clauses.len() as u64;
    let mut visited: HashSet<u64> = HashSet::default();
    let mut cone_original_canonicals: HashSet<u64> = HashSet::default();
    let mut stack: Vec<u64> = vec![dag.empty_clause_id];
    while let Some(id) = stack.pop() {
        meter.charge(1, 0)?;
        if !visited.insert(id) {
            continue;
        }
        if id == 0 {
            return Ok(None);
        }
        if id <= originals_len {
            cone_original_canonicals.insert(id);
            continue;
        }
        let Ok(derived_index) = usize::try_from(id - originals_len - 1) else {
            return Ok(None);
        };
        let Some(step) = dag.derived.get(derived_index) else {
            return Ok(None);
        };
        if step.id != id {
            return Ok(None);
        }
        meter.charge(step.rup_hints.len(), 0)?;
        stack.extend(step.rup_hints.iter().copied());
    }
    let mappings = validated.original_mappings();
    meter.charge(
        mappings.len(),
        checked_resource_mul(
            cone_original_canonicals.len(),
            size_of::<u64>() * 2,
            ResolutionValidationResource::Bytes,
        )?,
    )?;
    let mut cone_trace_ids: HashSet<u64> = HashSet::default();
    for mapping in mappings {
        if cone_original_canonicals.contains(&mapping.canonical_id()) {
            cone_trace_ids.insert(mapping.trace_id());
        }
    }
    if cone_trace_ids.len() != cone_original_canonicals.len() {
        // A cone member without a trace mapping (or a duplicated trace id):
        // fall back to exhaustive authentication.
        return Ok(None);
    }
    Ok(Some(cone_trace_ids))
}

fn build_fragment(
    executor: &mut Executor,
    authority: &SealedAuthority,
    authored: &AuthoredTerms,
    original_id_cone: Option<&HashSet<u64>>,
    meter: &mut CheckedRefutationMeter,
) -> Result<ExactOriginalProofFragment, CheckedSatRefutationError> {
    let trace = executor
        .last_clause_trace
        .as_ref()
        .ok_or(CheckedSatRefutationError::MissingClauseTrace)?;
    let var_to_term = executor
        .last_var_to_term
        .as_ref()
        .ok_or(CheckedSatRefutationError::MissingVariableMap)?;
    let scope_assumptions = trace
        .scope_assumptions()
        .ok_or(CheckedSatRefutationError::MissingScopeAuthority)?;
    let clausification_proofs = executor.last_clausification_proofs.as_deref();
    let theory_proofs = executor.last_original_clause_theory_proofs.as_deref();
    // #dt-ground-conflict: registries for the pedigree-free DT lane, built
    // BEFORE the manager takes the mutable term-store borrow. `None` on
    // datatype-free problems — the lane is then skipped entirely.
    let dt_registry = crate::theory_inference::dt_funnel_registry_data(&executor.ctx);

    let mut manager = SatProofManager::new(var_to_term, &mut executor.ctx.terms);
    manager.set_dt_registry_data(dt_registry.as_ref());
    manager.set_scope_assumptions(scope_assumptions)?;
    if let Some(proofs) = clausification_proofs {
        manager.set_clausification_proofs(proofs);
    }
    if let Some(proofs) = theory_proofs {
        manager.set_original_clause_theory_proofs(proofs);
    }
    if !authority.instance_derivations.is_empty() {
        manager.set_instance_derivations(&authority.instance_derivations);
    }
    if !authority.skolem_derivations.is_empty() {
        manager.set_skolem_derivations(&authority.skolem_derivations);
    }
    if !authority.propagation_environment.is_empty() {
        manager.set_propagation_environment(&authority.propagation_environment);
    }
    if !authority.instance_root_derivations.is_empty() {
        manager.set_instance_root_derivations(&authority.instance_root_derivations);
    }
    if !authority.context_derivations.is_empty() {
        manager.set_context_derivations(&authority.context_derivations);
    }
    Ok(
        manager.build_exact_original_proof_fragment_metered_with_diagnostic(
            trace,
            &authored.combined,
            original_id_cone,
            &mut |work, bytes| meter.charge(work, bytes),
            &mut |message| crate::executor::probe_cert_reject_raw(|| message),
        )?,
    )
}

fn authenticate_and_compose(
    executor: &mut Executor,
    fragment: &ExactOriginalProofFragment,
    replay: &mut ReplayValidation,
    authored: &AuthoredTerms,
    strict: &StrictContext,
    original_id_cone: Option<&HashSet<u64>>,
) -> Result<(), CheckedSatRefutationError> {
    let authentication_bytes = strict_authentication_bytes(fragment.proof(), &mut replay.meter)?;
    replay
        .meter
        .charge(fragment.proof().steps.len(), authentication_bytes)?;
    let mut authentication_resource_error = None;
    let authenticated =
        ay_proof::authenticate_premise_clauses_with_deferred_generic_theory_and_typed_context_and_progress(
            fragment.proof(),
            &executor.ctx.terms,
            (!strict.datatype_decls.is_empty()).then_some(strict.datatype_decls.as_slice()),
            (!strict.selector_decls.is_empty()).then_some(strict.selector_decls.as_slice()),
            strict.member_signatures.as_slice(),
            &authored.combined,
            &mut |work, bytes| match replay.meter.charge(work, bytes) {
                Ok(()) => true,
                Err(error) => {
                    authentication_resource_error = Some(error);
                    false
                }
            },
        );
    if let Some(error) = authentication_resource_error {
        return Err(error.into());
    }
    let authenticated = SemanticallyCompletedPremiseClauses::complete(
        authenticated?,
        &executor.conflict_semantic_verify_memo,
        &executor.ctx.terms,
        &mut replay.meter,
    )?;
    replay.meter.charge(0, 0)?;

    let var_to_term = executor
        .last_var_to_term
        .as_ref()
        .ok_or(CheckedSatRefutationError::MissingVariableMap)?;
    let scope_assumptions = executor
        .last_clause_trace
        .as_ref()
        .ok_or(CheckedSatRefutationError::MissingClauseTrace)?
        .scope_assumptions()
        .ok_or(CheckedSatRefutationError::MissingScopeAuthority)?;
    verify_exact_composition(
        &replay.validated,
        fragment,
        &authenticated,
        original_id_cone,
        var_to_term,
        scope_assumptions,
        &mut executor.ctx.terms,
        &mut replay.meter,
    )?;
    authenticate_assumption_unit_premises(
        &authored.ordered_assumptions,
        &replay.assumption_sat_literals,
        &authored.combined,
        var_to_term,
        &mut executor.ctx.terms,
        &strict.datatype_decls,
        &strict.selector_decls,
        &strict.member_signatures,
        &mut replay.meter,
    )
}

fn finish_capability(
    authority: SealedAuthority,
    authored: AuthoredTerms,
    replay: &mut ReplayValidation,
) -> Result<CheckedSatRefutation, CheckedSatRefutationError> {
    let boxed_root_bytes = checked_resource_mul(
        authored.ordered_roots.len(),
        size_of::<TermId>(),
        ResolutionValidationResource::Bytes,
    )?;
    replay
        .meter
        .charge(authored.ordered_roots.len(), boxed_root_bytes)?;
    let ordered_authored_roots = authored.ordered_roots.into_boxed_slice();
    let boxed_assumption_bytes = checked_resource_mul(
        authored.ordered_assumptions.len(),
        size_of::<TermId>(),
        ResolutionValidationResource::Bytes,
    )?;
    replay
        .meter
        .charge(authored.ordered_assumptions.len(), boxed_assumption_bytes)?;
    let ordered_assumptions = authored.ordered_assumptions.into_boxed_slice();
    replay.meter.charge(0, 0)?;
    let original_clause_count = checked_resource_add(
        replay.validated.original_mappings().len(),
        ordered_assumptions.len(),
        ResolutionValidationResource::OriginalClauses,
    )?;
    Ok(CheckedSatRefutation {
        query_epoch: authority.query_epoch,
        source_context_stamp: authority.source_context_stamp,
        ordered_authored_roots,
        ordered_assumptions,
        original_clause_count,
        derived_step_count: replay.validated.dag().derived.len(),
    })
}

pub(super) fn build(
    executor: &mut Executor,
) -> Result<CheckedSatRefutation, CheckedSatRefutationError> {
    let phase_clock = ay_core::time::Instant::now();
    let phase = |label: &str| {
        if ay_core::misc_cli_flags().probe_cert_reject {
            ay_core::safe_eprintln!(
                "--probe-cert-reject: build phase {label} at {:?}",
                phase_clock.elapsed()
            );
        }
    };
    let authority = seal_authority(executor)?;
    phase("sealed");
    let mut replay = replay_trace(executor)?;
    phase("replayed");
    let authored = copy_authored_terms(executor, &mut replay.meter)?;
    let strict = prepare_strict_context(executor, &mut replay.meter)?;
    let original_id_cone = original_cone_trace_ids(&replay.validated, &mut replay.meter)?;
    phase("cone");
    let fragment = build_fragment(
        executor,
        &authority,
        &authored,
        original_id_cone.as_ref(),
        &mut replay.meter,
    )?;
    phase("fragment");
    authenticate_and_compose(
        executor,
        &fragment,
        &mut replay,
        &authored,
        &strict,
        original_id_cone.as_ref(),
    )?;
    finish_capability(authority, authored, &mut replay)
}
