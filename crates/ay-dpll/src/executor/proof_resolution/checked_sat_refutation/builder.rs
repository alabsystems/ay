// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordered construction stages for CheckedSatRefutation.

use super::*;
use crate::sat_proof_manager::{
    FragmentInstanceDerivation, FragmentInstanceRootDerivation, FragmentPropagationEnvironment,
    FragmentSkolemDerivation,
};

struct SealedAuthority {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    instance_derivations: HashMap<TermId, FragmentInstanceDerivation>,
    skolem_derivations: HashMap<TermId, FragmentSkolemDerivation>,
    propagation_environment: FragmentPropagationEnvironment,
    instance_root_derivations: Vec<FragmentInstanceRootDerivation>,
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
    let (query_epoch, source_context_stamp) = executor
        .checked_sat_refutation_query_scope()
        .ok_or(CheckedSatRefutationError::UnsupportedQueryScope)?;
    let bound_assumptions = executor
        .checked_sat_refutation_query_assumptions()
        .ok_or(CheckedSatRefutationError::UnsupportedQueryScope)?;
    let solver_assumptions_match = executor.last_assumptions.as_deref() == Some(bound_assumptions)
        || (bound_assumptions.is_empty() && executor.last_assumptions.is_none());
    if !solver_assumptions_match {
        return Err(CheckedSatRefutationError::UnsupportedQueryScope);
    }
    Ok(SealedAuthority {
        query_epoch,
        source_context_stamp,
        instance_derivations,
        skolem_derivations,
        propagation_environment,
        instance_root_derivations,
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

fn build_fragment(
    executor: &mut Executor,
    authority: &SealedAuthority,
    authored: &AuthoredTerms,
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

    let mut manager = SatProofManager::new(var_to_term, &mut executor.ctx.terms);
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
    Ok(manager.build_exact_original_proof_fragment_metered(
        trace,
        &authored.combined,
        &mut |work, bytes| meter.charge(work, bytes),
    )?)
}

fn authenticate_and_compose(
    executor: &mut Executor,
    fragment: &ExactOriginalProofFragment,
    replay: &mut ReplayValidation,
    authored: &AuthoredTerms,
    strict: &StrictContext,
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
    let authority = seal_authority(executor)?;
    let mut replay = replay_trace(executor)?;
    let authored = copy_authored_terms(executor, &mut replay.meter)?;
    let strict = prepare_strict_context(executor, &mut replay.meter)?;
    let fragment = build_fragment(executor, &authority, &authored, &mut replay.meter)?;
    authenticate_and_compose(executor, &fragment, &mut replay, &authored, &strict)?;
    finish_capability(authority, authored, &mut replay)
}
