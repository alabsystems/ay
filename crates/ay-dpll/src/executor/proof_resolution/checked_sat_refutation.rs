// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed composition of SMT premise authority with a checked SAT refutation.
//!
//! The SAT trace is an untrusted candidate. This module accepts it only when:
//!
//! * its exact solver-reported variable namespace is available;
//! * a finite-budget positive-RUP replay derives the empty clause under the
//!   exact bound assumptions as fixed unit premises;
//! * every structural original maps by stable trace ID, trace position, and
//!   byte-for-byte SAT literals to a proof step built from that same trace;
//! * the strict proof checker authenticates the exact SMT clause at every such
//!   proof-step identity against the frozen authored query roots, with each
//!   `Generic` theory premise separately matched to an exact positive verdict
//!   retained by this query's semantic-conflict verifier; and
//! * the resulting capability remains bound to the same public query epoch,
//!   frontend source stamp, ordered roots, and ordered assumption slice.
//!
//! No producer verdict, `is_original` bit, content-only lookup, or later proof
//! surgery participates in this authority.

mod builder;
mod derivation_evidence;
mod metering;

use metering::*;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Proof, ProofId, ProofStep, TermData, TermId, TermStore, TheoryLit};
use ay_frontend::SourceContextStamp;
use ay_proof::PremiseClausesWithDeferredGeneric;
#[cfg(test)]
use ay_sat::validate_clause_trace_resolution;
use ay_sat::{
    validate_clause_trace_resolution_with_unit_premises_interruptible, ClauseTraceOriginalMapping,
    ClauseTraceResolutionError, Literal, ResolutionDag, ResolutionValidationError,
    ResolutionValidationLimits, ResolutionValidationResource, ValidatedClauseTraceResolution,
    ValidatedPremisedClauseTraceResolution, Variable,
};
use std::mem::size_of;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use crate::executor::{Executor, QueryAuthorityEpoch};
use crate::sat_proof_manager::{
    ExactOriginalProofError, ExactOriginalProofFragment, SatProofManager,
};
use crate::verification::ConflictSemanticVerifyMemo;
#[cfg(test)]
use derivation_evidence::{CheckedInstanceDerivation, CheckedSkolemDerivation};

fn checked_resource_add(
    lhs: usize,
    rhs: usize,
    resource: ResolutionValidationResource,
) -> Result<usize, ResolutionValidationError> {
    lhs.checked_add(rhs)
        .ok_or(ResolutionValidationError::AccountingOverflow { resource })
}

fn checked_resource_mul(
    lhs: usize,
    rhs: usize,
    resource: ResolutionValidationResource,
) -> Result<usize, ResolutionValidationError> {
    lhs.checked_mul(rhs)
        .ok_or(ResolutionValidationError::AccountingOverflow { resource })
}

fn charge_capacity_excess<T>(
    capacity: usize,
    requested: usize,
    meter: &mut CheckedRefutationMeter,
) -> Result<(), ResolutionValidationError> {
    let excess =
        capacity
            .checked_sub(requested)
            .ok_or(ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Bytes,
            })?;
    meter.charge(
        0,
        checked_resource_mul(excess, size_of::<T>(), ResolutionValidationResource::Bytes)?,
    )
}

fn metered_term_id_copy(
    source: &[TermId],
    meter: &mut CheckedRefutationMeter,
) -> Result<Vec<TermId>, ResolutionValidationError> {
    let bytes = checked_resource_mul(
        source.len(),
        size_of::<TermId>(),
        ResolutionValidationResource::Bytes,
    )?;
    meter.charge(source.len(), bytes)?;

    let mut copy = Vec::new();
    copy.try_reserve_exact(source.len()).map_err(|_| {
        ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::Bytes,
        }
    })?;
    charge_capacity_excess::<TermId>(copy.capacity(), source.len(), meter)?;
    for chunk in source.chunks(1024) {
        meter.charge(0, 0)?;
        copy.extend_from_slice(chunk);
    }
    meter.charge(0, 0)?;
    Ok(copy)
}

fn metered_term_id_concat(
    left: &[TermId],
    right: &[TermId],
    meter: &mut CheckedRefutationMeter,
) -> Result<Vec<TermId>, ResolutionValidationError> {
    let len = checked_resource_add(left.len(), right.len(), ResolutionValidationResource::Work)?;
    let bytes = checked_resource_mul(
        len,
        size_of::<TermId>(),
        ResolutionValidationResource::Bytes,
    )?;
    meter.charge(len, bytes)?;
    let mut combined = Vec::new();
    combined
        .try_reserve_exact(len)
        .map_err(|_| ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::Bytes,
        })?;
    charge_capacity_excess::<TermId>(combined.capacity(), len, meter)?;
    for chunk in left.chunks(1024).chain(right.chunks(1024)) {
        meter.charge(0, 0)?;
        combined.extend_from_slice(chunk);
    }
    meter.charge(0, 0)?;
    Ok(combined)
}

fn metered_literal_concat(
    left: &[Literal],
    right: &[Literal],
    meter: &mut CheckedRefutationMeter,
) -> Result<Vec<Literal>, ResolutionValidationError> {
    let len = checked_resource_add(left.len(), right.len(), ResolutionValidationResource::Work)?;
    let bytes = checked_resource_mul(
        len,
        size_of::<Literal>(),
        ResolutionValidationResource::Bytes,
    )?;
    meter.charge(len, bytes)?;
    let mut combined = Vec::new();
    combined
        .try_reserve_exact(len)
        .map_err(|_| ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::Bytes,
        })?;
    charge_capacity_excess::<Literal>(combined.capacity(), len, meter)?;
    combined.extend_from_slice(left);
    combined.extend_from_slice(right);
    meter.charge(0, 0)?;
    Ok(combined)
}

fn validate_scope_assumptions(
    assumptions: &[Literal],
    var_to_term: &HashMap<u32, TermId>,
    sat_num_vars: usize,
    meter: &mut CheckedRefutationMeter,
) -> Result<(), CheckedSatRefutationError> {
    meter.charge(assumptions.len(), 0)?;
    let mut previous = None;
    for (premise_index, &premise) in assumptions.iter().enumerate() {
        let variable = premise.variable().index() as u32;
        if premise.is_positive() {
            return Err(CheckedSatRefutationError::PositiveScopePremise {
                premise_index,
                variable,
            });
        }
        if variable as usize >= sat_num_vars {
            return Err(CheckedSatRefutationError::StructuralTrace(
                ClauseTraceResolutionError::UnitPremiseVariableOutOfRange {
                    premise_index,
                    variable: variable as usize,
                    num_vars: sat_num_vars,
                },
            ));
        }
        if var_to_term.contains_key(&variable) {
            return Err(CheckedSatRefutationError::MappedScopePremise { variable });
        }
        if let Some(prior) = previous {
            if variable == prior {
                return Err(CheckedSatRefutationError::DuplicateScopePremise { variable });
            }
            if variable < prior {
                return Err(CheckedSatRefutationError::UnorderedScopePremise {
                    premise_index,
                    previous: prior,
                    variable,
                });
            }
        }
        previous = Some(variable);
    }
    meter.charge(0, 0)?;
    Ok(())
}

/// Reconstruct the exact SAT literal used for each authored assumption.
///
/// The producing path intentionally retains no term-to-variable map, so this
/// scans the authoritative inverse map and accepts only one unambiguous exact
/// syntactic match. Rewritten/preprocessed assumptions therefore fail closed
/// until they carry their own checked equivalence evidence.
fn exact_assumption_sat_literals(
    assumptions: &[TermId],
    var_to_term: &HashMap<u32, TermId>,
    terms: &TermStore,
    sat_num_vars: usize,
    meter: &mut CheckedRefutationMeter,
) -> Result<Vec<Literal>, CheckedSatRefutationError> {
    let bytes = checked_resource_mul(
        assumptions.len(),
        size_of::<Literal>(),
        ResolutionValidationResource::Bytes,
    )?;
    meter.charge(assumptions.len(), bytes)?;
    let mut literals = Vec::new();
    literals.try_reserve_exact(assumptions.len()).map_err(|_| {
        ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::Bytes,
        }
    })?;
    charge_capacity_excess::<Literal>(literals.capacity(), assumptions.len(), meter)?;

    for (assumption_index, &assumption) in assumptions.iter().enumerate() {
        meter.charge(
            checked_resource_add(var_to_term.len(), 1, ResolutionValidationResource::Work)?,
            0,
        )?;
        if assumption.index() >= terms.len() {
            return Err(CheckedSatRefutationError::StaleAssumptionTerm {
                assumption_index,
                assumption,
            });
        }
        let assumption_negates = match terms.get(assumption) {
            TermData::Not(inner) => Some(*inner),
            _ => None,
        };
        let mut matched = None;
        for (&variable, &mapped) in var_to_term {
            if mapped.index() >= terms.len() {
                continue;
            }
            let polarity = if mapped == assumption {
                Some(true)
            } else if matches!(terms.get(mapped), TermData::Not(inner) if *inner == assumption)
                || assumption_negates == Some(mapped)
            {
                Some(false)
            } else {
                None
            };
            let Some(positive) = polarity else {
                continue;
            };
            let variable_index = variable as usize;
            if variable_index >= sat_num_vars || variable > i32::MAX as u32 {
                return Err(CheckedSatRefutationError::AssumptionVariableOutOfRange {
                    assumption_index,
                    variable,
                    sat_num_vars,
                });
            }
            let variable = Variable::new(variable);
            let literal = if positive {
                Literal::positive(variable)
            } else {
                Literal::negative(variable)
            };
            if matched.replace(literal).is_some() {
                return Err(CheckedSatRefutationError::AmbiguousAssumptionMapping {
                    assumption_index,
                    assumption,
                });
            }
        }
        let literal = matched.ok_or(CheckedSatRefutationError::UnmappedAssumption {
            assumption_index,
            assumption,
        })?;
        literals.push(literal);
        if assumption_index % 1024 == 0 {
            meter.charge(0, 0)?;
        }
    }
    meter.charge(0, 0)?;
    Ok(literals)
}

fn metered_string_copy(
    source: &str,
    meter: &mut CheckedRefutationMeter,
) -> Result<String, ResolutionValidationError> {
    meter.charge(source.len(), source.len())?;
    let mut copy = String::new();
    copy.try_reserve_exact(source.len()).map_err(|_| {
        ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::Bytes,
        }
    })?;
    meter.charge(
        0,
        copy.capacity().checked_sub(source.len()).ok_or(
            ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Bytes,
            },
        )?,
    )?;
    copy.push_str(source);
    meter.charge(0, 0)?;
    Ok(copy)
}

fn metered_datatype_decls(
    executor: &Executor,
    meter: &mut CheckedRefutationMeter,
) -> Result<Vec<(String, Vec<String>)>, ResolutionValidationError> {
    let mut declarations = Vec::new();
    for (name, constructors) in executor.ctx.datatype_iter() {
        // `try_reserve(1)` may grow geometrically and an empty Vec commonly
        // starts at four elements. Four outer slots per inserted declaration
        // conservatively cover both that minimum and later spare capacity.
        meter.charge(
            1,
            checked_resource_mul(
                4,
                size_of::<(String, Vec<String>)>(),
                ResolutionValidationResource::Bytes,
            )?,
        )?;
        declarations
            .try_reserve(1)
            .map_err(|_| ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::Bytes,
            })?;

        let name = metered_string_copy(name, meter)?;
        let constructor_headers = checked_resource_mul(
            constructors.len(),
            size_of::<String>(),
            ResolutionValidationResource::Bytes,
        )?;
        meter.charge(constructors.len(), constructor_headers)?;
        let mut copied_constructors = Vec::new();
        copied_constructors
            .try_reserve_exact(constructors.len())
            .map_err(|_| ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::Bytes,
            })?;
        charge_capacity_excess::<String>(
            copied_constructors.capacity(),
            constructors.len(),
            meter,
        )?;
        for constructor in constructors {
            copied_constructors.push(metered_string_copy(constructor, meter)?);
        }
        declarations.push((name, copied_constructors));
        meter.charge(0, 0)?;
    }
    Ok(declarations)
}

fn metered_selector_decls(
    executor: &Executor,
    meter: &mut CheckedRefutationMeter,
) -> Result<Vec<(String, Vec<String>)>, ResolutionValidationError> {
    let mut declarations = Vec::new();
    for (constructor, selectors) in executor.ctx.ctor_selectors_iter() {
        meter.charge(
            1,
            checked_resource_mul(
                4,
                size_of::<(String, Vec<String>)>(),
                ResolutionValidationResource::Bytes,
            )?,
        )?;
        declarations
            .try_reserve(1)
            .map_err(|_| ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::Bytes,
            })?;

        let constructor = metered_string_copy(constructor, meter)?;
        let selector_headers = checked_resource_mul(
            selectors.len(),
            size_of::<String>(),
            ResolutionValidationResource::Bytes,
        )?;
        meter.charge(selectors.len(), selector_headers)?;
        let mut copied_selectors = Vec::new();
        copied_selectors
            .try_reserve_exact(selectors.len())
            .map_err(|_| ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::Bytes,
            })?;
        charge_capacity_excess::<String>(copied_selectors.capacity(), selectors.len(), meter)?;
        for selector in selectors {
            copied_selectors.push(metered_string_copy(selector, meter)?);
        }
        declarations.push((constructor, copied_selectors));
        meter.charge(0, 0)?;
    }
    Ok(declarations)
}

/// Static scratch envelope for strict premise authentication.
///
/// The strict checker separately reports dynamic term/sort payload and every
/// expensive validation rule through its metered callback. This census covers
/// the proof-step containers up front and, critically, polls caller controls
/// while traversing a large proof instead of running one unchecked preflight.
fn strict_authentication_bytes(
    proof: &Proof,
    meter: &mut CheckedRefutationMeter,
) -> Result<usize, ResolutionValidationError> {
    meter.charge(0, 0)?;
    let proof_slot_size = size_of::<Option<Vec<TermId>>>()
        .checked_add(size_of::<ProofStep>())
        .ok_or(ResolutionValidationError::AccountingOverflow {
            resource: ResolutionValidationResource::Bytes,
        })?;
    let mut bytes = proof.steps.len().checked_mul(proof_slot_size).ok_or(
        ResolutionValidationError::AccountingOverflow {
            resource: ResolutionValidationResource::Bytes,
        },
    )?;
    for chunk in proof.steps.chunks(1024) {
        // This census is itself part of the accepting path. Poll the inherited
        // controls and charge every visited step rather than spending an
        // unbounded scan before the strict checker starts reporting progress.
        meter.charge(chunk.len(), 0)?;
        for step in chunk {
            let slots = match step {
                ProofStep::Assume(_) => 1,
                ProofStep::Resolution { clause, .. } | ProofStep::TheoryLemma { clause, .. } => {
                    clause.len()
                }
                ProofStep::Step {
                    clause,
                    premises,
                    args,
                    ..
                } => checked_resource_add(
                    checked_resource_add(
                        clause.len(),
                        premises.len(),
                        ResolutionValidationResource::Bytes,
                    )?,
                    args.len(),
                    ResolutionValidationResource::Bytes,
                )?,
                ProofStep::Anchor { variables, .. } => variables.len(),
                _ => 1,
            };
            bytes = checked_resource_add(
                bytes,
                checked_resource_mul(slots, 32, ResolutionValidationResource::Bytes)?,
                ResolutionValidationResource::Bytes,
            )?;
        }
    }
    meter.charge(0, 0)?;
    Ok(bytes)
}

fn authenticate_assumption_unit_premises(
    assumptions: &[TermId],
    sat_literals: &[Literal],
    authored_query_terms: &[TermId],
    var_to_term: &HashMap<u32, TermId>,
    terms: &mut TermStore,
    datatype_decls: &[(String, Vec<String>)],
    selector_decls: &[(String, Vec<String>)],
    member_signatures: &[ay_proof::DatatypeMemberSignature],
    meter: &mut CheckedRefutationMeter,
) -> Result<(), CheckedSatRefutationError> {
    if assumptions.len() != sat_literals.len() {
        return Err(CheckedSatRefutationError::AssumptionPremiseCountMismatch {
            assumptions: assumptions.len(),
            premises: sat_literals.len(),
        });
    }
    if assumptions.is_empty() {
        meter.charge(0, 0)?;
        return Ok(());
    }

    let proof_bytes = checked_resource_mul(
        assumptions.len(),
        size_of::<ProofStep>(),
        ResolutionValidationResource::Bytes,
    )?;
    meter.charge(assumptions.len(), proof_bytes)?;
    let mut proof = Proof::new();
    proof
        .steps
        .try_reserve_exact(assumptions.len())
        .map_err(|_| ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::Bytes,
        })?;
    charge_capacity_excess::<ProofStep>(proof.steps.capacity(), assumptions.len(), meter)?;
    for (index, (&assumption, &sat_literal)) in assumptions.iter().zip(sat_literals).enumerate() {
        let translated = translate_sat_clause(
            0,
            std::slice::from_ref(&sat_literal),
            var_to_term,
            &[],
            terms,
            meter,
        )?;
        if translated.as_slice() != [assumption] {
            return Err(CheckedSatRefutationError::AssumptionSemanticMismatch {
                assumption_index: index,
                assumption,
                sat_literal,
            });
        }
        proof.add_assume(assumption, None);
        if index % 1024 == 0 {
            meter.charge(0, 0)?;
        }
    }

    let authentication_bytes = strict_authentication_bytes(&proof, meter)?;
    meter.charge(proof.steps.len(), authentication_bytes)?;
    let mut authentication_resource_error = None;
    let authenticated =
        ay_proof::authenticate_premise_clauses_strict_with_typed_context_and_progress(
            &proof,
            terms,
            (!datatype_decls.is_empty()).then_some(datatype_decls),
            (!selector_decls.is_empty()).then_some(selector_decls),
            member_signatures,
            authored_query_terms,
            &mut |work, bytes| match meter.charge(work, bytes) {
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
    let authenticated = authenticated?;
    if authenticated.step_count() != proof.steps.len() {
        return Err(
            CheckedSatRefutationError::AssumptionAuthenticatedStepCountMismatch {
                proof: proof.steps.len(),
                authenticated: authenticated.step_count(),
            },
        );
    }
    for (index, &assumption) in assumptions.iter().enumerate() {
        let proof_index =
            u32::try_from(index).map_err(|_| ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Work,
            })?;
        let clause = authenticated.clause(ProofId(proof_index)).ok_or(
            CheckedSatRefutationError::UnauthenticatedAssumptionPremise {
                assumption_index: index,
                assumption,
            },
        )?;
        meter.charge(clause.len(), 0)?;
        if clause != [assumption] {
            return Err(
                CheckedSatRefutationError::UnauthenticatedAssumptionPremise {
                    assumption_index: index,
                    assumption,
                },
            );
        }
    }
    meter.charge(0, 0)?;
    Ok(())
}

include!("checked_sat_refutation/semantically_completed_premises.rs");

/// Opaque proof that one exact query has a strictly authenticated SAT-level
/// refutation.
///
/// Construction is private to this module and runs all three independent
/// validators from one immutable trace bundle. The retained value contains
/// only publication identity; the potentially large replay scratch and proof
/// fragment are dropped after successful composition.
#[derive(Debug)]
pub(in crate::executor) struct CheckedSatRefutation {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    ordered_authored_roots: Box<[TermId]>,
    ordered_assumptions: Box<[TermId]>,
    original_clause_count: usize,
    derived_step_count: usize,
}

impl CheckedSatRefutation {
    /// Whether this capability still denotes the exact public query being
    /// published, including assumption order and multiplicity.
    pub(in crate::executor) fn is_current_for(
        &self,
        query_epoch: &QueryAuthorityEpoch,
        source_context_stamp: &SourceContextStamp,
        ordered_authored_roots: &[TermId],
        assumptions: &[TermId],
    ) -> bool {
        self.query_epoch.is_same_epoch(query_epoch)
            && &self.source_context_stamp == source_context_stamp
            && self.ordered_authored_roots.as_ref() == ordered_authored_roots
            && self.ordered_assumptions.as_ref() == assumptions
            && self.original_clause_count > 0
            && self.derived_step_count > 0
    }

    fn build(executor: &mut Executor) -> Result<Self, CheckedSatRefutationError> {
        builder::build(executor)
    }
}

#[cfg(test)]
impl Executor {
    pub(in crate::executor) fn plant_stale_checked_sat_refutation_for_test(&mut self) {
        self.last_checked_sat_refutation = Some(CheckedSatRefutation {
            query_epoch: self.query_authority_epoch.clone(),
            source_context_stamp: self.ctx.source_context_stamp(),
            ordered_authored_roots: self.ctx.assertions.clone().into_boxed_slice(),
            ordered_assumptions: Box::new([]),
            original_clause_count: 1,
            derived_step_count: 1,
        });
    }
}

#[derive(Debug, thiserror::Error)]
enum CheckedSatRefutationError {
    #[error("checked SAT refutation resource envelope failed: {0}")]
    CertificationResource(#[from] ResolutionValidationError),
    #[error("the active public query is not the exact bound supported scope")]
    UnsupportedQueryScope,
    #[error("the SAT trace has no frozen authored-problem provenance")]
    MissingAuthoredProvenance,
    #[error("the frozen proof roots differ from the exact public query roots")]
    AuthoredRootMismatch,
    #[error("no SAT clause trace is available")]
    MissingClauseTrace,
    #[error("the SAT trace has no authoritative solver variable-namespace size")]
    MissingSatVariableNamespace,
    #[error("the SAT trace has no solver-minted active-scope authority")]
    MissingScopeAuthority,
    #[error("the SAT trace has no exact SAT-variable to SMT-term map")]
    MissingVariableMap,
    #[error("authored assumption {assumption_index} references stale term {assumption:?}")]
    StaleAssumptionTerm {
        assumption_index: usize,
        assumption: TermId,
    },
    #[error(
        "authored assumption {assumption_index} maps to SAT variable {variable} outside solver namespace 0..{sat_num_vars}"
    )]
    AssumptionVariableOutOfRange {
        assumption_index: usize,
        variable: u32,
        sat_num_vars: usize,
    },
    #[error("authored assumption {assumption_index} ({assumption:?}) has no exact SAT literal")]
    UnmappedAssumption {
        assumption_index: usize,
        assumption: TermId,
    },
    #[error(
        "authored assumption {assumption_index} ({assumption:?}) maps to multiple SAT literals"
    )]
    AmbiguousAssumptionMapping {
        assumption_index: usize,
        assumption: TermId,
    },
    #[error("validated unit premises differ from the exact mapped assumption slice")]
    ValidatedAssumptionPremiseMismatch,
    #[error("scope premise {premise_index} for SAT variable {variable} must be negative")]
    PositiveScopePremise { premise_index: usize, variable: u32 },
    #[error("scope premise SAT variable {variable} appears more than once")]
    DuplicateScopePremise { variable: u32 },
    #[error(
        "scope premise {premise_index} SAT variable {variable} is not greater than prior variable {previous}"
    )]
    UnorderedScopePremise {
        premise_index: usize,
        previous: u32,
        variable: u32,
    },
    #[error("scope premise SAT variable {variable} overlaps the SMT-term map")]
    MappedScopePremise { variable: u32 },
    #[error(
        "authored assumption count {assumptions} differs from validated unit-premise count {premises}"
    )]
    AssumptionPremiseCountMismatch { assumptions: usize, premises: usize },
    #[error(
        "authored assumption {assumption_index} ({assumption:?}) does not translate from SAT literal {sat_literal:?}"
    )]
    AssumptionSemanticMismatch {
        assumption_index: usize,
        assumption: TermId,
        sat_literal: Literal,
    },
    #[error(
        "authenticated assumption step count {authenticated} differs from unit proof count {proof}"
    )]
    AssumptionAuthenticatedStepCountMismatch { proof: usize, authenticated: usize },
    #[error(
        "authored assumption {assumption_index} ({assumption:?}) was not authenticated as its exact unit premise"
    )]
    UnauthenticatedAssumptionPremise {
        assumption_index: usize,
        assumption: TermId,
    },
    #[error(transparent)]
    StructuralTrace(#[from] ClauseTraceResolutionError),
    #[error(transparent)]
    OriginalProof(#[from] ExactOriginalProofError),
    #[error("strict original-premise authentication failed: {0}")]
    PremiseAuthentication(#[from] ay_proof::ProofCheckError),
    #[error("deferred Generic premise {step:?} references stale term {term:?}")]
    StaleDeferredGenericTerm { step: ProofId, term: TermId },
    #[error(
        "deferred Generic premise {step:?} has no exact successful semantic-conflict verification in this query"
    )]
    DeferredGenericNotSemanticallyVerified { step: ProofId },
    #[error("validated original count {validated} differs from semantic binding count {semantic}")]
    OriginalCountMismatch { validated: usize, semantic: usize },
    #[error(
        "authenticated step count {authenticated} differs from fragment step count {fragment}"
    )]
    AuthenticatedStepCountMismatch {
        fragment: usize,
        authenticated: usize,
    },
    #[error("trace original {trace_id} has no exact semantic binding")]
    MissingOriginalBinding { trace_id: u64 },
    #[error("trace original {trace_id} is not the exact canonical DAG original")]
    DagOriginalMismatch { trace_id: u64 },
    #[error("trace original {trace_id} is paired with a binding from another trace entry")]
    BindingSourceMismatch { trace_id: u64 },
    #[error("trace original {trace_id} references unmapped SAT variable {variable}")]
    UnmappedVariable { trace_id: u64, variable: u32 },
    #[error("trace original {trace_id} contains satisfied negative scope selector {variable}")]
    SatisfiedScopeGuard { trace_id: u64, variable: u32 },
    #[error("trace original {trace_id} maps SAT variable {variable} to stale term {term:?}")]
    StaleMappedTerm {
        trace_id: u64,
        variable: u32,
        term: TermId,
    },
    #[error("trace original {trace_id} translates to a different SMT clause")]
    SemanticClauseMismatch { trace_id: u64 },
    #[error("trace original {trace_id} is not authenticated at its exact proof-step identity")]
    AuthenticatedClauseMismatch { trace_id: u64 },
}

fn clause_sort_work(len: usize) -> Result<usize, ResolutionValidationError> {
    if len <= 1 {
        return Ok(len);
    }
    let passes = (usize::BITS - (len - 1).leading_zeros()) as usize;
    checked_resource_mul(
        len,
        checked_resource_add(passes, 1, ResolutionValidationResource::Work)?,
        ResolutionValidationResource::Work,
    )
}

fn normalize_clause_metered(
    clause: &[TermId],
    meter: &mut CheckedRefutationMeter,
) -> Result<Vec<TermId>, ResolutionValidationError> {
    let copy_and_dedup_work =
        checked_resource_mul(clause.len(), 2, ResolutionValidationResource::Work)?;
    let work = checked_resource_add(
        copy_and_dedup_work,
        clause_sort_work(clause.len())?,
        ResolutionValidationResource::Work,
    )?;
    let bytes = checked_resource_mul(
        clause.len(),
        size_of::<TermId>(),
        ResolutionValidationResource::Bytes,
    )?;
    meter.charge(work, bytes)?;

    let mut normalized = Vec::new();
    normalized.try_reserve_exact(clause.len()).map_err(|_| {
        ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::Bytes,
        }
    })?;
    charge_capacity_excess::<TermId>(normalized.capacity(), clause.len(), meter)?;
    for chunk in clause.chunks(1024) {
        meter.charge(0, 0)?;
        normalized.extend_from_slice(chunk);
    }
    normalized.sort_unstable();
    normalized.dedup();
    meter.charge(0, 0)?;
    Ok(normalized)
}

fn translate_sat_clause(
    trace_id: u64,
    literals: &[Literal],
    var_to_term: &HashMap<u32, TermId>,
    scope_assumptions: &[Literal],
    terms: &mut TermStore,
    meter: &mut CheckedRefutationMeter,
) -> Result<Vec<TermId>, CheckedSatRefutationError> {
    // In addition to the translated vector, a negative SAT literal may insert
    // one `Not` node into the term store. A per-literal node envelope rejects
    // an oversized translation before either allocation starts.
    let term_ids = checked_resource_mul(
        literals.len(),
        size_of::<TermId>(),
        ResolutionValidationResource::Bytes,
    )?;
    let potential_terms =
        checked_resource_mul(literals.len(), 128, ResolutionValidationResource::Bytes)?;
    meter.charge(
        literals.len(),
        checked_resource_add(
            term_ids,
            potential_terms,
            ResolutionValidationResource::Bytes,
        )?,
    )?;
    let mut clause = Vec::new();
    clause.try_reserve_exact(literals.len()).map_err(|_| {
        ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::Bytes,
        }
    })?;
    charge_capacity_excess::<TermId>(clause.capacity(), literals.len(), meter)?;
    for (index, &literal) in literals.iter().enumerate() {
        if index % 1024 == 0 {
            meter.charge(0, 0)?;
        }
        let variable = literal.variable().index() as u32;
        if scope_assumptions
            .iter()
            .any(|premise| !premise.is_positive() && premise.variable().index() as u32 == variable)
        {
            if literal.is_positive() {
                continue;
            }
            return Err(CheckedSatRefutationError::SatisfiedScopeGuard { trace_id, variable });
        }
        let &positive = var_to_term
            .get(&variable)
            .ok_or(CheckedSatRefutationError::UnmappedVariable { trace_id, variable })?;
        if positive.index() >= terms.len() {
            return Err(CheckedSatRefutationError::StaleMappedTerm {
                trace_id,
                variable,
                term: positive,
            });
        }
        let term = if literal.is_positive() {
            positive
        } else if let TermData::Not(inner) = terms.get(positive) {
            *inner
        } else {
            terms.mk_not_raw(positive)
        };
        clause.push(term);
    }
    Ok(normalize_clause_metered(&clause, meter)?)
}

fn verify_exact_composition_shape(
    mapping_count: usize,
    fragment: &ExactOriginalProofFragment,
    authenticated: &SemanticallyCompletedPremiseClauses,
    original_id_cone: Option<&ay_core::kani_compat::DetHashSet<u64>>,
    meter: &mut CheckedRefutationMeter,
) -> Result<(), CheckedSatRefutationError> {
    meter.charge(
        mapping_count,
        checked_resource_mul(
            mapping_count,
            size_of::<Option<Vec<TermId>>>(),
            ResolutionValidationResource::Bytes,
        )?,
    )?;
    let expected_bindings = original_id_cone.map_or(mapping_count, |cone| cone.len());
    if expected_bindings != fragment.binding_count() {
        return Err(CheckedSatRefutationError::OriginalCountMismatch {
            validated: expected_bindings,
            semantic: fragment.binding_count(),
        });
    }
    if authenticated.step_count() != fragment.proof().steps.len() {
        return Err(CheckedSatRefutationError::AuthenticatedStepCountMismatch {
            fragment: fragment.proof().steps.len(),
            authenticated: authenticated.step_count(),
        });
    }
    Ok(())
}

/// Join the independently validated structural and semantic identities.
///
/// Count equality plus iteration over every structural original makes the
/// mapping bidirectional. Stable ID alone is insufficient: the exact source
/// position and byte-for-byte SAT literal vector must also match, preventing a
/// fragment constructed from another same-ID trace from being paired here.
fn verify_exact_composition<E: CheckedResolutionEvidence>(
    validated: &E,
    fragment: &ExactOriginalProofFragment,
    authenticated: &SemanticallyCompletedPremiseClauses,
    original_id_cone: Option<&ay_core::kani_compat::DetHashSet<u64>>,
    var_to_term: &HashMap<u32, TermId>,
    scope_assumptions: &[Literal],
    terms: &mut TermStore,
    meter: &mut CheckedRefutationMeter,
) -> Result<(), CheckedSatRefutationError> {
    let mappings = validated.original_mappings();
    verify_exact_composition_shape(
        mappings.len(),
        fragment,
        authenticated,
        original_id_cone,
        meter,
    )?;

    for mapping in mappings {
        if original_id_cone.is_some_and(|cone| !cone.contains(&mapping.trace_id())) {
            continue;
        }
        let source_len = mapping.trace_entry().clause.len();
        // Stable-ID, source-position, SAT-byte, DAG, and translated-clause
        // comparisons all scan this original. Account for those scans before
        // doing them; allocation-heavy translation and normalization add their
        // own charges below.
        meter.charge(
            checked_resource_add(
                checked_resource_mul(source_len, 6, ResolutionValidationResource::Work)?,
                1,
                ResolutionValidationResource::Work,
            )?,
            0,
        )?;
        let trace_id = mapping.trace_id();
        let binding = fragment
            .binding(trace_id)
            .ok_or(CheckedSatRefutationError::MissingOriginalBinding { trace_id })?;

        let dag_index: usize = mapping
            .canonical_id()
            .checked_sub(1)
            .and_then(|index| index.try_into().ok())
            .ok_or(CheckedSatRefutationError::DagOriginalMismatch { trace_id })?;
        let Some((dag_id, dag_clause)) = validated.dag().original_clauses.get(dag_index) else {
            return Err(CheckedSatRefutationError::DagOriginalMismatch { trace_id });
        };
        if *dag_id != mapping.canonical_id()
            || dag_clause.as_slice() != mapping.trace_entry().clause.as_slice()
        {
            return Err(CheckedSatRefutationError::DagOriginalMismatch { trace_id });
        }

        if binding.trace_id() != trace_id
            || binding.trace_index() != mapping.trace_index()
            || binding.source_sat_clause() != mapping.trace_entry().clause.as_slice()
        {
            return Err(CheckedSatRefutationError::BindingSourceMismatch { trace_id });
        }

        let translated = translate_sat_clause(
            trace_id,
            &mapping.trace_entry().clause,
            var_to_term,
            scope_assumptions,
            terms,
            meter,
        )?;
        if translated != binding.clause() {
            return Err(CheckedSatRefutationError::SemanticClauseMismatch { trace_id });
        }

        let Some(checked_clause) = authenticated.clause(binding.proof_id()) else {
            return Err(CheckedSatRefutationError::AuthenticatedClauseMismatch { trace_id });
        };
        meter.charge(
            checked_resource_add(checked_clause.len(), 1, ResolutionValidationResource::Work)?,
            0,
        )?;
        if normalize_clause_metered(checked_clause, meter)? != binding.clause() {
            return Err(CheckedSatRefutationError::AuthenticatedClauseMismatch { trace_id });
        }
        meter.charge(0, 0)?;
    }

    meter.charge(0, 0)?;
    Ok(())
}

impl Executor {
    /// Whether the retained checked SAT-refutation sidecar proves the current
    /// public query: same epoch, source stamp, ordered roots, and assumptions.
    pub(in crate::executor) fn checked_sat_refutation_authorizes_current_query(&self) -> bool {
        let Some((query_epoch, source_context_stamp)) = self.checked_sat_refutation_query_scope()
        else {
            return false;
        };
        let Some(roots) = self.checked_sat_refutation_query_roots() else {
            return false;
        };
        let Some(assumptions) = self.checked_sat_refutation_query_assumptions() else {
            return false;
        };
        let authorized = self
            .last_checked_sat_refutation
            .as_ref()
            .is_some_and(|checked| {
                checked.is_current_for(&query_epoch, &source_context_stamp, roots, assumptions)
            });
        if !authorized && ay_core::misc_cli_flags().debug_cert {
            match self.last_checked_sat_refutation.as_ref() {
                None => eprintln!("CERT/authorize: no minted sidecar"),
                Some(checked) => eprintln!(
                    "CERT/authorize MISMATCH: epoch_ok={} stamp_ok={} roots_ok={} (sidecar {} vs query {}) assumptions_ok={} ({} vs {})",
                    checked.query_epoch.is_same_epoch(&query_epoch),
                    checked.source_context_stamp == source_context_stamp,
                    checked.ordered_authored_roots.as_ref() == roots,
                    checked.ordered_authored_roots.len(),
                    roots.len(),
                    checked.ordered_assumptions.as_ref() == assumptions,
                    checked.ordered_assumptions.len(),
                    assumptions.len(),
                ),
            }
        }
        authorized
    }

    /// Rebuild the checked SAT-refutation sidecar from the current immutable
    /// proof bundle. Any missing or rejected evidence clears the prior token.
    /// #dt-value-flow (#dt-context-derivation): compose constructor VALUES
    /// through the sealed step equations and record one hint per composed
    /// value fact.
    ///
    /// The residual certification premises are tower-state facts
    /// (`is-stack`, emptiness, identity across a step) whose truth flows
    /// from WHICH values the towers hold at each step. The step equations
    /// themselves are already sealed hints (`(= s^{k+1}!f (rest s^k!f))`,
    /// identities, `(stack …)` pushes); what is missing is the composed
    /// value `(= s^{k+1}!f V)` with `V` constructor-headed, which lets the
    /// ground refuter evaluate testers by projection and the transport
    /// lanes walk to it. Composition:
    ///
    /// * seed: every asserted or sealed single-equality whose one side is a
    ///   registered-constructor application anchors that side's value;
    /// * step: for a sealed single-equality `(= A B)`, `A`'s value is `B`
    ///   itself when `B` is constructor-headed, the anchored value of `B`,
    ///   or the field-`i` projection of `B = sel_i(X)` through `X`'s
    ///   anchored constructor value.
    ///
    /// Each composed fact records with MINIMAL premises — the step equation
    /// plus the prior value equality — so discharge chains recursively
    /// through earlier compositions down to asserted anchors. Every hint is
    /// re-derived by the ground refuter at sealing (congruence + selector
    /// projection close exactly these), and a hint for an arm that did NOT
    /// hold simply never discharges: candidates are capped, fail-closed.
    pub(in crate::executor) fn record_value_flow_composition_hints(&mut self) {
        use ay_core::kani_compat::{DetHashMap, DetHashSet};
        const MAX_ROUNDS: usize = 12;
        const MAX_VALUES_PER_SUBJECT: usize = 10;
        const MAX_NEW_RECORDS: usize = 4096;

        // Selector name -> (constructor name, field index, field count).
        let mut selector_index: DetHashMap<String, (String, usize, usize)> = DetHashMap::default();
        for (ctor, selectors) in self.ctx.ctor_selectors_iter() {
            for (index, selector) in selectors.iter().enumerate() {
                selector_index
                    .entry(selector.clone())
                    .or_insert_with(|| (ctor.clone(), index, selectors.len()));
            }
        }
        if selector_index.is_empty() && self.ctx.datatype_iter().next().is_none() {
            return;
        }
        let ctor_headed =
            |terms: &TermStore, term: TermId, ctx: &ay_frontend::Context| match terms.get(term) {
                TermData::App(symbol, _) => ctx.is_constructor(symbol.name()).is_some(),
                TermData::Var(name, _) => ctx.is_constructor(name).is_some(),
                _ => false,
            };

        // Candidate step equations: every sealed single-equality clause plus
        // every asserted equality.
        let mut equations: Vec<TermId> = Vec::new();
        let mut seen_equations: DetHashSet<TermId> = DetHashSet::default();
        for record in &self.dt_context_conflict_records.records {
            if let [clause_term] = record.clause.as_slice() {
                if seen_equations.insert(*clause_term) {
                    equations.push(*clause_term);
                }
            }
        }
        for &assertion in &self.ctx.assertions {
            if seen_equations.insert(assertion) {
                equations.push(assertion);
            }
        }

        // Value environment: subject -> [(value, establishing eq term)].
        let mut environment: DetHashMap<TermId, Vec<(TermId, TermId)>> = DetHashMap::default();
        let push_value = |environment: &mut DetHashMap<TermId, Vec<(TermId, TermId)>>,
                          subject: TermId,
                          value: TermId,
                          via: TermId| {
            let entry = environment.entry(subject).or_default();
            if entry.len() < MAX_VALUES_PER_SUBJECT
                && !entry.iter().any(|&(existing, _)| existing == value)
            {
                entry.push((value, via));
                true
            } else {
                false
            }
        };

        // Seed anchors.
        for &equation in &equations {
            let TermData::App(symbol, args) = self.ctx.terms.get(equation) else {
                continue;
            };
            if symbol.name() != "=" || args.len() != 2 {
                continue;
            }
            let (left, right) = (args[0], args[1]);
            for (subject, value) in [(left, right), (right, left)] {
                if !ctor_headed(&self.ctx.terms, subject, &self.ctx)
                    && ctor_headed(&self.ctx.terms, value, &self.ctx)
                {
                    push_value(&mut environment, subject, value, equation);
                }
            }
        }

        // Iterate composition to a bounded fixpoint, recording new facts.
        let mut recorded = 0usize;
        for _ in 0..MAX_ROUNDS {
            let mut changed = false;
            for &equation in &equations {
                if recorded >= MAX_NEW_RECORDS {
                    return;
                }
                let TermData::App(symbol, args) = self.ctx.terms.get(equation) else {
                    continue;
                };
                if symbol.name() != "=" || args.len() != 2 {
                    continue;
                }
                let (first, second) = (args[0], args[1]);
                for (target, source) in [(first, second), (second, first)] {
                    if ctor_headed(&self.ctx.terms, target, &self.ctx) {
                        continue;
                    }
                    // Candidate values for `source`, each with the premises
                    // that establish it beyond the step equation itself.
                    let mut candidates: Vec<(TermId, Vec<TermId>)> = Vec::new();
                    if let Some(values) = environment.get(&source) {
                        for &(value, via) in values {
                            if via != equation {
                                candidates.push((value, vec![via]));
                            }
                        }
                    }
                    // Selector projection through an anchored value.
                    if let TermData::App(sel_symbol, sel_args) = self.ctx.terms.get(source).clone()
                    {
                        if let ([inner], Some((ctor, field, arity))) = (
                            sel_args.as_slice(),
                            selector_index.get(sel_symbol.name()).cloned(),
                        ) {
                            if let Some(values) = environment.get(inner) {
                                for &(value, via) in values.clone().iter() {
                                    let TermData::App(value_symbol, value_args) =
                                        self.ctx.terms.get(value)
                                    else {
                                        continue;
                                    };
                                    if value_symbol.name() == ctor
                                        && value_args.len() == arity
                                        && field < value_args.len()
                                    {
                                        candidates.push((value_args[field], vec![via]));
                                    }
                                }
                            }
                        }
                    }
                    for (value, mut premises) in candidates {
                        if !ctor_headed(&self.ctx.terms, value, &self.ctx) {
                            continue;
                        }
                        if self.ctx.terms.sort(target) != self.ctx.terms.sort(value) {
                            continue;
                        }
                        let value_equation = self.ctx.terms.mk_eq(target, value);
                        if !push_value(&mut environment, target, value, value_equation) {
                            continue;
                        }
                        premises.push(equation);
                        premises.dedup();
                        // The composed fact may coincide with an existing
                        // equation (then it needs no record of its own).
                        if premises.iter().any(|&p| p == value_equation) {
                            continue;
                        }
                        self.dt_context_conflict_records
                            .record(vec![value_equation], premises);
                        recorded += 1;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        if ay_core::misc_cli_flags().probe_cert_reject {
            let anchored: usize = environment.len();
            eprintln!(
                "c value-flow-debug equations={} subjects={anchored} recorded={recorded}",
                equations.len()
            );
            for (subject, values) in environment.iter() {
                let rendered = ay_proof::render_term_canonical(&self.ctx.terms, *subject);
                if rendered.contains("____") && !rendered.contains('(') {
                    eprintln!(
                        "c value-flow-debug subject={rendered} values={}",
                        values.len()
                    );
                }
            }
        }
    }

    /// #dt-context-derivation: record one hint per level-0 propagated fact
    /// of the persistent solver's CURRENT trail, decoding clause/binary
    /// reasons exactly like the mid-solve walk (Tseitin aux variables are
    /// resolved through their own level-0 reasons). Records grant no
    /// authority — sealing re-derives every entailment.
    pub(in crate::executor) fn record_certification_level0_hints(&mut self) {
        use ay_sat::SolverContext;
        const MAX_WALK: usize = 8192;
        const FLATTEN_BUDGET: usize = 64;
        let mut collected: Vec<(TermId, Vec<TermId>)> = Vec::new();
        {
            let Some(state) = self.incr_theory_state.as_ref() else {
                return;
            };
            let Some(solver) = state.persistent_sat.as_ref() else {
                return;
            };
            let Some(var_to_term) = self.last_var_to_term.as_ref() else {
                return;
            };
            let Some(negations) = self.last_negations.as_ref() else {
                return;
            };
            let fact_of = |literal: Literal| -> Option<TermId> {
                let atom = *var_to_term.get(&(literal.variable().index() as u32))?;
                if literal.is_positive() {
                    Some(atom)
                } else {
                    negations.get(&atom).copied()
                }
            };
            for (walked, &literal) in solver.trail().iter().enumerate() {
                if walked >= MAX_WALK
                    || SolverContext::var_level(solver, literal.variable()) != Some(0)
                {
                    break;
                }
                let Some(side) = SolverContext::var_reason_side(solver, literal.variable()) else {
                    continue;
                };
                if side.is_empty() {
                    continue;
                }
                let Some(fact) = fact_of(literal) else {
                    continue;
                };
                let mut side_facts: Vec<TermId> = Vec::new();
                let mut work = side;
                let mut budget = FLATTEN_BUDGET;
                let mut seen: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
                let mut complete = true;
                while let Some(side_literal) = work.pop() {
                    if budget == 0 {
                        complete = false;
                        break;
                    }
                    budget -= 1;
                    let key = (side_literal.variable().index() as u64) * 2
                        + u64::from(side_literal.is_positive());
                    if !seen.insert(key) {
                        continue;
                    }
                    if let Some(side_fact) = fact_of(side_literal.negated()) {
                        if side_fact != fact && !side_facts.contains(&side_fact) {
                            side_facts.push(side_fact);
                        }
                        continue;
                    }
                    let aux = side_literal.negated();
                    if SolverContext::var_level(solver, aux.variable()) != Some(0) {
                        complete = false;
                        break;
                    }
                    let Some(aux_side) = SolverContext::var_reason_side(solver, aux.variable())
                    else {
                        complete = false;
                        break;
                    };
                    work.extend(aux_side);
                }
                if complete && !side_facts.is_empty() {
                    collected.push((fact, side_facts));
                }
            }
        }
        for (fact, premises) in collected {
            self.dt_context_conflict_records
                .record(vec![fact], premises);
        }
    }

    pub(in crate::executor) fn refresh_checked_sat_refutation(&mut self) {
        self.last_checked_sat_refutation = None;
        // #dt-context-derivation: final level-0 hint sweep. Mid-solve hint
        // walks are timing-dependent — a fact that reached level 0 AFTER the
        // last recorded conflict has no hint. The persistent solver's
        // level-0 trail at refutation time is the definitive fact set; walk
        // it once through the same reason decoding before sealing.
        self.record_certification_level0_hints();
        // #dt-value-flow: compose per-step constructor values through the
        // sealed step equations so tester/emptiness premises gain evaluable
        // anchors (see `record_value_flow_composition_hints`).
        self.record_value_flow_composition_hints();
        match CheckedSatRefutation::build(self) {
            Ok(checked) => {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "checked SAT refutation MINTED".to_string()
                });
                self.last_checked_sat_refutation = Some(checked)
            }
            Err(error) => {
                tracing::debug!(%error, "checked SAT refutation unavailable");
                // Name every decline under the probe carrier: post-
                // authentication stages (composition, deferred discharge,
                // strict re-check, resources) were invisible once the
                // census reached zero.
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    format!("checked SAT refutation DECLINED: {error}")
                });
                // Bounded opt-in diagnostics: an unauthenticated original is
                // reported WITH its rendered terms — the gate that refused it
                // is otherwise unobservable outside this crate, and the term
                // ids alone do not identify the axiom/rewrite family.
                let rendered_unauthenticated = match &error {
                    CheckedSatRefutationError::OriginalProof(
                        ExactOriginalProofError::UnauthenticatedOriginalClause { clause, .. },
                    ) if ay_core::misc_cli_flags().probe_cert_reject => {
                        Some(self.bounded_cert_reject_probe_terms(clause))
                    }
                    _ => None,
                };
                crate::executor::unsat_cert::probe_cert_reject(|| match rendered_unauthenticated {
                    Some(rendered) => format!(
                        "checked SAT refutation unavailable: {error}
  rendered: {rendered}"
                    ),
                    None => format!("checked SAT refutation unavailable: {error}"),
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{atomic::AtomicBool, Arc};

    use ay_core::{AletheRule, Proof, Sort, TheoryLemmaKind};
    use ay_frontend::{Command, Context};
    use ay_sat::{ClauseTrace, Literal, Variable};

    use super::*;
    use crate::executor::SkolemInstanceRecord;
    use crate::executor_types::SolveResult;
    include!("checked_sat_refutation/incremental_id_tests.rs");
    fn contradictory_unit_executor() -> (Executor, TermId, TermId) {
        let mut executor = Executor::new();
        let proposition = executor.ctx.terms.mk_var("p", Sort::Bool);
        let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
        executor.ctx.assertions = vec![proposition, not_proposition];
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);

        let result = executor
            .check_sat()
            .expect("contradictory Boolean units solve successfully");
        assert!(result.is_unsat());
        (executor, proposition, not_proposition)
    }

    fn assumption_dependent_unit_executor() -> (Executor, TermId, TermId) {
        let mut executor = Executor::new();
        let proposition = executor.ctx.terms.mk_var("assumed_p", Sort::Bool);
        let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
        executor.ctx.assertions = vec![proposition];
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[not_proposition]);

        let result = executor
            .check_sat_assuming(&[not_proposition])
            .expect("contrary Boolean assumption solve succeeds");
        assert!(result.is_unsat());
        (executor, proposition, not_proposition)
    }

    fn unstamped_contradictory_unit_executor() -> (Executor, TermId) {
        let mut executor = Executor::new();
        let proposition = executor.ctx.terms.mk_var("p", Sort::Bool);
        let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
        executor.ctx.assertions = vec![proposition, not_proposition];
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);

        let mut trace = ClauseTrace::new();
        trace.add_clause(41, vec![Literal::positive(Variable::new(0))], true);
        trace.add_clause(7, vec![Literal::negative(Variable::new(0))], true);
        trace.add_clause_with_hints(90, Vec::new(), false, vec![41, 7]);
        let mut var_to_term = HashMap::default();
        var_to_term.insert(0, proposition);

        executor.last_clause_trace = Some(trace);
        executor.last_var_to_term = Some(var_to_term);
        executor.last_clausification_proofs = None;
        executor.last_original_clause_theory_proofs = None;
        (executor, proposition)
    }

    fn scoped_contradictory_unit_executor() -> (Executor, TermId) {
        let mut executor = Executor::new();
        let proposition = executor.ctx.terms.mk_var("scoped_p", Sort::Bool);
        let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
        executor.ctx.assertions = vec![proposition, not_proposition];
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        executor.proof_problem_assertion_provenance = Some(
            crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
                original_problem_assertions: vec![proposition, not_proposition],
                problem_assertions: vec![proposition, not_proposition],
                assertion_sources: Default::default(),
            },
        );

        let mut sat = ay_sat::Solver::new(1);
        sat.enable_clause_trace();
        sat.push();
        sat.add_clause(vec![Literal::positive(Variable::new(0))]);
        sat.add_clause(vec![Literal::negative(Variable::new(0))]);
        assert!(sat.solve().into_inner().is_unsat());
        let trace = sat
            .snapshot_clause_trace()
            .expect("proof-enabled scoped solver retains a trace");
        assert_eq!(
            trace.scope_assumptions(),
            Some([Literal::negative(Variable::new(1))].as_slice())
        );

        let mut var_to_term = HashMap::default();
        var_to_term.insert(0, proposition);
        executor.last_clause_trace = Some(trace);
        executor.last_var_to_term = Some(var_to_term);
        executor.last_clausification_proofs = None;
        executor.last_original_clause_theory_proofs = None;
        (executor, proposition)
    }

    #[test]
    fn exact_composition_mints_epoch_bound_sidecar() {
        let (executor, proposition, not_proposition) = contradictory_unit_executor();
        let checked = executor
            .last_checked_sat_refutation
            .as_ref()
            .expect("two exact contrary authored units have a checked RUP refutation");
        assert!(checked.is_current_for(
            &executor.query_authority_epoch,
            &executor.ctx.source_context_stamp(),
            &[proposition, not_proposition],
            &[],
        ));
        assert!(!checked.is_current_for(
            &executor.query_authority_epoch,
            &executor.ctx.source_context_stamp(),
            &[not_proposition, proposition],
            &[],
        ));
        assert!(!checked.is_current_for(
            &QueryAuthorityEpoch::fresh(),
            &executor.ctx.source_context_stamp(),
            &[proposition, not_proposition],
            &[],
        ));
        assert!(!checked.is_current_for(
            &executor.query_authority_epoch,
            &Context::new().source_context_stamp(),
            &[proposition, not_proposition],
            &[],
        ));
        assert!(!checked.is_current_for(
            &executor.query_authority_epoch,
            &executor.ctx.source_context_stamp(),
            &[proposition, not_proposition],
            &[proposition],
        ));
    }

    #[test]
    fn solver_minted_scope_premise_authorizes_guard_projection() {
        let (mut executor, _) = scoped_contradictory_unit_executor();
        executor.refresh_checked_sat_refutation();
        assert!(
            executor.last_checked_sat_refutation.is_some(),
            "the sealed negative selector must support both structural replay and semantic projection"
        );
    }

    #[test]
    fn flipped_or_dropped_scope_authority_fails_closed() {
        let (mut executor, proposition) = scoped_contradictory_unit_executor();
        let mut map = HashMap::default();
        map.insert(0, proposition);
        let error = validate_scope_assumptions(
            &[Literal::positive(Variable::new(1))],
            &map,
            2,
            &mut CheckedRefutationMeter::unbounded(),
        )
        .expect_err("flipping the solver-minted negative selector must be rejected");
        assert!(matches!(
            error,
            CheckedSatRefutationError::PositiveScopePremise {
                premise_index: 0,
                variable: 1
            }
        ));

        let mut trace = executor
            .last_clause_trace
            .take()
            .expect("scoped trace candidate");
        trace.mark_empty();
        assert_eq!(trace.scope_assumptions(), None);
        executor.last_clause_trace = Some(trace);
        executor.refresh_checked_sat_refutation();
        assert!(
            executor.last_checked_sat_refutation.is_none(),
            "a trace mutation that drops scope authority must retire the capability"
        );
    }

    #[test]
    fn assumption_dependent_refutation_mints_exact_ordered_sidecar() {
        let (executor, proposition, not_proposition) = assumption_dependent_unit_executor();
        let checked = executor
            .last_checked_sat_refutation
            .as_ref()
            .expect("the bound (not p) unit must compose with authored p");
        assert!(checked.is_current_for(
            &executor.query_authority_epoch,
            &executor.ctx.source_context_stamp(),
            &[proposition],
            &[not_proposition],
        ));
        assert!(!checked.is_current_for(
            &executor.query_authority_epoch,
            &executor.ctx.source_context_stamp(),
            &[proposition],
            &[],
        ));
        assert!(!checked.is_current_for(
            &executor.query_authority_epoch,
            &executor.ctx.source_context_stamp(),
            &[proposition],
            &[proposition],
        ));
    }

    #[test]
    fn solver_assumption_drift_retires_assumption_sidecar() {
        let (mut executor, proposition, _) = assumption_dependent_unit_executor();
        executor.last_assumptions = Some(vec![proposition]);
        executor.refresh_checked_sat_refutation();
        assert!(executor.last_checked_sat_refutation.is_none());
    }

    #[test]
    fn assumption_dependent_sidecar_can_authorize_only_the_same_query() {
        let (mut executor, proposition, not_proposition) = assumption_dependent_unit_executor();
        let mut trust_proof = Proof::new();
        trust_proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        executor.last_proof = Some(trust_proof);

        let accepted =
            executor.certify_unsat_for_publication(SolveResult::unsat(), &[not_proposition]);
        assert!(accepted.is_unsat());
        assert!(executor.admit_command_solve_result(accepted).is_unsat());
        assert!(executor.last_command_unsat_was_independently_verified());

        // A fresh capability is required for a second publication. Rebuild it,
        // then prove that dropping the assumption cannot borrow its authority:
        // the authored assertion `p` by itself is satisfiable.
        executor.refresh_checked_sat_refutation();
        let mut trust_proof = Proof::new();
        trust_proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        executor.last_proof = Some(trust_proof);
        let rejected = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(rejected.is_unknown());
        assert_eq!(executor.ctx.assertions, vec![proposition]);
    }

    include!("checked_sat_refutation/resource_tests.rs");

    mod instance_authority_tests;
}
