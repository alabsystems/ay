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

/// Hard resource envelope for the independent positive-RUP replay.
///
/// These are deliberately written at the production call site rather than
/// inherited implicitly from `Default`: changing a library default cannot
/// silently widen the mandatory verdict gate.
fn validation_limits(executor: &Executor) -> ResolutionValidationLimits {
    ResolutionValidationLimits {
        deadline: executor.solve_deadline.get(),
        max_original_clauses: 2_000_000,
        max_original_literals: 16_000_000,
        max_derived_steps: 2_000_000,
        max_derived_literals: 16_000_000,
        max_hints: 32_000_000,
        max_work: 250_000_000,
        max_bytes: 512 * 1024 * 1024,
    }
}

/// One aggregate resource/control meter for every accepting phase after SAT
/// search. It resumes from conversion/replay usage rather than granting proof
/// reconstruction, strict authentication, and composition fresh allowances.
struct CheckedRefutationMeter {
    limits: ResolutionValidationLimits,
    interrupt: Option<Arc<AtomicBool>>,
    memory_limit: Option<usize>,
    work: u64,
    bytes: usize,
}

/// Read-only projection shared by ordinary test evidence and production's
/// premise-carrying evidence.  Crucially, this trait is private: it cannot be
/// used to erase the unit premises from a checked result outside this module.
trait CheckedResolutionEvidence {
    fn dag(&self) -> &ResolutionDag;
    fn original_mappings(&self) -> &[ClauseTraceOriginalMapping];
    fn validation_work(&self) -> u64;
    fn retained_bytes(&self) -> usize;
}

impl CheckedResolutionEvidence for ValidatedClauseTraceResolution {
    fn dag(&self) -> &ResolutionDag {
        self.dag()
    }

    fn original_mappings(&self) -> &[ClauseTraceOriginalMapping] {
        self.original_mappings()
    }

    fn validation_work(&self) -> u64 {
        self.validation_work()
    }

    fn retained_bytes(&self) -> usize {
        self.retained_bytes()
    }
}

impl CheckedResolutionEvidence for ValidatedPremisedClauseTraceResolution {
    fn dag(&self) -> &ResolutionDag {
        self.dag()
    }

    fn original_mappings(&self) -> &[ClauseTraceOriginalMapping] {
        self.original_mappings()
    }

    fn validation_work(&self) -> u64 {
        self.validation_work()
    }

    fn retained_bytes(&self) -> usize {
        self.retained_bytes()
    }
}

impl CheckedRefutationMeter {
    fn new(
        limits: ResolutionValidationLimits,
        interrupt: Option<Arc<AtomicBool>>,
        memory_limit: Option<usize>,
    ) -> Result<Self, ResolutionValidationError> {
        let mut meter = Self {
            limits,
            interrupt,
            memory_limit,
            work: 0,
            bytes: 0,
        };
        meter.charge(0, 0)?;
        Ok(meter)
    }

    #[cfg(test)]
    fn resume<E: CheckedResolutionEvidence>(
        limits: ResolutionValidationLimits,
        interrupt: Option<Arc<AtomicBool>>,
        memory_limit: Option<usize>,
        validated: &E,
    ) -> Result<Self, ResolutionValidationError> {
        let mut meter = Self::new(limits, interrupt, memory_limit)?;
        meter.absorb_validation(validated)?;
        Ok(meter)
    }

    fn remaining_validation_limits(
        &self,
    ) -> Result<ResolutionValidationLimits, ResolutionValidationError> {
        self.check_controls()?;
        let mut remaining = self.limits.clone();
        remaining.max_work = remaining.max_work.checked_sub(self.work).ok_or(
            ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Work,
            },
        )?;
        remaining.max_bytes = remaining.max_bytes.checked_sub(self.bytes).ok_or(
            ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Bytes,
            },
        )?;
        Ok(remaining)
    }

    fn absorb_validation<E: CheckedResolutionEvidence>(
        &mut self,
        validated: &E,
    ) -> Result<(), ResolutionValidationError> {
        let work = usize::try_from(validated.validation_work()).map_err(|_| {
            ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Work,
            }
        })?;
        self.charge(work, validated.retained_bytes())
    }

    #[cfg(test)]
    fn unbounded() -> Self {
        Self {
            limits: ResolutionValidationLimits::unbounded(),
            interrupt: None,
            memory_limit: None,
            work: 0,
            bytes: 0,
        }
    }

    fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ResolutionValidationError> {
        self.check_controls()?;
        let work =
            u64::try_from(work).map_err(|_| ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Work,
            })?;
        self.work =
            self.work
                .checked_add(work)
                .ok_or(ResolutionValidationError::AccountingOverflow {
                    resource: ResolutionValidationResource::Work,
                })?;
        if self.work > self.limits.max_work {
            return Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                limit: u128::from(self.limits.max_work),
                actual: u128::from(self.work),
            });
        }
        self.bytes =
            self.bytes
                .checked_add(bytes)
                .ok_or(ResolutionValidationError::AccountingOverflow {
                    resource: ResolutionValidationResource::Bytes,
                })?;
        if self.bytes > self.limits.max_bytes {
            return Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                limit: self.limits.max_bytes as u128,
                actual: self.bytes as u128,
            });
        }
        self.check_controls()
    }

    fn check_controls(&self) -> Result<(), ResolutionValidationError> {
        if self
            .limits
            .deadline
            .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
        {
            return Err(ResolutionValidationError::DeadlineExceeded);
        }
        if self
            .interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
            || crate::memory::memory_exceeded(self.memory_limit)
            || ay_sys::process_memory_exceeded()
        {
            return Err(ResolutionValidationError::Cancelled);
        }
        Ok(())
    }
}

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
    let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        terms,
        (!datatype_decls.is_empty()).then_some(datatype_decls),
        (!selector_decls.is_empty()).then_some(selector_decls),
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

/// Premise table whose only proof-kernel deferrals have all been discharged by
/// the semantic conflict verifier in this exact query.
///
/// The raw deferred table is intentionally private to this constructor.  A
/// caller cannot obtain a clause through this wrapper until every `Generic`
/// theory premise in the fragment has an exact `true` memo entry.  The memo is
/// cleared at query entry and whenever quantified support axioms change, so a
/// match carries the same term/support state under which the conflict was
/// independently re-solved before it was learned.
#[derive(Debug)]
struct SemanticallyCompletedPremiseClauses {
    premises: PremiseClausesWithDeferredGeneric,
}

impl SemanticallyCompletedPremiseClauses {
    fn complete(
        premises: PremiseClausesWithDeferredGeneric,
        semantic_memo: &ConflictSemanticVerifyMemo,
        terms: &TermStore,
        meter: &mut CheckedRefutationMeter,
    ) -> Result<Self, CheckedSatRefutationError> {
        for (step, clause) in premises.deferred_generic_clauses() {
            let bytes = checked_resource_mul(
                clause.len(),
                size_of::<TheoryLit>(),
                ResolutionValidationResource::Bytes,
            )?;
            let work = checked_resource_add(
                clause.len(),
                clause_sort_work(clause.len())?,
                ResolutionValidationResource::Work,
            )?;
            meter.charge(work, bytes)?;

            let mut key = Vec::new();
            key.try_reserve_exact(clause.len()).map_err(|_| {
                ResolutionValidationError::AllocationFailed {
                    resource: ResolutionValidationResource::Bytes,
                }
            })?;
            charge_capacity_excess::<TheoryLit>(key.capacity(), clause.len(), meter)?;
            for (index, &literal) in clause.iter().enumerate() {
                if literal.index() >= terms.len() {
                    return Err(CheckedSatRefutationError::StaleDeferredGenericTerm {
                        step,
                        term: literal,
                    });
                }
                key.push(match terms.get(literal) {
                    TermData::Not(inner) => TheoryLit::new(*inner, true),
                    _ => TheoryLit::new(literal, false),
                });
                if index % 1024 == 0 {
                    meter.charge(0, 0)?;
                }
            }
            key.sort_unstable();
            if semantic_memo.get(&key) != Some(&true) {
                return Err(
                    CheckedSatRefutationError::DeferredGenericNotSemanticallyVerified { step },
                );
            }
        }
        meter.charge(0, 0)?;
        Ok(Self { premises })
    }

    fn step_count(&self) -> usize {
        self.premises.step_count()
    }

    fn clause(&self, step: ProofId) -> Option<&[TermId]> {
        self.premises
            .strictly_authenticated_clause(step)
            .or_else(|| self.premises.deferred_generic_clause(step))
    }
}

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
        let (query_epoch, source_context_stamp) = executor
            .checked_sat_refutation_query_scope()
            .ok_or(CheckedSatRefutationError::UnsupportedQueryScope)?;
        let bound_assumptions = executor
            .checked_sat_refutation_query_assumptions()
            .ok_or(CheckedSatRefutationError::UnsupportedQueryScope)?;
        let solver_assumptions_match = executor.last_assumptions.as_deref()
            == Some(bound_assumptions)
            || (bound_assumptions.is_empty() && executor.last_assumptions.is_none());
        if !solver_assumptions_match {
            return Err(CheckedSatRefutationError::UnsupportedQueryScope);
        }

        // Snapshot caller-owned controls before borrowing the retained trace.
        // The deadline remains the exact absolute solve deadline; interrupt
        // and both RSS ceilings are polled cooperatively throughout conversion
        // and independent replay.
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

        // Mapping the authored assumptions into the solver-stamped Boolean
        // namespace is part of the same finite certification allowance as trace
        // conversion and replay. Give the validator only the remainder, then
        // absorb its exact usage back into this meter.
        let mut meter = CheckedRefutationMeter::new(limits, interrupt, memory_limit)?;
        let assumption_sat_literals = exact_assumption_sat_literals(
            bound_assumptions,
            var_to_term,
            &executor.ctx.terms,
            sat_num_vars,
            &mut meter,
        )?;
        let remaining_limits = meter.remaining_validation_limits()?;
        let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
            trace,
            sat_num_vars,
            assumption_sat_literals.as_slice(),
            &remaining_limits,
            &mut should_stop,
        )?;
        meter.absorb_validation(&validated)?;
        meter.charge(validated.unit_premises().len(), 0)?;
        if validated.unit_premises() != assumption_sat_literals {
            return Err(CheckedSatRefutationError::ValidatedAssumptionPremiseMismatch);
        }

        // The query epoch previously cloned this potentially large vector
        // before the aggregate meter existed. Copy it only after replay has
        // resumed that meter, with fallible allocation and periodic control
        // polling, because the boxed copy survives in the minted capability.
        let ordered_authored_roots = {
            let roots = executor
                .checked_sat_refutation_query_roots()
                .ok_or(CheckedSatRefutationError::UnsupportedQueryScope)?;
            metered_term_id_copy(roots, &mut meter)?
        };
        let ordered_assumptions = {
            let assumptions = executor
                .checked_sat_refutation_query_assumptions()
                .ok_or(CheckedSatRefutationError::UnsupportedQueryScope)?;
            metered_term_id_copy(assumptions, &mut meter)?
        };
        let authored_query_terms = metered_term_id_concat(
            ordered_authored_roots.as_slice(),
            ordered_assumptions.as_slice(),
            &mut meter,
        )?;
        let provenance = executor
            .proof_problem_assertion_provenance
            .as_ref()
            .ok_or(CheckedSatRefutationError::MissingAuthoredProvenance)?;
        meter.charge(ordered_authored_roots.len(), 0)?;
        if provenance.original_problem_assertions != ordered_authored_roots {
            return Err(CheckedSatRefutationError::AuthoredRootMismatch);
        }

        let datatype_decls = metered_datatype_decls(executor, &mut meter)?;
        let selector_decls = metered_selector_decls(executor, &mut meter)?;
        let clausification_proofs = executor.last_clausification_proofs.as_deref();
        let theory_proofs = executor.last_original_clause_theory_proofs.as_deref();

        let fragment = {
            let mut manager = SatProofManager::new(var_to_term, &mut executor.ctx.terms);
            if let Some(proofs) = clausification_proofs {
                manager.set_clausification_proofs(proofs);
            }
            if let Some(proofs) = theory_proofs {
                manager.set_original_clause_theory_proofs(proofs);
            }
            manager.build_exact_original_proof_fragment_metered(
                trace,
                authored_query_terms.as_slice(),
                &mut |work, bytes| meter.charge(work, bytes),
            )?
        };

        // Keep this opaque result function-local and tied to the exact fragment,
        // TermStore, and trace bundle used above. It is not a free-standing
        // theorem and must never be cached or paired with another fragment.
        let authentication_bytes = strict_authentication_bytes(fragment.proof(), &mut meter)?;
        // Precharge the proof-container scratch before entering the checker.
        // Its callback adds the reachable term/sort payload and rule-specific
        // work to this same meter before those phases run.
        let authentication_input_work = fragment.proof().steps.len();
        meter.charge(authentication_input_work, authentication_bytes)?;
        let mut authentication_resource_error = None;
        let authenticated =
            ay_proof::authenticate_premise_clauses_with_deferred_generic_theory_and_progress(
                fragment.proof(),
                &executor.ctx.terms,
                (!datatype_decls.is_empty()).then_some(datatype_decls.as_slice()),
                (!selector_decls.is_empty()).then_some(selector_decls.as_slice()),
                authored_query_terms.as_slice(),
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
        let authenticated = SemanticallyCompletedPremiseClauses::complete(
            authenticated?,
            &executor.conflict_semantic_verify_memo,
            &executor.ctx.terms,
            &mut meter,
        )?;
        meter.charge(0, 0)?;

        verify_exact_composition(
            &validated,
            &fragment,
            &authenticated,
            var_to_term,
            &mut executor.ctx.terms,
            &mut meter,
        )?;
        authenticate_assumption_unit_premises(
            ordered_assumptions.as_slice(),
            assumption_sat_literals.as_slice(),
            authored_query_terms.as_slice(),
            var_to_term,
            &mut executor.ctx.terms,
            datatype_decls.as_slice(),
            selector_decls.as_slice(),
            &mut meter,
        )?;

        // `Vec::into_boxed_slice` is allowed to shrink/reallocate when spare
        // capacity exists. Charge a simultaneous destination envelope before
        // conversion even though this path currently reserves exactly.
        let boxed_root_bytes = checked_resource_mul(
            ordered_authored_roots.len(),
            size_of::<TermId>(),
            ResolutionValidationResource::Bytes,
        )?;
        meter.charge(ordered_authored_roots.len(), boxed_root_bytes)?;
        let ordered_authored_roots = ordered_authored_roots.into_boxed_slice();
        let boxed_assumption_bytes = checked_resource_mul(
            ordered_assumptions.len(),
            size_of::<TermId>(),
            ResolutionValidationResource::Bytes,
        )?;
        meter.charge(ordered_assumptions.len(), boxed_assumption_bytes)?;
        let ordered_assumptions = ordered_assumptions.into_boxed_slice();
        meter.charge(0, 0)?;

        let original_clause_count = checked_resource_add(
            validated.original_mappings().len(),
            ordered_assumptions.len(),
            ResolutionValidationResource::OriginalClauses,
        )?;

        Ok(Self {
            query_epoch,
            source_context_stamp,
            ordered_authored_roots,
            ordered_assumptions,
            original_clause_count,
            derived_step_count: validated.dag().derived.len(),
        })
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
    var_to_term: &HashMap<u32, TermId>,
    terms: &mut TermStore,
    meter: &mut CheckedRefutationMeter,
) -> Result<(), CheckedSatRefutationError> {
    let mappings = validated.original_mappings();
    meter.charge(
        mappings.len(),
        checked_resource_mul(
            mappings.len(),
            size_of::<Option<Vec<TermId>>>(),
            ResolutionValidationResource::Bytes,
        )?,
    )?;
    if mappings.len() != fragment.binding_count() {
        return Err(CheckedSatRefutationError::OriginalCountMismatch {
            validated: mappings.len(),
            semantic: fragment.binding_count(),
        });
    }
    if authenticated.step_count() != fragment.proof().steps.len() {
        return Err(CheckedSatRefutationError::AuthenticatedStepCountMismatch {
            fragment: fragment.proof().steps.len(),
            authenticated: authenticated.step_count(),
        });
    }

    for mapping in mappings {
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
    /// Rebuild the checked SAT-refutation sidecar from the current immutable
    /// proof bundle. Any missing or rejected evidence clears the prior token.
    pub(in crate::executor) fn refresh_checked_sat_refutation(&mut self) {
        self.last_checked_sat_refutation = None;
        match CheckedSatRefutation::build(self) {
            Ok(checked) => {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "checked SAT refutation MINTED".to_string()
                });
                self.last_checked_sat_refutation = Some(checked)
            }
            Err(error) => {
                tracing::debug!(%error, "checked SAT refutation unavailable");
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    format!("checked SAT refutation unavailable: {error}")
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
    use crate::executor_types::SolveResult;

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

    #[test]
    fn fired_interrupt_cancels_trace_conversion_before_sidecar_refresh() {
        let (mut executor, proposition, _) = contradictory_unit_executor();
        // The successful solve has already consumed its large clause-trace
        // payload after minting the sidecar. Install a fresh, solver-stamped
        // candidate so this regression reaches the conversion boundary whose
        // caller-control propagation it exercises.
        let mut sat = ay_sat::Solver::new(1);
        sat.enable_clause_trace();
        sat.add_clause(vec![Literal::positive(Variable::new(0))]);
        sat.add_clause(vec![Literal::negative(Variable::new(0))]);
        assert!(sat.solve().into_inner().is_unsat());
        executor.last_clause_trace = sat.take_clause_trace();
        let mut var_to_term = HashMap::default();
        var_to_term.insert(0, proposition);
        executor.last_var_to_term = Some(var_to_term);
        executor.set_interrupt(Arc::new(AtomicBool::new(true)));

        let error = CheckedSatRefutation::build(&mut executor)
            .expect_err("a fired caller interrupt must reject SAT-refutation conversion");
        assert!(
            matches!(
                error,
                CheckedSatRefutationError::CertificationResource(
                    ResolutionValidationError::Cancelled
                )
            ),
            "unexpected checked-refutation cancellation error: {error:?}"
        );
    }

    #[test]
    fn post_replay_phases_share_work_and_byte_allowances() {
        let mut trace = ClauseTrace::new();
        trace.add_clause(41, vec![Literal::positive(Variable::new(0))], true);
        trace.add_clause(7, vec![Literal::negative(Variable::new(0))], true);
        trace.add_clause_with_hints(90, Vec::new(), false, vec![41, 7]);
        let validated =
            validate_clause_trace_resolution(&trace, 1, &ResolutionValidationLimits::unbounded())
                .expect("two contrary units have a checked refutation");

        let mut work_limits = ResolutionValidationLimits::unbounded();
        work_limits.max_work = validated.validation_work();
        let mut work_meter = CheckedRefutationMeter::resume(work_limits, None, None, &validated)
            .expect("the exact already-consumed work fits");
        assert!(matches!(
            work_meter.charge(1, 0),
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                ..
            })
        ));

        let mut byte_limits = ResolutionValidationLimits::unbounded();
        byte_limits.max_bytes = validated.retained_bytes();
        let mut byte_meter = CheckedRefutationMeter::resume(byte_limits, None, None, &validated)
            .expect("the exact retained trace payload fits");
        assert!(matches!(
            byte_meter.charge(0, 1),
            Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                ..
            })
        ));
    }

    #[test]
    fn post_replay_phase_observes_inherited_interrupt() {
        let mut trace = ClauseTrace::new();
        trace.add_clause(41, vec![Literal::positive(Variable::new(0))], true);
        trace.add_clause(7, vec![Literal::negative(Variable::new(0))], true);
        trace.add_clause_with_hints(90, Vec::new(), false, vec![41, 7]);
        let validated =
            validate_clause_trace_resolution(&trace, 1, &ResolutionValidationLimits::unbounded())
                .expect("two contrary units have a checked refutation");
        let fired = Arc::new(AtomicBool::new(true));

        assert!(matches!(
            CheckedRefutationMeter::resume(
                ResolutionValidationLimits::unbounded(),
                Some(fired),
                None,
                &validated,
            ),
            Err(ResolutionValidationError::Cancelled)
        ));
    }

    #[test]
    fn composition_normalization_is_precharged_before_allocation_and_sort() {
        let clause: Vec<TermId> = (0..4096).rev().map(TermId).collect();
        let mut meter = CheckedRefutationMeter::unbounded();
        meter.limits.max_work = 1000;

        let error = normalize_clause_metered(&clause, &mut meter)
            .expect_err("a wide normalization must consume the aggregate work allowance");
        assert!(matches!(
            error,
            ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                limit: 1000,
                ..
            }
        ));
    }

    #[test]
    fn authored_root_copy_is_precharged_before_allocation() {
        let roots = [TermId(0), TermId(1)];
        let mut meter = CheckedRefutationMeter::unbounded();
        meter.limits.max_bytes = size_of::<TermId>();

        let error = metered_term_id_copy(&roots, &mut meter)
            .expect_err("the retained root copy must consume the aggregate byte allowance");
        assert!(matches!(
            error,
            ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                ..
            }
        ));
    }

    #[test]
    fn exact_assumption_mapping_preserves_order_polarity_and_fails_on_ambiguity() {
        let mut terms = TermStore::new();
        let proposition = terms.mk_var("mapped_p", Sort::Bool);
        let not_proposition = terms.mk_not_raw(proposition);
        let mut map = HashMap::default();
        map.insert(0, proposition);
        let literals = exact_assumption_sat_literals(
            &[not_proposition, proposition],
            &map,
            &terms,
            1,
            &mut CheckedRefutationMeter::unbounded(),
        )
        .expect("both polarities have one exact SAT mapping");
        assert_eq!(
            literals,
            vec![
                Literal::negative(Variable::new(0)),
                Literal::positive(Variable::new(0)),
            ]
        );

        map.insert(1, proposition);
        let error = exact_assumption_sat_literals(
            &[proposition],
            &map,
            &terms,
            2,
            &mut CheckedRefutationMeter::unbounded(),
        )
        .expect_err("two SAT variables for one assumption are not exact authority");
        assert!(matches!(
            error,
            CheckedSatRefutationError::AmbiguousAssumptionMapping {
                assumption_index: 0,
                assumption,
            } if assumption == proposition
        ));
    }

    #[test]
    fn generic_premise_requires_exact_positive_semantic_memo_entry() {
        let mut terms = TermStore::new();
        let proposition = terms.mk_var("semantic_generic_p", Sort::Bool);
        let mut proof = Proof::new();
        let generic =
            proof.add_theory_lemma_with_kind("theory", vec![proposition], TheoryLemmaKind::Generic);

        let authenticate = || {
            ay_proof::authenticate_premise_clauses_with_deferred_generic_theory_and_progress(
                &proof,
                &terms,
                None,
                None,
                &[],
                &mut |_, _| true,
            )
            .expect("the proof kernel must separate the Generic obligation")
        };

        let key = vec![TheoryLit::new(proposition, false)];
        let mut rejected_memo = ConflictSemanticVerifyMemo::default();
        rejected_memo.insert(key.clone(), false);
        let error = SemanticallyCompletedPremiseClauses::complete(
            authenticate(),
            &rejected_memo,
            &terms,
            &mut CheckedRefutationMeter::unbounded(),
        )
        .expect_err("a memoized semantic rejection is not premise authority");
        assert!(matches!(
            error,
            CheckedSatRefutationError::DeferredGenericNotSemanticallyVerified { step }
                if step == generic
        ));

        let mut accepted_memo = ConflictSemanticVerifyMemo::default();
        accepted_memo.insert(key, true);
        let completed = SemanticallyCompletedPremiseClauses::complete(
            authenticate(),
            &accepted_memo,
            &terms,
            &mut CheckedRefutationMeter::unbounded(),
        )
        .expect("the exact current semantic verifier verdict discharges the obligation");
        assert_eq!(completed.clause(generic), Some([proposition].as_slice()));
    }

    #[test]
    fn mismatched_same_id_trace_and_fragment_are_rejected() {
        let mut terms = TermStore::new();
        let q = terms.mk_var("q", Sort::Bool);
        let not_q = terms.mk_not_raw(q);

        let mut trace_a = ClauseTrace::new();
        trace_a.add_clause(5, vec![Literal::positive(Variable::new(0))], true);
        trace_a.add_clause(9, vec![Literal::negative(Variable::new(0))], true);
        trace_a.add_clause_with_hints(12, Vec::new(), false, vec![5, 9]);
        let validated_a = validate_clause_trace_resolution(
            &trace_a,
            1,
            &ResolutionValidationLimits {
                deadline: None,
                max_original_clauses: 8,
                max_original_literals: 8,
                max_derived_steps: 8,
                max_derived_literals: 8,
                max_hints: 8,
                max_work: 128,
                max_bytes: 64 * 1024,
            },
        )
        .expect("trace A is structurally valid");

        let mut trace_b = ClauseTrace::new();
        trace_b.add_clause(5, vec![Literal::positive(Variable::new(1))], true);
        trace_b.add_clause(9, vec![Literal::negative(Variable::new(1))], true);
        trace_b.add_clause_with_hints(12, Vec::new(), false, vec![5, 9]);
        let mut map_b = HashMap::default();
        map_b.insert(1, q);
        let fragment_b = SatProofManager::new(&map_b, &mut terms)
            .build_exact_original_proof_fragment(&trace_b, &[q, not_q])
            .expect("trace B units have exact authored authority");
        let authenticated_b =
            ay_proof::authenticate_premise_clauses_with_deferred_generic_theory_and_progress(
                fragment_b.proof(),
                &terms,
                None,
                None,
                &[q, not_q],
                &mut |_, _| true,
            )
            .expect("trace B fragment is strictly authenticated");
        let authenticated_b = SemanticallyCompletedPremiseClauses::complete(
            authenticated_b,
            &ConflictSemanticVerifyMemo::default(),
            &terms,
            &mut CheckedRefutationMeter::unbounded(),
        )
        .expect("trace B fragment has no deferred Generic premise");

        let error = verify_exact_composition(
            &validated_a,
            &fragment_b,
            &authenticated_b,
            &map_b,
            &mut terms,
            &mut CheckedRefutationMeter::unbounded(),
        )
        .expect_err("same stable IDs cannot join evidence from different traces");
        assert!(matches!(
            error,
            CheckedSatRefutationError::BindingSourceMismatch { trace_id: 5 }
        ));
    }

    #[test]
    fn checked_sidecar_is_only_an_alternative_for_trust_family_rejection() {
        let (mut accepted, _, _) = contradictory_unit_executor();
        let mut trust_proof = Proof::new();
        trust_proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        accepted.last_proof = Some(trust_proof);
        let result = accepted.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(result.is_unsat());
        assert!(accepted.admit_command_solve_result(result).is_unsat());
        assert!(!accepted.last_command_unsat_was_strictly_verified());
        assert!(accepted.last_command_unsat_was_independently_verified());
        assert!(!accepted.last_command_unsat_was_exact_semantically_verified());

        let (mut rejected, _, _) = contradictory_unit_executor();
        rejected.last_proof = Some(Proof::new());
        let result = rejected.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(result.is_unknown());
        assert!(rejected.take_unsat_certificate().is_none());
    }

    #[test]
    fn changed_source_stamp_retires_checked_sidecar() {
        let (mut executor, _, _) = contradictory_unit_executor();
        let mut trust_proof = Proof::new();
        trust_proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        executor.last_proof = Some(trust_proof);

        executor
            .ctx
            .process_command(&Command::Push(1))
            .expect("direct frontend mutation succeeds");
        let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(result.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn missing_authoritative_namespace_and_nonempty_assumptions_decline() {
        let (mut unstamped, _) = unstamped_contradictory_unit_executor();
        unstamped.refresh_checked_sat_refutation();
        assert!(unstamped.last_checked_sat_refutation.is_none());

        let (mut assuming, proposition) = unstamped_contradictory_unit_executor();
        assuming.bind_unsat_query_assumptions(&[proposition]);
        assuming.refresh_checked_sat_refutation();
        assert!(assuming.last_checked_sat_refutation.is_none());
    }

    #[test]
    fn finite_replay_limits_remain_explicit() {
        let executor = Executor::new();
        let limits = validation_limits(&executor);
        assert!(limits.max_original_clauses < usize::MAX);
        assert!(limits.max_derived_steps < usize::MAX);
        assert!(limits.max_work < u64::MAX);
        assert!(limits.max_bytes < usize::MAX);
    }
}
