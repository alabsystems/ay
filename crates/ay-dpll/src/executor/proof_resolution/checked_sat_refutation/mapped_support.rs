// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pre-conversion screen: decline a checked SAT refutation that the exact
//! original-fragment builder is certain to reject, before paying for the trace
//! conversion and replay.
//!
//! This is the "bit-blast UnmappedVariable" class that
//! `checked_qpf_instance_refutation` names: an eager bit-blast trace carries
//! original gate clauses over SAT variables absent from `var_to_term`, so the
//! sidecar can never mint for it. Measured on the ay-chc nested-record
//! certification obligation (DT/array/bit-vector): every certification built
//! the sidecar three times (the solve, then the nested re-solves of
//! deferred-trust steps (3) and (4)), and each spent 0.3-0.5 s on an A725 core
//! in trace conversion only to decline with "original clause N references
//! unmapped SAT variable M".

use super::*;

#[path = "mapped_support/search.rs"]
mod search;

// Private optimization allowances, not new proof or user-configurable limits.
// Exceeding any of these skips the screen and leaves the complete builder alone.
const MAX_SCREEN_WORK: u64 = 1_000_000;
const MAX_SCREEN_BYTES: usize = 64 * 1024 * 1024;
const MAX_SCREEN_LITERALS: usize = 65_536;
const MAX_SCREEN_CLAUSES: usize = 8_192;
const MAX_SCREEN_VARIABLES: usize = 4_096;

/// Deterministic conflict allowance for the mapped-support satisfiability
/// check.
///
/// The screen pays off when the mapped originals are EASILY satisfiable, which
/// is the eager bit-blast shape it exists for: the SAT search refutes the
/// problem on bit-level clauses over variables no SMT term names, while the
/// Boolean skeleton over named atoms is satisfiable at once (measured: 60
/// clauses over 24 variables, decided in well under a millisecond). When the
/// mapped originals are hard or unsatisfiable (a lazy, lemma-based refutation)
/// the check gives up after this many conflicts and the ordinary conversion
/// runs exactly as before, so a small fixed allowance bounds its cost on every
/// other path.
const MAPPED_SUPPORT_CONFLICT_BUDGET: u64 = 1_000;
const MAPPED_SUPPORT_DECISION_BUDGET: u64 = 4_096;

#[derive(Debug)]
enum ScreenFailure {
    Decline,
    CallerStop(ResolutionValidationError),
}

impl From<ResolutionValidationError> for ScreenFailure {
    fn from(error: ResolutionValidationError) -> Self {
        match error {
            ResolutionValidationError::DeadlineExceeded | ResolutionValidationError::Cancelled => {
                Self::CallerStop(error)
            }
            _ => Self::Decline,
        }
    }
}

impl From<CheckedSatRefutationError> for ScreenFailure {
    fn from(error: CheckedSatRefutationError) -> Self {
        match error {
            CheckedSatRefutationError::CertificationResource(error) => error.into(),
            _ => Self::Decline,
        }
    }
}

type ScreenResult<T> = Result<T, ScreenFailure>;

fn screen_limits(executor: &Executor) -> ResolutionValidationLimits {
    let mut limits = validation_limits(executor);
    limits.max_work = limits.max_work.min(MAX_SCREEN_WORK);
    limits.max_bytes = limits.max_bytes.min(MAX_SCREEN_BYTES);
    limits
}

/// Refuse a trace whose every acceptable refutation must rest on an original
/// clause the fragment builder cannot translate.
///
/// WHY THE DECLINE IS CERTAIN. `build_fragment` translates every original of
/// the validated DAG's empty-clause cone (every original, when that cone
/// cannot be computed), and `translate_exact_original_clause` rejects a clause
/// holding a literal over a SAT variable that is neither a scope selector nor
/// a key of `var_to_term` (`UnmappedVariable`), or a negative scope selector
/// (`SatisfiedScopeGuard`). Call every other original *mappable*. Replay is
/// hints-only RUP under exactly the structural unit premises (scope selectors
/// plus the exact assumption literals), so a validated DAG shows that its cone
/// originals together with those premises are propositionally unsatisfiable.
/// If the mappable originals together with the premises are SATISFIABLE, then
/// every cone that validation could accept contains an unmappable original,
/// whatever the conversion's hint compaction or widening selects, and the
/// build rejects it. Declining here therefore changes no sidecar outcome: it
/// only skips the sealing, conversion, replay and fragment work whose
/// rejection is already decided.
///
/// The screen speaks only on a model it has itself checked against every
/// mappable clause and every premise. Anything `replay_trace` would reject on
/// its own (missing scope, trace, namespace or map, an unmappable assumption,
/// a malformed selector, a literal outside the namespace), an unsatisfiable or
/// locally over-budget check all say nothing, and the ordinary build runs.
/// Observed caller deadline, interrupt and memory stops instead remain terminal;
/// they must not start the expensive fallback. The local meter is a throwaway:
/// the build's allowance is untouched.
pub(super) fn reject_unmappable_refutation(
    executor: &Executor,
) -> Result<(), CheckedSatRefutationError> {
    reject_with_limits(executor, screen_limits(executor))
}

fn reject_with_limits(
    executor: &Executor,
    limits: ResolutionValidationLimits,
) -> Result<(), CheckedSatRefutationError> {
    let mut meter = CheckedRefutationMeter::new(
        limits,
        executor.solve_interrupt.clone(),
        executor.memory_limit(),
    )?;
    let result = screen(executor, &mut meter);
    // Poll even after an ordinary refusal or a false SAT result. Preserve an
    // already observed stop even if a live interrupt/memory condition recovered.
    if let Err(ScreenFailure::CallerStop(error)) = &result {
        return Err(error.clone().into());
    }
    if let Err(ScreenFailure::CallerStop(error)) = meter.charge(0, 0).map_err(ScreenFailure::from) {
        return Err(error.into());
    }
    match result {
        Ok(Some((trace_id, variable))) => {
            Err(CheckedSatRefutationError::UnmappableRefutation { trace_id, variable })
        }
        _ => Ok(()),
    }
}

fn screen(
    executor: &Executor,
    meter: &mut CheckedRefutationMeter,
) -> ScreenResult<Option<(u64, u32)>> {
    let inputs = ScreenInputs::gather(executor, meter)?;
    let partition = inputs.partition_originals(meter)?;
    if search::mapped_originals_satisfiable(
        &partition.mappable,
        &inputs.unit_premises,
        meter,
        executor.solve_interrupt.clone(),
    )? {
        Ok(Some(partition.first_unmappable))
    } else {
        Ok(None)
    }
}

/// Admit requested and actual capacity before writing any element. Allocation
/// failures are local declines; the final control poll still checks caller RSS.
fn screen_vec<T>(count: usize, meter: &mut CheckedRefutationMeter) -> ScreenResult<Vec<T>> {
    let bytes = checked_resource_mul(count, size_of::<T>(), ResolutionValidationResource::Bytes)?;
    meter.charge(count, bytes)?;
    let mut buffer = Vec::new();
    buffer
        .try_reserve_exact(count)
        .map_err(|_| ScreenFailure::Decline)?;
    charge_capacity_excess::<T>(buffer.capacity(), count, meter)?;
    Ok(buffer)
}

fn search_work(count: usize) -> usize {
    count.bit_width() as usize + 1
}

/// The exact trace, variable map and structural unit premises
/// `replay_trace` validates under.
struct ScreenInputs<'executor> {
    trace: &'executor ay_sat::ClauseTrace,
    sat_num_vars: usize,
    var_to_term: &'executor HashMap<u32, TermId>,
    scope_assumptions: &'executor [Literal],
    unit_premises: Vec<Literal>,
}

/// The originals split by translatability, when at least one is unmappable.
struct OriginalPartition<'trace> {
    /// Trace id and SAT variable of the first unmappable original.
    first_unmappable: (u64, u32),
    mappable: Vec<&'trace [Literal]>,
}

impl<'executor> ScreenInputs<'executor> {
    /// Reuse the exact structural helpers, under smaller local allowances.
    fn gather(
        executor: &'executor Executor,
        meter: &mut CheckedRefutationMeter,
    ) -> ScreenResult<Self> {
        let bound_assumptions = executor
            .checked_sat_refutation_query_assumptions()
            .ok_or(ScreenFailure::Decline)?;
        let trace = executor
            .last_clause_trace
            .as_ref()
            .ok_or(ScreenFailure::Decline)?;
        let sat_num_vars = trace.solver_num_vars().ok_or(ScreenFailure::Decline)?;
        let var_to_term = executor
            .last_var_to_term
            .as_ref()
            .ok_or(ScreenFailure::Decline)?;
        let scope_assumptions = trace.scope_assumptions().ok_or(ScreenFailure::Decline)?;
        if bound_assumptions.len() > MAX_SCREEN_VARIABLES
            || var_to_term.len() > MAX_SCREEN_LITERALS
            || scope_assumptions.len() > MAX_SCREEN_VARIABLES
        {
            return Err(ScreenFailure::Decline);
        }
        let assumption_literals = exact_assumption_sat_literals(
            bound_assumptions,
            var_to_term,
            &executor.ctx.terms,
            sat_num_vars,
            meter,
        )?;
        // This validates negative polarity, namespace, absence from the term
        // map, and strictly ascending variable IDs BEFORE binary search below.
        validate_scope_assumptions(scope_assumptions, var_to_term, sat_num_vars, meter)?;
        let unit_premises = metered_literal_concat(scope_assumptions, &assumption_literals, meter)?;
        Ok(Self {
            trace,
            sat_num_vars,
            var_to_term,
            scope_assumptions,
            unit_premises,
        })
    }

    /// Split the originals exactly as `translate_exact_original_clause`
    /// judges them: a selector must be positive, every other variable must be
    /// named. No scratch allocation is proportional to the SAT namespace.
    fn partition_originals(
        &self,
        meter: &mut CheckedRefutationMeter,
    ) -> ScreenResult<OriginalPartition<'executor>> {
        let trace = self.trace;
        let mut first_unmappable = None;
        let mut mappable = screen_vec(trace.len().min(MAX_SCREEN_CLAUSES), meter)?;
        let mut literal_count = 0usize;
        for entry in trace.entries().iter() {
            meter.charge(1, 0)?;
            if !entry.is_original {
                continue;
            }
            literal_count = literal_count
                .checked_add(entry.clause.len())
                .ok_or(ScreenFailure::Decline)?;
            if literal_count > MAX_SCREEN_LITERALS {
                return Err(ScreenFailure::Decline);
            }
            let work = checked_resource_mul(
                entry.clause.len(),
                search_work(self.scope_assumptions.len()) + 1,
                ResolutionValidationResource::Work,
            )?;
            meter.charge(work, 0)?;
            let mut unmappable = None;
            for (index, literal) in entry.clause.iter().enumerate() {
                if index % 256 == 0 {
                    meter.charge(0, 0)?;
                }
                let variable = literal.variable().index();
                if variable >= self.sat_num_vars {
                    return Err(ScreenFailure::Decline);
                }
                let selector = self
                    .scope_assumptions
                    .binary_search_by_key(&variable, |premise| premise.variable().index())
                    .is_ok();
                let translatable = if selector {
                    literal.is_positive()
                } else {
                    self.var_to_term.contains_key(&(variable as u32))
                };
                if !translatable && unmappable.is_none() {
                    unmappable = Some(variable as u32);
                }
            }
            match unmappable {
                Some(variable) => {
                    first_unmappable.get_or_insert((entry.id, variable));
                }
                None => {
                    if mappable.len() == MAX_SCREEN_CLAUSES {
                        return Err(ScreenFailure::Decline);
                    }
                    mappable.push(entry.clause);
                }
            }
        }
        Ok(OriginalPartition {
            first_unmappable: first_unmappable.ok_or(ScreenFailure::Decline)?,
            mappable,
        })
    }
}

#[cfg(test)]
#[path = "mapped_support_tests.rs"]
mod tests;
