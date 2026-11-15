// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-root canonical proof search. No native producer CNF, operation tag,
//! cached decomposition, caller target, or serialized gate graph is authoritative.
//! The private source compiler reconstructs every covered live term, emits only
//! total Boolean definitions plus source roots/RM domain, and compares ALL ordered
//! originals before independently replaying RUP. Unsupported source is refusal.
//!
//! This is an internal prerequisite, NOT a public native verdict/certificate
//! publication path or original script/Rust-source journal credential. The outer
//! original reader must authenticate SMT reserved symbols and RoundingMode.
//! Logical allocations and bounded search/replay are priced on the SAME borrowed
//! original WorkBudget. Opaque SAT, allocator and destruction intervals remain
//! subject to its original callback and external process envelope, not a claimed
//! complete aggregate latency/RSS/work theorem.

use super::ReferenceError;
use ay_core::time::Instant;
use ay_core::{
    original_query::{QueryError, WorkBudget},
    TermId, TermStore,
};
use ay_sat::{ResolutionDag, ResolutionProofLimits};

mod circuit;
mod floating;
mod operators;
mod source;
#[cfg(test)]
mod tests;
mod words;

#[derive(Debug, thiserror::Error)]
pub(super) enum Error {
    #[error("canonical FP source is unsupported or malformed")]
    Source,
    #[error("canonical FP original owner refused: {0}")]
    Owner(#[from] QueryError),
    #[error("canonical FP reference refused: {0}")]
    Reference(#[from] ReferenceError),
    #[error("canonical FP refutation refused: {0}")]
    Search(#[from] ay_sat::ResolutionProofError),
    #[error("canonical FP independent replay refused: {0}")]
    Replay(#[from] ay_sat::ResolutionValidationError),
    #[error("canonical FP proof originals do not match complete source circuit")]
    Binding,
}
type Result<T> = std::result::Result<T, Error>;

/// This object cannot outlive or mutate its actual source store. It is not a
/// public proof permit. Its DAG is always replayed against newly derived CNF.
pub(super) struct Refutation<'terms, 'work, 'owner> {
    terms: &'terms TermStore,
    roots: Vec<TermId>,
    dag: ResolutionDag,
    limits: ResolutionProofLimits,
    work: &'work mut WorkBudget<'owner>,
    mode: RootMode,
}

struct Captured {
    roots: Vec<TermId>,
    dag: ResolutionDag,
}

#[derive(Clone, Copy)]
enum RootMode {
    Assertions,
    NegatedClause,
}

/// Proof search over the complete supported original root inventory. `limits`
/// supplies a preexisting absolute deadline, never a relative timeout or credit.
/// Even if that deadline is later than the original owner's, SAME work checks
/// still refuse at its original deadline. No local owner is recreated.
pub(super) fn capture<'terms, 'work, 'owner>(
    terms: &'terms TermStore,
    roots: &[TermId],
    limits: &ResolutionProofLimits,
    work: &'work mut WorkBudget<'owner>,
) -> Result<Refutation<'terms, 'work, 'owner>> {
    capture_with_mode(terms, roots, limits, work, RootMode::Assertions)
}

pub(super) fn capture_clause<'terms, 'work, 'owner>(
    terms: &'terms TermStore,
    clause: &[TermId],
    limits: &ResolutionProofLimits,
    work: &'work mut WorkBudget<'owner>,
) -> Result<Refutation<'terms, 'work, 'owner>> {
    capture_with_mode(terms, clause, limits, work, RootMode::NegatedClause)
}

fn capture_with_mode<'terms, 'work, 'owner>(
    terms: &'terms TermStore,
    roots: &[TermId],
    limits: &ResolutionProofLimits,
    work: &'work mut WorkBudget<'owner>,
    mode: RootMode,
) -> Result<Refutation<'terms, 'work, 'owner>> {
    work.charge(0)?;
    let limits = limits.clone();
    let result = capture_inner(terms, roots, &limits, work, mode);
    let terminal = observe(&limits, work);
    let Captured { roots, dag } = preserve_first(result, terminal)?;
    Ok(Refutation {
        terms,
        roots,
        dag,
        limits,
        work,
        mode,
    })
}

fn capture_inner<'terms>(
    terms: &'terms TermStore,
    roots: &[TermId],
    limits: &ResolutionProofLimits,
    work: &mut WorkBudget<'_>,
    mode: RootMode,
) -> Result<Captured> {
    deadline(limits)?;
    let cnf = compile_mode(terms, roots, limits, work, mode)?;
    price_search(limits, work)?;
    let dag = ay_sat::prove_unsat_resolution_dag_with_limits_and_cancellation(
        cnf.num_vars,
        &cnf.clauses,
        limits,
        &mut || work.charge(0).is_ok(),
    )?;
    bind(&cnf, &dag, work)?;
    let bytes = roots
        .len()
        .checked_mul(std::mem::size_of::<TermId>())
        .ok_or_else(|| work.refuse_exhaustion())?;
    work.admit(roots.len(), bytes)?;
    let mut owned = Vec::new();
    owned
        .try_reserve_exact(roots.len())
        .map_err(|_| work.refuse_exhaustion())?;
    for &root in roots {
        work.charge(1)?;
        owned.push(root);
    }
    // Destruction of canonical scratch precedes the enclosing terminal poll.
    drop(cnf);
    Ok(Captured { roots: owned, dag })
}

impl Refutation<'_, '_, '_> {
    /// Reuse the retained original owner and limits; neither can be replaced
    /// through this object. Dropping it releases only the borrow, never credit.
    pub(super) fn replay(&mut self) -> Result<()> {
        self.work.charge(0)?;
        let result = replay_mode(
            self.terms,
            &self.roots,
            &self.dag,
            &self.limits,
            self.work,
            self.mode,
        );
        let terminal = observe(&self.limits, self.work);
        preserve_first(result, terminal)
    }
}

fn replay_for(
    terms: &TermStore,
    roots: &[TermId],
    dag: &ResolutionDag,
    limits: &ResolutionProofLimits,
    work: &mut WorkBudget<'_>,
) -> Result<()> {
    replay_mode(terms, roots, dag, limits, work, RootMode::Assertions)
}

fn replay_mode(
    terms: &TermStore,
    roots: &[TermId],
    dag: &ResolutionDag,
    limits: &ResolutionProofLimits,
    work: &mut WorkBudget<'_>,
    mode: RootMode,
) -> Result<()> {
    deadline(limits)?;
    let cnf = compile_mode(terms, roots, limits, work, mode)?;
    bind(&cnf, dag, work)?;
    let mut validation = limits.validation.clone();
    validation.deadline = limits.deadline.into_iter().chain(validation.deadline).min();
    let units = usize::try_from(validation.max_work).map_err(|_| work.refuse_exhaustion())?;
    work.admit(units, validation.max_bytes)?;
    dag.validate_with_limits_and_cancellation(&validation, &mut || work.charge(0).is_ok())?;
    drop(cnf);
    work.charge(0)?;
    deadline(limits)
}

fn compile(
    terms: &TermStore,
    roots: &[TermId],
    limits: &ResolutionProofLimits,
    work: &mut WorkBudget<'_>,
) -> Result<circuit::Cnf> {
    compile_mode(terms, roots, limits, work, RootMode::Assertions)
}

fn compile_mode(
    terms: &TermStore,
    roots: &[TermId],
    limits: &ResolutionProofLimits,
    work: &mut WorkBudget<'_>,
    mode: RootMode,
) -> Result<circuit::Cnf> {
    // Source/ref/gate costs forward bulk debits unchanged to this SAME owner.
    let result = {
        let mut progress =
            |units, bytes| observe(limits, work).is_ok() && work.admit(units, bytes).is_ok();
        (|| {
            let mut program = source::build(terms, roots, limits.max_num_vars, &mut progress)?;
            let cnf = circuit::compile(&mut program, limits, mode)?;
            drop(program);
            Ok(cnf)
        })()
    };
    // Local range/allocation/envelope refusal cannot be retried through a
    // fresh program on this original owner. Preserve its earlier stop first.
    let terminal = work.charge(0).map_err(Error::Owner);
    let result = match result {
        Err(Error::Reference(
            ReferenceError::Resource | ReferenceError::Allocation | ReferenceError::Width,
        )) => Err(Error::Owner(work.refuse_exhaustion())),
        other => other,
    };
    preserve_first(result, terminal)
}

/// Observe both retained controls without rewriting an earlier source/replay
/// failure. A healthy candidate requires both controls; no error is evidence.
fn observe(limits: &ResolutionProofLimits, work: &mut WorkBudget<'_>) -> Result<()> {
    let owner = work.charge(0).map_err(Error::Owner);
    let clock = deadline(limits);
    if clock.is_err() {
        work.refuse_exhaustion();
    }
    owner.and(clock)
}

fn preserve_first<T>(result: Result<T>, terminal: Result<()>) -> Result<T> {
    match result {
        Err(error) => Err(error),
        Ok(value) => match terminal {
            Ok(()) => Ok(value),
            Err(error) => {
                drop(value);
                Err(error)
            }
        },
    }
}

fn deadline(limits: &ResolutionProofLimits) -> Result<()> {
    let end = limits
        .deadline
        .ok_or(ay_sat::ResolutionProofError::UnboundedSearch)?;
    if Instant::now() >= end {
        return Err(ay_sat::ResolutionProofError::DeadlineExceeded {
            phase: ay_sat::ResolutionProofPhase::Preflight,
        }
        .into());
    }
    Ok(())
}

fn price_search(limits: &ResolutionProofLimits, work: &mut WorkBudget<'_>) -> Result<()> {
    // These finite ceilings are PREPAYMENT, not a renewed grant. This counts
    // bounded search counters and independent replay, not all opaque SAT work.
    let counters = limits
        .max_conflicts
        .zip(limits.max_decisions)
        .ok_or_else(|| work.refuse_exhaustion())?;
    let units = counters
        .0
        .checked_add(counters.1)
        .and_then(|n| n.checked_add(limits.validation.max_work))
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| work.refuse_exhaustion())?;
    let bytes = limits
        .max_proof_output_bytes
        .checked_add(limits.max_codec_bytes)
        .and_then(|n| n.checked_add(limits.max_backward_reconstruction_bytes))
        .and_then(|n| n.checked_add(limits.validation.max_bytes))
        .ok_or_else(|| work.refuse_exhaustion())?;
    work.admit(units, bytes)?;
    Ok(())
}

fn bind(cnf: &circuit::Cnf, dag: &ResolutionDag, work: &mut WorkBudget<'_>) -> Result<()> {
    work.charge(1)?;
    if dag.num_vars != cnf.num_vars || dag.original_clauses.len() != cnf.clauses.len() {
        return Err(Error::Binding);
    }
    for (index, ((id, actual), expected)) in
        dag.original_clauses.iter().zip(&cnf.clauses).enumerate()
    {
        work.charge(expected.len().saturating_add(1))?;
        let wanted = u64::try_from(index)
            .ok()
            .and_then(|n| n.checked_add(1))
            .ok_or(Error::Binding)?;
        if *id != wanted || actual != expected {
            return Err(Error::Binding);
        }
    }
    Ok(())
}
