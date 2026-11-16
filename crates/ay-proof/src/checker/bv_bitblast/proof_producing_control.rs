// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Caller control for the strict checker's source-bound BV proof producer.
//!
//! No serialized proof is accepted here: the exact live clause is lowered,
//! bit-blasted and independently replayed in this call. Provenance text cannot
//! substitute for the source expression or the checked gate/resolution graph.

use super::case_split::Case;
use super::hypotheses::Reading;
use super::*;
use crate::bv_blast_export::BvBlastValidateError;
use crate::bv_blast_solver::{validate_bv_expr_compact, BvExprExportError};

mod definitional;
pub(super) use definitional::Definitions;
mod disjoint;
mod ordinary;
use ordinary::{refute_ordinary_clause, LoweredClause, OrdinaryFailure};
mod outside_frame;
pub(crate) mod retained;
pub(crate) use outside_frame::Shape as OutsideFrameShape;

// This is only a proof-search hint. Exporters must derive the property from
// the actual source guard; the native checker's result is not an Alethe step.
pub(crate) fn outside_frame_candidate(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<OutsideFrameShape> {
    OutsideFrameShape::recognize(terms, clause)
}

/// Why one proof-producing attempt did not accept its clause.
///
/// Only [`Self::Rejected`] is a verdict about the clause. The strict checker
/// rejects the lemma on either of the other two as well — every failure fails
/// closed — but it may remember only a rejection.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub(super) enum Failure {
    /// The caller's poll refused: an interrupt, the caller's solve deadline or
    /// its progress budget. Says nothing about the clause.
    #[error("proof-producing clause validation cancelled")]
    Cancelled,
    /// Decided by the clause and the COUNTED envelope alone: a counted cap ran
    /// out, the clause is outside the supported fragment, or the checked
    /// producer found it false — all before the hang guard.
    #[error("{0}")]
    Rejected(String),
    /// The outer hang guard ([`super::producer_limits::PRODUCER_HANG_GUARD`]) ended the
    /// attempt. A stop, not a verdict.
    #[error("{0}")]
    Stopped(String),
}

#[cfg(test)]
thread_local! {
    /// Proof-producing attempts started on this thread, so a test can prove a
    /// remembered refusal did not run the producer again.
    pub(super) static ATTEMPTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn note_attempt() {
    ATTEMPTS.with(|attempts| attempts.set(attempts.get() + 1));
}

#[cfg(not(test))]
fn note_attempt() {}

pub(super) fn validate(
    terms: &TermStore,
    clause: &[TermId],
    poll: semantic_control::Poll<'_>,
) -> Result<(), Failure> {
    validate_with_envelope(terms, clause, poll, ProducerEnvelope::Strict)
}

/// [`validate`] under one counted envelope (see
/// `super::producer_limits::ProducerEnvelope`): identical decision
/// procedure; `Speculative` only stops its searches sooner, so its
/// acceptances are strict acceptances and its refusals are remembered only
/// under its own envelope identity.
pub(super) fn validate_with_envelope(
    terms: &TermStore,
    clause: &[TermId],
    poll: semantic_control::Poll<'_>,
    envelope: ProducerEnvelope,
) -> Result<(), Failure> {
    note_attempt();
    poll().map_err(|_| Failure::Cancelled)?;
    if clause.is_empty() || clause.len() > MAX_PROOF_PRODUCING_CLAUSE_LITERALS {
        return Err(Failure::Rejected(format!(
            "clause has {} literals (supported: 1..={MAX_PROOF_PRODUCING_CLAUSE_LITERALS})",
            clause.len()
        )));
    }
    // An array-free clause is read with its bounded leaf-wiring hypotheses as substitutions
    // and, when it has an `ite` condition `(= v K)`, first by cases on it
    // (`super::hypotheses`, `super::case_split`). Each case is no larger
    // than the whole clause — a variable read as a literal, or a condition
    // as `false` — and the lemmas it exists for are the ones whose whole
    // attempt spends its entire envelope before it is rejected (external-codegen's
    // guarded `IDIV`, measured 2026-09-30: 74 s of sweeping). A clause over
    // arrays is lowered as it is: see `super::hypotheses` for why.
    let array_free = !mentions_array(terms, clause);
    let mut stopped = false;
    if array_free {
        'candidate: for cases in Case::candidates(terms, clause) {
            for case in &cases {
                let reading = Reading {
                    hypotheses: true,
                    case: Some(case),
                };
                match attempt(terms, clause, poll, reading, envelope) {
                    Ok(()) => {}
                    Err(Failure::Rejected(_)) => continue 'candidate,
                    Err(Failure::Stopped(_)) => {
                        stopped = true;
                        continue 'candidate;
                    }
                    Err(Failure::Cancelled) => return Err(Failure::Cancelled),
                }
            }
            return Ok(());
        }
    }
    let whole = Reading {
        hypotheses: array_free,
        case: None,
    };
    match attempt(terms, clause, poll, whole, envelope) {
        // A case the hang guard stopped may have been admitted: the verdict
        // is not the clause's alone, so it must not be remembered.
        Err(Failure::Rejected(reason)) if stopped => Err(Failure::Stopped(reason)),
        other => other,
    }
}

/// One counted attempt at `clause`, read as `reading` says, and, when it is
/// rejected and a division is in sight, ONE exact attempt under a fresh
/// envelope (`super::division`), whose sweep the proof build's memo may
/// withhold (`crate::exact_division_sweeps`). Counted caps decide;
/// `deadline` is only the outer hang guard.
fn attempt(
    terms: &TermStore,
    clause: &[TermId],
    poll: semantic_control::Poll<'_>,
    reading: Reading<'_>,
    envelope: ProducerEnvelope,
) -> Result<(), Failure> {
    let mut run = |exact_division| {
        let (limits, deadline) = envelope.limits(None);
        let route = Route {
            exact_division,
            reading,
        };
        stopped_by_hang_guard(
            prove_and_replay(terms, clause, limits, deadline, poll, route),
            deadline,
        )
    };
    match run(false) {
        Err(Failure::Rejected(reason)) if division::clause_mentions_division(terms, clause) => {
            // A caller deciding without the exact divider is refused here
            // (`crate::exact_division_sweeps::without_exact_division`).
            if crate::exact_division_sweeps::withholds_exact_division() {
                return Err(Failure::Rejected(reason));
            }
            let hypotheses = reading.case.is_none().then_some(reading.hypotheses);
            crate::exact_division_sweeps::exact_division(
                terms,
                clause,
                hypotheses,
                envelope.id(),
                || run(true),
            )
        }
        other => other,
    }
}

/// How [`prove_and_replay`] lowers one clause. The default is the clause as
/// written, its divisions abstracted.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Route<'c> {
    /// Lower `bvudiv`/`bvurem` exactly (`super::division`).
    pub(super) exact_division: bool,
    /// Read the clause as this says (`super::hypotheses`).
    pub(super) reading: Reading<'c>,
}

/// Re-label a rejection the hang guard may have caused.
///
/// Every wall-clock check under [`prove_and_replay`] — lowering, the
/// finite-array budget, SAT search, LRAT decoding, replay and final admission —
/// compares the monotonic clock with this ONE `hang_guard`. An attempt that
/// ended while the clock was still before it therefore cannot have been
/// stopped by it, so its rejection is the counted envelope's. One that ended at
/// or after it may have been, so it is a [`Failure::Stopped`], which the
/// checker never memoizes. (A counted refusal that merely finished late is
/// re-labelled too: that errs toward re-deciding, never toward a stale verdict.)
fn stopped_by_hang_guard(outcome: Result<(), Failure>, hang_guard: Instant) -> Result<(), Failure> {
    match outcome {
        Err(Failure::Rejected(reason)) if Instant::now() >= hang_guard => {
            Err(Failure::Stopped(reason))
        }
        other => other,
    }
}

fn prove_and_replay(
    terms: &TermStore,
    clause: &[TermId],
    mut limits: BvExprProofLimits,
    deadline: Instant,
    poll: semantic_control::Poll<'_>,
    route: Route<'_>,
) -> Result<(), Failure> {
    let disjoint = super::disjoint::Shape::recognize(terms, clause);
    let outside = outside_frame::Shape::recognize(terms, clause);
    let disjunction = match (disjoint, outside) {
        (None, None) => {
            return refute_ordinary_clause(terms, clause, limits, deadline, poll, route)
        }
        (Some(shape), Some(_)) => {
            // Both offset theorems are checked before conditional lowering.
            // Every discarded store, key and value is validated without
            // expanding read muxes. Remaining source operands are all lowered
            // normally under the proved local facts.
            disjoint::lower(terms, shape, &mut limits, deadline, poll)?
        }
        // Preserve complete ordinary lowering for the other offset routes.
        // It validates discarded operands before any conditional fact.
        (Some(shape), None) => {
            validate_ordinary_lowering(terms, clause, deadline, route, poll)?;
            disjoint::lower(terms, shape, &mut limits, deadline, poll)?
        }
        (None, Some(shape)) => {
            validate_ordinary_lowering(terms, clause, deadline, route, poll)?;
            outside_frame::lower(terms, shape, &mut limits, deadline, poll)?
        }
    };
    replay_refutation(disjunction, &limits, poll).map_err(|error| match error {
        BvExprExportError::Cancelled => Failure::Cancelled,
        other => Failure::Rejected(refutation_failure(&other)),
    })?;
    admit_success(deadline, poll)
}

fn validate_ordinary_lowering(
    terms: &TermStore,
    clause: &[TermId],
    deadline: Instant,
    route: Route<'_>,
    poll: semantic_control::Poll<'_>,
) -> Result<(), Failure> {
    lower_clause_as(terms, clause, deadline, route, &mut || poll().is_ok()).map(|_validated| ())
}

fn refutation_failure(error: &BvExprExportError) -> String {
    format!("negated clause did not yield a refutation: {error}")
}

/// Bit-blast the negated clause, surface a pure-RUP refutation and replay it.
fn replay_refutation(
    disjunction: BvExpr,
    limits: &BvExprProofLimits,
    poll: semantic_control::Poll<'_>,
) -> Result<(), BvExprExportError> {
    poll().map_err(|_| BvExprExportError::Cancelled)?;
    let truth = BvExpr::const_val(1, 1);
    let replayed = validate_bv_expr_compact(
        &disjunction,
        &truth,
        limits,
        &proof_replay_limits(limits),
        &mut || poll().is_ok(),
    );
    // Poll success only after disposing the transient proof and expression.
    // Their individual destructor operations are still opaque intervals.
    drop(disjunction);
    drop(truth);
    replayed
}

fn admit_success(deadline: Instant, poll: semantic_control::Poll<'_>) -> Result<(), Failure> {
    poll().map_err(|_| Failure::Cancelled)?;
    if Instant::now() >= deadline {
        return Err(Failure::Stopped(format!(
            "surfaced bit-blast refutation failed replay: {}",
            BvBlastValidateError::DeadlineExceeded
        )));
    }
    Ok(())
}

/// Whether any term below `clause` is array-sorted (a bounded walk; a clause
/// too large to walk counts as mentioning one).
fn mentions_array(terms: &TermStore, clause: &[TermId]) -> bool {
    const MAX_VISITS: usize = 1 << 20;
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = clause.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_VISITS || matches!(terms.sort(term), Sort::Array(_)) {
            return true;
        }
        stack.extend(terms.children(term));
    }
    false
}

/// [`lower_clause_as`], with the clause read as it is.
#[cfg(test)]
fn lower_clause(
    terms: &TermStore,
    clause: &[TermId],
    deadline: Instant,
    exact_division: bool,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<BvExpr, Failure> {
    let route = Route {
        exact_division,
        reading: Reading::default(),
    };
    lower_clause_as(terms, clause, deadline, route, keep_going)
}

/// Lower the clause's disjunction, read as `route` says, with small-index
/// reads scalarized over their complete domain (`lower_clause_with_reads`).
fn lower_clause_as(
    terms: &TermStore,
    clause: &[TermId],
    deadline: Instant,
    route: Route<'_>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<BvExpr, Failure> {
    let reads = array_finite::SmallIndexReads::CompleteDomain;
    lower_clause_with_reads(terms, clause, deadline, route, keep_going, reads)
        .map(|lowered| lowered.disjunction)
        .map_err(OrdinaryFailure::into_failure)
}

/// Lower the clause's disjunction, reading small-index arrays as `reads`
/// says; when the tree lowering of a clause over no array is refused for SIZE
/// (a counted cap on its expansion ran out), lower it once more
/// DEFINITIONALLY, which is linear in the source DAG (`definitional.rs` says
/// why that is sound). Arrays are excluded for the reason the sweep excludes
/// them (`bv_blast_solver/sweep.rs`), so this retry and the store-chain retry
/// (`refute_ordinary_clause`), which needs an array read, never meet. The
/// definitional retry continues the first lowering's walk count, so both
/// together stay within one lowering's walk cap; every other cap is its own,
/// as for any lowering. The retry reads the clause as the first lowering did
/// (`route`): a reading only replaces a variable by a leaf or a condition by
/// `false`, which the definitions name like any other lowered term.
fn lower_clause_with_reads(
    terms: &TermStore,
    clause: &[TermId],
    deadline: Instant,
    route: Route<'_>,
    keep_going: &mut dyn FnMut() -> bool,
    reads: array_finite::SmallIndexReads,
) -> Result<LoweredClause, OrdinaryFailure> {
    let once = |definitional, keep_going: &mut dyn FnMut() -> bool| {
        lower_clause_once(
            terms,
            clause,
            deadline,
            route,
            definitional,
            keep_going,
            reads,
        )
    };
    match once(None, keep_going) {
        (Err(OrdinaryFailure::Final(Failure::Cancelled)), _) => {
            Err(OrdinaryFailure::Final(Failure::Cancelled))
        }
        (Err(_), Some(walked)) if !mentions_array(terms, clause) => {
            once(Some(walked), keep_going).0
        }
        (ordinary, _) => ordinary,
    }
}

/// One lowering (definitional when `definitional` carries the walk an earlier
/// lowering spent), and, when it was refused because a counted lowering cap
/// ran out, the walk it spent.
fn lower_clause_once(
    terms: &TermStore,
    clause: &[TermId],
    deadline: Instant,
    route: Route<'_>,
    definitional: Option<u64>,
    keep_going: &mut dyn FnMut() -> bool,
    reads: array_finite::SmallIndexReads,
) -> (Result<LoweredClause, OrdinaryFailure>, Option<u64>) {
    let mut lowerer = if route.exact_division {
        ProofProducingLowerer::new_with_exact_division(terms, deadline)
    } else {
        ProofProducingLowerer::new_for_lemma_validation(terms, deadline)
    };
    lowerer.keep_going = Some(keep_going);
    lowerer.small_index_reads = reads;
    if let Some(walked) = definitional {
        lowerer.lowering_walk = walked;
        lowerer.record_definitions(clause);
    }
    let result = lowerer
        .lower_clause_read(clause, route.reading)
        .and_then(|mut lowered| {
            // Array functionality constrains models of the negated clause.
            // Thus C is proved as A => C: add NOT A to this disjunction,
            // whereas source-query authentication conjoins A positively.
            let consistency = lowerer.take_sparse_read_consistency()?;
            lowered.try_reserve(consistency.len()).map_err(|error| {
                lowerer.resource_exhausted = true;
                format!("sparse clause consistency allocation failed: {error}")
            })?;
            for constraint in consistency {
                lowerer.poll_lowering()?;
                lowerer.charge_constructed_expr_nodes(1)?;
                lowered.push(BvExpr::not(constraint));
            }
            let definitions = lowerer.take_negated_definitions(&lowered);
            lowered.extend(definitions);
            balanced_bool_expr_controlled(lowered, false, BvExpr::or, &mut || {
                lowerer.poll_lowering()
            })
        });
    #[cfg(test)]
    if result.is_ok() {
        lowerer.audit_census();
    }
    let walked = (result.is_err() && lowerer.resource_exhausted).then_some(lowerer.lowering_walk);
    // Legacy lowering uses diagnostic strings internally. Never infer
    // cancellation from their text or publish one as an unsupported fragment:
    // the distinct sticky state is checked before any diagnostic conversion.
    let cancelled = lowerer.cancelled;
    let exhausted = lowerer.resource_exhausted;
    let scalarized_small_index_reads = lowerer.scalarized_small_index_reads;
    drop(lowerer);
    if cancelled {
        return (Err(OrdinaryFailure::Final(Failure::Cancelled)), None);
    }
    let lowered = match result {
        Ok(disjunction) => Ok(LoweredClause {
            disjunction,
            scalarized_small_index_reads,
        }),
        Err(reason) if exhausted => Err(OrdinaryFailure::exhausted(
            reason,
            None,
            scalarized_small_index_reads,
            deadline,
        )),
        Err(reason) => Err(OrdinaryFailure::Final(Failure::Rejected(reason))),
    };
    (lowered, walked)
}

impl ProofProducingLowerer<'_, '_> {
    pub(super) fn count_bv_nodes(&mut self, expr: &BvExpr) -> Result<usize, String> {
        let nodes = bv_expr_nodes_controlled(expr, &mut || self.poll_lowering())?;
        self.charge_lowering_walk(nodes)?;
        Ok(nodes)
    }

    pub(super) fn count_proof_nodes(&mut self, expr: &ProofProducingExpr) -> Result<usize, String> {
        let nodes = proof_producing_expr_nodes_controlled(expr, &mut || self.poll_lowering())?;
        self.charge_lowering_walk(nodes)?;
        Ok(nodes)
    }

    pub(super) fn poll_lowering(&mut self) -> Result<(), String> {
        if self.cancelled {
            return Err("proof-producing lowering cancelled".to_owned());
        }
        if let Some(keep_going) = self.keep_going.as_mut() {
            // Refusal remains sticky even if a caller catches a callback panic.
            self.cancelled = true;
            if !keep_going() {
                return Err("proof-producing lowering cancelled".to_owned());
            }
            self.cancelled = false;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
