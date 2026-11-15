// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed original-model validation. The decision procedures remain unchanged.

use super::*;
use crate::bmc::memory::Budget;
use crate::smt::replay_control::ScopedReplayControl;
use crate::smt::resource_observation::{ResourceRefusal, ScopedResourceObservation};
use ay_core::time::Instant;

/// Why a caller-submitted invariant did or did not pass full original checks.
/// This reports validation, NOT a Safe/Unsafe verdict for the CHC problem.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExternalInvariantValidation {
    /// Every necessary original check completed and the owner remains open.
    Valid,
    /// An original clause-violation query was SAT. The CANDIDATE is refuted;
    /// this is not a reachable counterexample or proof that the CHC is unsafe.
    Refuted,
    /// An empty/incomplete interpretation or free non-binder variable was
    /// explicitly rejected. No satisfiable violation witness is claimed.
    Rejected,
    /// The original caller/ambient wall was actually observed expired.
    Timeout,
    /// The linked sticky caller/ambient cancellation was actually observed.
    Cancelled,
    /// An actual local term ceiling or process-wide cap refusal was observed.
    /// This does not imply aggregate PDR/model/AST allocation accounting.
    Memory,
    /// The captured original ResourceGuard actually exhausted its work grant.
    /// These are that guard's shared ticks, not a claim of complete primitive
    /// solver-work accounting. An opaque Boolean stop remains Inconclusive.
    WorkLimit,
    /// No complete validation and no more specific observed reason. Includes
    /// unsupported checks, solver unknowns and unclassified certificate refusal.
    Inconclusive,
}

/// Validate on the ORIGINAL signatures/clauses with precise refusal kinds.
///
/// Keeps the legacy full PDR, quantified-certificate and independent plus
/// exhaustive empty-model checks. False/Unknown never becomes Refuted.
/// One wall starts before setup; nested clocks/caps only tighten it. Resource
/// observations share one original owner through nested scopes and survive
/// context reset/cleanup. A fresh outer call after Drop has no old latch. The first
/// OBSERVED owner refusal wins over all decision labels, including a candidate
/// refutation found before cleanup exceeded the wall. This refuses evidence,
/// not the logical fact: no original-model Refuted/Valid is published outside
/// the caller's envelope. Previously observed memory survives later reset;
/// simultaneous first polling checks cancellation, memory, then the wall. Opaque
/// phases remain cooperative; this is not a hard drain-latency/RSS guarantee.
/// Internal verifier/panic errors remain Err, even if cleanup also observes a
/// resource stop; only successful API returns use these typed decision labels.
pub fn validate_external_invariant_model_typed(
    problem: &ChcProblem,
    model: &InvariantModel,
    config: &PdrConfig,
) -> ChcResult<ExternalInvariantValidation> {
    let _verification_pin = crate::smt::lane::ScopedVerificationMode::install();
    ay_core::catch_ay_panics(
        AssertUnwindSafe(|| validate_attempt(problem, model, config)),
        |reason| Err(ChcError::Internal(reason)),
    )
}

fn validate_attempt(
    problem: &ChcProblem,
    model: &InvariantModel,
    config: &PdrConfig,
) -> ChcResult<ExternalInvariantValidation> {
    let start = Instant::now();
    let observation = ScopedResourceObservation::install();
    let memory = Budget::capture(config.memory_budget, None);
    let _memory_scope = memory.install();
    let budget = config.solve_timeout.unwrap_or(PDR_PROOF_VALIDATION_TIMEOUT);
    let Some(deadline) = start.checked_add(budget) else {
        return Ok(ExternalInvariantValidation::Inconclusive);
    };
    let caller = config.effective_cancellation_token();
    let control = ScopedReplayControl::install_until(deadline, caller.as_ref());
    if let Some(refusal) = refusal(&control, memory, &observation) {
        return Ok(refusal);
    }
    let mut validation_config = external_model_validation_config(config);
    validation_config.cancellation_token = control.cancellation().cloned();
    validation_config.memory_budget = memory.term_limit();
    validation_config.solve_timeout =
        Some(control.deadline().saturating_duration_since(Instant::now()));
    let result = check_original(problem, model, validation_config)?;
    // All nested verifier/executor destruction completed inside check_original.
    // An observed refusal never publishes Valid/Refuted even after live recovery.
    Ok(refusal(&control, memory, &observation).unwrap_or(result))
}

fn refusal(
    control: &ScopedReplayControl,
    memory: Budget,
    observation: &ScopedResourceObservation,
) -> Option<ExternalInvariantValidation> {
    let interrupted = crate::smt::deadline::lane_interrupt_flag()
        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed));
    if interrupted
        || control
            .cancellation()
            .is_some_and(CancellationToken::is_cancelled)
    {
        observation.note(ResourceRefusal::Cancelled);
    }
    let _open = memory.open(); // records an actual zero/global-memory refusal
    if Instant::now() >= control.deadline() {
        observation.note(ResourceRefusal::Timeout);
    }
    observation.first().map(|reason| match reason {
        ResourceRefusal::Cancelled => ExternalInvariantValidation::Cancelled,
        ResourceRefusal::Timeout => ExternalInvariantValidation::Timeout,
        ResourceRefusal::Memory => ExternalInvariantValidation::Memory,
    })
}

fn check_original(
    problem: &ChcProblem,
    model: &InvariantModel,
    validation_config: PdrConfig,
) -> ChcResult<ExternalInvariantValidation> {
    if let Some(certificate) = model.ghost_pair_certificate() {
        return Ok(from_completed(
            crate::transform::recheck_ghost_pair_certificate(
                problem,
                certificate,
                validation_config.solve_timeout,
                false,
            ),
        ));
    }
    if model.is_empty() {
        if let Some(result) =
            validate_empty_scalar_acyclic_bmc_certificate(problem, &validation_config)
        {
            return result.map(from_completed);
        }
    }
    let budget = validation_config.solve_timeout;
    let mut verifier = PdrSolver::new(problem.clone(), validation_config);
    let completed = match budget {
        Some(budget) if budget.is_zero() => false,
        Some(budget) => {
            verifier.set_validation_deadline(budget);
            verifier.verify_model_with_budget(model, budget)
        }
        None => verifier.try_verify_model(model)?,
    };
    Ok(if completed {
        ExternalInvariantValidation::Valid
    } else {
        verifier
            .observed_model_validation_failure()
            .unwrap_or(ExternalInvariantValidation::Inconclusive)
    })
}

fn from_completed(completed: bool) -> ExternalInvariantValidation {
    if completed {
        ExternalInvariantValidation::Valid
    } else {
        ExternalInvariantValidation::Inconclusive
    }
}

mod owner;
pub use owner::{validate_external_invariant_model_with_owner, ExternalInvariantValidationOwner};

#[cfg(test)]
mod tests;
