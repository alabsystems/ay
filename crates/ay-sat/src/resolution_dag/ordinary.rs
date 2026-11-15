// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cancellation-only sibling of the ordinary text-LRAT producer.

use super::*;

#[cfg(test)]
mod tests;

/// Ordinary producer errors without changing the legacy error enum.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ResolutionDagCancellationError {
    /// The original borrowed observer refused this entire call.
    #[error("ordinary resolution proof cancelled")]
    Cancelled,
    /// An unchanged ordinary producer error.
    #[error(transparent)]
    Resolution(#[from] ResolutionDagError),
}

/// Produce the ordinary refutation with one borrowed, sticky stop callback.
///
/// The first attempt keeps ordinary inprocessing enabled. Only the same
/// hint-authority fail-closed condition retries once with inprocessing off.
/// Both actual solver children share the observer, which is never moved to a
/// worker or stored beyond this call. No deadline, resource allowance, binary
/// proof mode, bounded posture or extra independent replay is introduced.
/// Existing configured artifact hooks are preserved rather than suppressed.
///
/// Input copies, proof extraction and result admission poll the same control;
/// the solver's ordinary interrupt checkpoints poll it inside both attempts.
/// Individual clause insertion, startup/inprocessing/finalization, configured
/// artifact I/O, text parsing, allocations and destruction retain opaque
/// intervals. This is cooperative cancellation, not an allocation/work budget
/// or a hard latency guarantee. No proof or SAT result escapes an observed stop.
///
/// # Errors
/// Returns `Cancelled` for an observed refusal; otherwise preserves every
/// error of [`prove_unsat_resolution_dag`]. Reached ordinary errors receive no
/// fresh callback, while successful results require final post-cleanup admission.
pub fn prove_unsat_resolution_dag_with_cancellation(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<ResolutionDag, ResolutionDagCancellationError> {
    with_work(num_vars, clauses, keep_going, None)
}

pub(super) fn with_work(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    keep_going: &mut dyn FnMut() -> bool,
    mut work: Option<ResolutionDagWork>,
) -> Result<ResolutionDag, ResolutionDagCancellationError> {
    let control = ProofControl::new(keep_going);
    control
        .poll()
        .map_err(|_| ResolutionDagCancellationError::Cancelled)?;
    let result = attempts(&control, |mode, control| {
        once_with_work(num_vars, clauses, mode, control, work.as_mut())
    });
    control
        .check_latched()
        .map_err(|_| ResolutionDagCancellationError::Cancelled)?;
    if result.is_ok() {
        // Both attempts' solver, writer, parsing and source scratch are gone.
        control
            .poll()
            .map_err(|_| ResolutionDagCancellationError::Cancelled)?;
    }
    result.map_err(ResolutionDagCancellationError::Resolution)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Inprocessing {
    Ordinary,
    HintAuthorityRetry,
}

enum Attempt {
    Done(Result<ResolutionDag, ResolutionDagError>),
    LratAuthorityFailClosed,
}

fn observe(control: &ProofControl<'_>) -> Result<(), ResolutionDagError> {
    control.poll().map_err(|_| ResolutionDagError::Unknown)
}

fn attempts(
    control: &ProofControl<'_>,
    mut derive: impl FnMut(Inprocessing, &ProofControl<'_>) -> Attempt,
) -> Result<ResolutionDag, ResolutionDagError> {
    match derive(Inprocessing::Ordinary, control) {
        Attempt::Done(outcome) => outcome,
        Attempt::LratAuthorityFailClosed => {
            observe(control)?;
            match derive(Inprocessing::HintAuthorityRetry, control) {
                Attempt::Done(outcome) => outcome,
                Attempt::LratAuthorityFailClosed => Err(ResolutionDagError::Unknown),
            }
        }
    }
}

#[cfg(test)]
fn once(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    mode: Inprocessing,
    control: &ProofControl<'_>,
) -> Attempt {
    once_with_work(num_vars, clauses, mode, control, None)
}

fn once_with_work(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    mode: Inprocessing,
    control: &ProofControl<'_>,
    work: Option<&mut ResolutionDagWork>,
) -> Attempt {
    Attempt::Done(match solve(num_vars, clauses, mode, control, work) {
        Ok(Some(dag)) => Ok(dag),
        Ok(None) => return Attempt::LratAuthorityFailClosed,
        Err(error) => Err(error),
    })
}

/// The existing ordinary solve, including its ambient artifact hooks.
/// Inprocessing is disabled only for the hint-authority retry, never by a
/// control or default resource policy. The same typed authority condition,
/// first-pass errors, original clause ids and pure-RUP parsing are preserved.
fn solve(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    mode: Inprocessing,
    control: &ProofControl<'_>,
    work: Option<&mut ResolutionDagWork>,
) -> Result<Option<ResolutionDag>, ResolutionDagError> {
    observe(control)?;
    let mut solver = Solver::with_proof_output(
        num_vars,
        ProofOutput::lrat_text(Vec::<u8>::new(), clauses.len() as u64),
    );
    // Already bit-blasted CNF: preserve the ordinary producer's preprocessing
    // exclusion and leave its authority-gated materializer entirely untouched.
    solver.set_preprocess_enabled(false);
    if mode == Inprocessing::HintAuthorityRetry {
        solver.disable_all_inprocessing();
    }
    for clause in clauses {
        observe(control)?;
        solver.add_clause(clause.clone());
        observe(control)?;
    }
    observe(control)?;
    if let Some(work) = work.as_deref() {
        work.install(&mut solver);
    }
    let result = solver
        .solve_interruptible(|| control.poll().is_err())
        .into_inner();
    let enveloped = work.is_some();
    if let Some(work) = work {
        work.charge(&solver);
    }
    control
        .check_latched()
        .map_err(|_| ResolutionDagError::Unknown)?;
    match result {
        SatResult::Unsat(_) => {}
        SatResult::Sat(_) => return Err(ResolutionDagError::Satisfiable),
        SatResult::Unknown if enveloped && within::ran_out(&solver) => {
            return Err(ResolutionDagError::OverEnvelope);
        }
        SatResult::Unknown => {
            if solver.last_unknown_reason() == Some(SatUnknownReason::ProofFinalizationFailure)
                && solver
                    .last_unknown_detail()
                    .is_some_and(|detail| detail.contains("LRAT authority fail-closed"))
            {
                return Ok(None);
            }
            return Err(ResolutionDagError::Unknown);
        }
    }
    observe(control)?;
    let writer = solver
        .take_proof_writer()
        .ok_or(ResolutionDagError::ProofWriterUnavailable)?;
    observe(control)?;
    let inner = writer
        .into_inner_with_cancellation(&|| control.poll().is_ok())
        .map_err(|_| ResolutionDagError::ProofWriterUnavailable)?;
    let bytes = inner
        .into_vec()
        .ok_or(ResolutionDagError::ProofWriterUnavailable)?;
    observe(control)?;
    let text = String::from_utf8(bytes).map_err(|_| ResolutionDagError::ProofNotUtf8)?;
    observe(control)?;
    let original_clauses = originals(clauses, control)?;
    observe(control)?;
    // Parsing is still the ordinary text codec, not the bounded binary codec.
    parse_lrat_text_into_dag(num_vars, original_clauses, &text).map(Some)
}

fn originals(
    clauses: &[Vec<Literal>],
    control: &ProofControl<'_>,
) -> Result<Vec<(u64, Vec<Literal>)>, ResolutionDagError> {
    let mut originals = Vec::new();
    for (index, clause) in clauses.iter().enumerate() {
        observe(control)?;
        let id = u64::try_from(index)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or(ResolutionDagError::TooManyClauses)?;
        originals.push((id, clause.clone()));
        observe(control)?;
    }
    Ok(originals)
}
