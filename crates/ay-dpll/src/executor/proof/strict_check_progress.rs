// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One caller-owned resource and cancellation envelope for strict proof checks.

use ay_core::{Proof, TermId};
#[cfg(feature = "proof-checker")]
use ay_proof::PartialProofCheck;
use ay_proof::{DatatypeMemberSignature, ProofCheckError, ProofQuality};

use crate::executor::Executor;

#[path = "strict_check_progress/meter.rs"]
mod meter;
use self::meter::{describe_stop_signal, executor_stopped, StrictCheckMeter};

/// Ordinary proof/context validation reserve, excluding the separately bounded
/// expensive BV-family semantic replay.
const GENERAL_CHECK_WORK: usize = 250_000_000;
const GENERAL_CHECK_BYTES: usize = 512 * 1024 * 1024;

/// Admit one maximum-size expensive BV-family lemma in addition to ordinary
/// proof validation. This is intentionally NOT multiplied by
/// `MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF`: that constant is a structural ceiling,
/// while the progress meter remains one independently bounded aggregate and
/// rejects larger mixtures when their checked cumulative precharges exceed it.
const _: () = assert!(ay_proof::MAX_EXPENSIVE_BV_WORK_PER_LEMMA <= usize::MAX as u64);
const MAX_EXPENSIVE_CHECK_WORK: usize = ay_proof::MAX_EXPENSIVE_BV_WORK_PER_LEMMA as usize;
// Const arithmetic is itself checked by rustc, while the assertions below pin
// the intended no-wrap relationship without adding production panic debt.
const MAX_CHECK_WORK: usize = GENERAL_CHECK_WORK + MAX_EXPENSIVE_CHECK_WORK;
const MAX_CHECK_BYTES: usize = GENERAL_CHECK_BYTES + ay_proof::MAX_EXPENSIVE_BV_BYTES_PER_LEMMA;

const _: () = assert!(MAX_CHECK_WORK >= GENERAL_CHECK_WORK);
const _: () = assert!(MAX_CHECK_BYTES >= GENERAL_CHECK_BYTES);
const _: () = assert!(MAX_CHECK_WORK >= MAX_EXPENSIVE_CHECK_WORK);
const _: () = assert!(MAX_CHECK_BYTES >= ay_proof::MAX_EXPENSIVE_BV_BYTES_PER_LEMMA);

/// WHICH limb of the strict-check envelope refused.
///
/// `ProofCheckError::ResourceLimit` used to collapse both. The two have
/// opposite remedies — `Cancelled` means the caller asked us to stop (widen the
/// deadline or the memory limit), `BudgetRefused` means the charge model or the
/// envelope constant is mis-calibrated — and only the collapsed variant reached
/// mandatory certification, so every downgrade read as a calibration problem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum StrictCheckRefusal {
    Cancelled,
    BudgetRefused,
}

/// Print the refusing limb's exact numbers under `--probe-strict-check`.
///
/// The limb IDENTITY now reaches callers as a distinct error variant
/// ([`StrictCheckRefusal`] -> `ProofCheckError::Cancelled` vs
/// `ProofCheckError::ResourceLimit`); this probe adds the calibration figures
/// behind it — how much of the envelope was consumed and by what delta.
/// Diagnostic only: no behaviour depends on it.
fn probe_strict_check_refusal(message: impl FnOnce() -> String) {
    if ay_core::misc_cli_flags().probe_strict_check {
        ay_core::safe_eprintln!(
            "--probe-strict-check: strict-check envelope refused: {}",
            message()
        );
    }
}

/// Charges between cancellation polls. See the note in
/// [`check_with_executor_progress`] for why the poll is not on every charge.
const STOP_POLL_INTERVAL: u64 = 1_024;

/// Run one strict check under the executor's active solve controls and one
/// aggregate, checked-arithmetic resource envelope.
pub(super) fn check_with_executor_progress(
    executor: &Executor,
    proof: &Proof,
    datatype_decls: Option<&[(String, Vec<String>)]>,
    selector_decls: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: &[DatatypeMemberSignature],
    problem_assertions: Option<&[TermId]>,
) -> Result<ProofQuality, ProofCheckError> {
    let should_stop = executor.make_should_stop();
    let mut meter = StrictCheckMeter::production();
    // The WORK/BYTE budget is charged on EVERY call (exact, fail-closed). The
    // cancellation/memory poll `executor_stopped` is NOT: its
    // `process_memory_exceeded` performs a `task_info` mach syscall per call, and
    // a large strict check emits millions of charges — that per-charge syscall
    // dominated certification wall time. Poll it only every
    // `STOP_POLL_INTERVAL` charges AND on every zero-delta charge (the explicit
    // post-validator checkpoints), which bounds interrupt/deadline/memory
    // detection latency to a tiny slice of metered work while removing ~all the
    // syscalls. Soundness is unaffected: the strict check's own footprint is
    // bounded by the per-call BYTE budget (`MAX_CHECK_BYTES`); this poll is a
    // secondary backstop, and the work budget still fails closed every call.
    let outcome = {
        let mut ops: u64 = 0;
        let mut progress = |work_delta: usize, byte_delta: usize| {
            ops = ops.wrapping_add(1);
            // Poll on the FIRST charge (so an already-active interrupt / passed
            // deadline / breached memory limit is honored immediately), on every
            // zero-delta charge (the explicit post-validator checkpoints), and every
            // STOP_POLL_INTERVAL charges thereafter (bounding mid-check detection
            // latency to a tiny slice of metered work).
            let poll_stop = ops == 1
                || (work_delta == 0 && byte_delta == 0)
                || ops.is_multiple_of(STOP_POLL_INTERVAL);
            if poll_stop {
                meter.charge_while_running(
                    work_delta,
                    byte_delta,
                    || executor_stopped(executor, &should_stop),
                    || describe_stop_signal(executor),
                )
            } else {
                meter.charge_while_running(
                    work_delta,
                    byte_delta,
                    || false,
                    || "unpolled".to_string(),
                )
            }
        };
        ay_proof::check_proof_strict_with_typed_context_and_progress(
            proof,
            &executor.ctx.terms,
            datatype_decls,
            selector_decls,
            datatype_member_signatures,
            problem_assertions,
            &mut progress,
        )
    };
    // The progress closure's scope has ended, so name WHICH meter limb refused.
    // The checker only sees a `bool`; this is the one place that knows both.
    match outcome {
        Err(ProofCheckError::ResourceLimit)
            if meter.refusal == Some(StrictCheckRefusal::Cancelled) =>
        {
            Err(ProofCheckError::Cancelled)
        }
        other => other,
    }
}

/// Run the DIAGNOSTIC (non-strict) whole-proof walk under the same
/// caller-owned envelope the mandatory strict gate already uses.
///
/// #diagnostic-envelope — WHY. `check_with_executor_progress` above bounds the
/// gate that DECIDES publication. The walk that runs beside it on every UNSAT
/// (`check_proof_partial` for `--self-check` bookkeeping, `check_proof_with_quality`
/// for `(get-info :all-statistics)`) was entirely unbounded: it bottoms out in
/// `ay_proof`'s `validate_step_with_datatypes`, which hardcodes `|_, _| true`,
/// so no interrupt, no solve deadline and no memory limit could stop it.
///
/// MEASURED, on the proof deductive-checks's datatype+quantifier encoding produces for
/// `datatype_ne_refutation::equality_direction_is_unchanged`: 126,548 steps /
/// 393,087,456 clause literals / widest clause 28,026, walked in 474.565 s, then
/// a 72,982-step / 392,818,556-literal proof walked in 481.779 s, then walked a
/// THIRD time by `check_proof_with_quality` — all of it AFTER the caller's 30 s
/// budget had already expired and its 130 s hang watchdog had already raised the
/// interrupt. The consumer saw a solve that never returned.
///
/// Two things change here and nothing else:
///  * the two walks become ONE (`check_proof_partial_with_quality`, which has
///    been in `ay_proof` since #proof-tax with zero callers — same checker, same
///    step order, same hole handling, same first-error semantics);
///  * that one walk is metered and cancellable, exactly like the strict gate.
///
/// FAIL-CLOSED. A refusal surfaces as `ProofCheckError::ResourceLimit` /
/// `Cancelled`, which the caller records as a check FAILURE: `proof_check_ok`
/// goes false and no `ProofQuality` is published. That can only WITHDRAW a
/// self-certification, never grant one, so no verdict can become more accepting
/// than it is today.
#[cfg(feature = "proof-checker")]
pub(in crate::executor) fn check_partial_with_executor_progress(
    executor: &Executor,
    proof: &Proof,
    want_quality: WantQuality,
) -> MeteredPartialCheck {
    check_partial_with_executor_progress_and_meter(
        executor,
        proof,
        want_quality,
        StrictCheckMeter::production(),
    )
}

/// [`check_partial_with_executor_progress`] with an explicit meter, so tests
/// can drive the BUDGET limb without a 350M-charge proof. Production has
/// exactly one caller, the wrapper above, which passes
/// [`StrictCheckMeter::production`].
#[cfg(feature = "proof-checker")]
fn check_partial_with_executor_progress_and_meter(
    executor: &Executor,
    proof: &Proof,
    want_quality: WantQuality,
    mut meter: StrictCheckMeter,
) -> MeteredPartialCheck {
    let should_stop = executor.make_should_stop();
    let (summary, quality, error) = {
        let mut ops: u64 = 0;
        let mut progress = |work_delta: usize, byte_delta: usize| {
            ops = ops.wrapping_add(1);
            let poll_stop = ops == 1
                || (work_delta == 0 && byte_delta == 0)
                || ops.is_multiple_of(STOP_POLL_INTERVAL);
            if poll_stop {
                meter.charge_while_running(
                    work_delta,
                    byte_delta,
                    || executor_stopped(executor, &should_stop),
                    || describe_stop_signal(executor),
                )
            } else {
                meter.charge_while_running(
                    work_delta,
                    byte_delta,
                    || false,
                    || "unpolled".to_string(),
                )
            }
        };
        match want_quality {
            WantQuality::Yes => ay_proof::check_proof_partial_with_quality_and_progress(
                proof,
                &executor.ctx.terms,
                &mut progress,
            ),
            // #diagnostic-envelope AMENDMENT. The fused quality walk ends with
            // `quantifier::validate_sko_forall_uniqueness`, an UNMETERED
            // whole-proof Skolem traversal that legacy `check_proof_partial`
            // never ran. The two callers that discard the quality must not pay
            // for it -- one of them is the hottest walk in this whole lane --
            // so they take the quality-free metered entry point, which is
            // `check_proof_partial` plus a meter and nothing else.
            WantQuality::No => {
                let (summary, error) = ay_proof::check_proof_partial_with_progress(
                    proof,
                    &executor.ctx.terms,
                    &mut progress,
                );
                (summary, None, error)
            }
        }
    };
    // NAME the refusing party, do not merely name the error. `ResourceLimit`
    // also arrives from budgets INSIDE the checker (`checker::lra_farkas`,
    // `checker::nia_*`), which are a property of the proof and were already
    // reachable before this envelope existed. `meter.refusal` is the only thing
    // that knows the difference, and its scope has just ended.
    let envelope_refusal = meter.refusal;
    let error = match (error, envelope_refusal) {
        (Some(ProofCheckError::ResourceLimit), Some(StrictCheckRefusal::Cancelled)) => {
            Some(ProofCheckError::Cancelled)
        }
        (other, _) => other,
    };
    MeteredPartialCheck {
        summary,
        quality,
        error,
        envelope_refusal,
    }
}

/// Whether a metered diagnostic walk should also measure `ProofQuality`.
///
/// A bare `bool` at three call sites is exactly the kind of parameter that gets
/// passed the wrong way round once and then stays wrong, and here the wrong way
/// round silently re-adds the unmetered Skolem walk this amendment removes.
#[cfg(feature = "proof-checker")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum WantQuality {
    Yes,
    No,
}

/// One metered diagnostic walk's outcome, INCLUDING who refused.
///
/// #diagnostic-envelope AMENDMENT — WHY `envelope_refused` EXISTS. Bounding the
/// walk turned "this proof does not check out" into two very different claims
/// that the `Option<ProofCheckError>` alone cannot separate:
///
///  * the checker reached a VERDICT and the verdict is "defective" — a bad
///    resolution link, a missing premise, a non-terminal empty clause;
///  * the checker reached NO verdict because the caller-owned envelope stopped
///    it (interrupt / solve deadline / memory limit, or this envelope's own
///    work/byte budget).
///
/// A caller that repairs the proof on a defect must not repair it on a refusal:
/// the repair is precisely the unbounded post-stop work the envelope was added
/// to eliminate. Measured on deductive-checks's `datatype_ne_refutation::t_dbl_one_eq`,
/// collapsing the two fired `build_unsat_assembly`'s strip-and-rebuild ladder
/// 12 times per solve, every one of them with `err = Cancelled`, one of them on
/// a 199,149-step proof, all of it after the stop signal had already been
/// raised.
///
/// `ResourceLimit` on its own is NOT sufficient to make that distinction: the
/// checker's own per-step budgets (`checker::lra_farkas`, `checker::nia_*`)
/// raise it too, and those predate the envelope. Only the meter knows whether
/// IT was the one that refused, so it reports that here as a separate fact.
#[cfg(feature = "proof-checker")]
pub(in crate::executor) struct MeteredPartialCheck {
    /// Step accounting, always populated (`check_proof_partial`'s contract).
    pub(in crate::executor) summary: PartialProofCheck,
    /// `Some` only when quality was requested AND the proof validated cleanly
    /// with no hole steps.
    pub(in crate::executor) quality: Option<ProofQuality>,
    /// The first validation error, or the refusal.
    pub(in crate::executor) error: Option<ProofCheckError>,
    /// `Some` when the CALLER-OWNED envelope refused the walk rather than the
    /// checker reaching a verdict about the proof — and WHICH limb refused,
    /// because the two limbs have opposite PUBLICATION consequences:
    ///
    ///  * `Cancelled` — `executor_stopped` fired (interrupt / solve deadline /
    ///    executor memory / process memory). `stop_declines_unsat_publication`
    ///    tests the same four signals, so on this limb the solve is already
    ///    being converted to `unknown`; nothing downstream can publish.
    ///  * `BudgetRefused` — none of those signals is asserted; only this
    ///    envelope's aggregate work/byte budget was exceeded. The solve
    ///    publishes normally, and every acceptance downstream still runs its
    ///    own separately-metered `check_strict_unsat_presentation` walk over
    ///    whatever chain is presented.
    ///
    /// Both limbs classify the walk `Undetermined` (nothing was learned about
    /// the proof), but only the second leaves publication live — which is why
    /// the limb itself is reported, not a collapsed `bool`.
    pub(in crate::executor) envelope_refusal: Option<StrictCheckRefusal>,
}

#[cfg(feature = "proof-checker")]
impl MeteredPartialCheck {
    /// Whether the caller-owned envelope (either limb) refused the walk.
    pub(in crate::executor) fn envelope_refused(&self) -> bool {
        self.envelope_refusal.is_some()
    }
}

/// Run the whole-proof REVERT GATE (`ay_proof::check_proof`) under the
/// executor's envelope.
///
/// #diagnostic-envelope — `Executor::split_euf_congruence_lemmas`,
/// `split_shadowed_store_equality_lemmas`, the rewritten-assertion bridge and
/// the congruence-explanation rebuild all use the same idiom: rebuild part of a
/// proof, re-check the WHOLE proof, and put the original back if the check
/// fails. On a triangular resolution proof that whole-proof re-check is the
/// dominant cost of the solve, and it ran with no meter and no cancellation
/// poll at all.
///
/// A refused/cancelled check returns `Err`, which is precisely the branch those
/// gates already take to discard their surgery and restore the original proof.
pub(in crate::executor) fn check_proof_gate_with_executor_progress(
    executor: &Executor,
    proof: &Proof,
) -> Result<(), ProofCheckError> {
    let should_stop = executor.make_should_stop();
    check_proof_gate_under_controls(
        proof,
        &executor.ctx.terms,
        &should_stop,
        executor.memory_limit(),
    )
}

/// As [`check_proof_gate_with_executor_progress`], for the surgery passes that
/// already hold `&mut ctx.terms` and therefore cannot also borrow the executor.
/// The caller lifts the two controls out first (`make_should_stop()`,
/// `memory_limit()`); both are owned values, so no borrow conflict remains.
pub(in crate::executor) fn check_proof_gate_under_controls(
    proof: &Proof,
    terms: &ay_core::TermStore,
    should_stop: &dyn Fn() -> bool,
    memory_limit: Option<usize>,
) -> Result<(), ProofCheckError> {
    let stopped = || {
        should_stop()
            || crate::memory::memory_exceeded(memory_limit)
            || ay_sys::process_memory_exceeded()
    };
    let mut meter = StrictCheckMeter::production();
    let outcome = {
        let mut ops: u64 = 0;
        let mut progress = |work_delta: usize, byte_delta: usize| {
            ops = ops.wrapping_add(1);
            let poll_stop = ops == 1
                || (work_delta == 0 && byte_delta == 0)
                || ops.is_multiple_of(STOP_POLL_INTERVAL);
            if poll_stop {
                meter.charge_while_running(work_delta, byte_delta, &stopped, || {
                    "interrupt, solve deadline, or memory limit".to_string()
                })
            } else {
                meter.charge_while_running(
                    work_delta,
                    byte_delta,
                    || false,
                    || "unpolled".to_string(),
                )
            }
        };
        ay_proof::check_proof_with_progress(proof, terms, &mut progress)
    };
    match outcome {
        Err(ProofCheckError::ResourceLimit)
            if meter.refusal == Some(StrictCheckRefusal::Cancelled) =>
        {
            Err(ProofCheckError::Cancelled)
        }
        other => other,
    }
}

#[cfg(test)]
#[path = "strict_check_progress/tests.rs"]
mod tests;
