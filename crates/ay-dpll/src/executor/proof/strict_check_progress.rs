// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One caller-owned resource and cancellation envelope for strict proof checks.

use ay_core::{Proof, TermId};
use ay_proof::PartialProofCheck;
use ay_proof::{DatatypeMemberSignature, ProofCheckError, ProofQuality};

use crate::executor::Executor;

#[path = "strict_check_progress/meter.rs"]
mod meter;
use self::meter::{describe_stop_signal, executor_stopped, typed_stop_signal, StrictCheckMeter};

#[path = "strict_check_progress/poll.rs"]
mod poll;
use poll::strided_memory_poll;

#[path = "strict_check_progress/solve_stop.rs"]
mod solve_stop;

#[path = "strict_check_progress/render_stop.rs"]
mod render_stop;
#[cfg(test)]
pub(in crate::executor) use render_stop::RENDER_CHECKS;

#[path = "strict_check_progress/caller.rs"]
mod caller;
pub(super) use caller::check_with_caller_progress;

#[path = "strict_check_progress/bounded.rs"]
mod bounded;
pub(in crate::executor::proof) use bounded::check_bounded_with_executor_progress;

#[path = "strict_check_progress/gate.rs"]
mod gate;
pub(in crate::executor) use gate::{
    check_proof_gate_under_controls, check_proof_gate_with_executor_progress,
};

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

/// Maximum callback interval between operating-system memory observations.
/// Interrupt and deadline controls are checked on every callback (the
/// deadline through a `DeadlinePoll`, `make_strict_check_stop`).
const STOP_POLL_INTERVAL: u64 = 1_024;

/// Whether the executor's stop signals (interrupt / solve deadline / memory)
/// are asserted RIGHT NOW — the exact poll a strict walk performs on its
/// first charge.
///
/// #strict-walk-memo consults this before answering from a stored verdict: a
/// stopping caller must observe the same `Cancelled` outcome a real walk
/// would produce (the walk's first-charge poll cancels it immediately), and a
/// cancellation must keep its calibrated downstream meaning — revert, nothing
/// learned about the document, and retain the observed owner stop. Answering from the cache while stopping would
/// let cached knowledge change WHAT a dying solve decides.
pub(in crate::executor) fn executor_stop_signals_asserted(executor: &Executor) -> bool {
    let should_stop = executor.make_strict_check_stop();
    executor_stopped(executor, &should_stop)
}

/// WHY THERE IS NO SECOND, TIGHTER PRICE (#eqdv-second-price-retired).
///
/// [`MAX_CHECK_WORK`] prices ONE strict walk. A tighter second price used to
/// sit beside it — `REPEATABLE_CHECK_WORK = GENERAL_CHECK_WORK / 2` (125M) —
/// because the pipeline did not run one walk: every assembly re-ran the
/// surgery revert gates and the mint's presentation over the whole document.
/// Its derivation was explicit: "~60 repetitions of a walk at this bound cost
/// under three seconds", i.e. `price * 60 ~= 7.5G` metered units.
///
/// #strict-walk-memo removed the repetition. RE-MEASURED on the same 900-file
/// QF_IDL sample the price was set on (seed 20260824, `AY_CENSUS=1 ay solve
/// --no-proof -T:10`, gate-level instrumentation, 189 asks over 117 files):
/// the gate is asked **1 or 2 times per solve, never more** (45 files once,
/// 72 twice), and **27 of the 29** asks the 125M price refused were memo
/// HITS — the walk was already paid by another consumer, so the refusal saved
/// nothing on the ask it refused. Re-deriving at the same three-second
/// constraint gives `7.5G / 2 = 3.75G`, **10.7x [`MAX_CHECK_WORK`]**: the
/// derived price is above the ceiling, so the ceiling binds.
///
/// The population agrees. Admitted costs run continuously 1.2M -> 120.5M and
/// refused ones 127.5M -> 334.7M, with no gap at 125M (the cheapest refusal
/// was 2.0% over the price). The only structural boundary there is the
/// envelope itself: a TYPED verdict means the checker walked the whole
/// document and objected to a named step, which it can only do inside
/// [`MAX_CHECK_WORK`]. So the `EqDiffVar` commit gate now prices a typed
/// verdict against nothing but the envelope that produced it, and what still
/// reverts is unchanged: `ResourceLimit` and `Cancelled`.
///
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
    check_with_executor_progress_reporting_work(
        executor,
        proof,
        datatype_decls,
        selector_decls,
        datatype_member_signatures,
        problem_assertions,
    )
    .0
}

/// As [`check_with_executor_progress`], additionally reporting the aggregate
/// WORK the meter recorded for the walk.
///
/// DETERMINISTIC by construction, and that is the property the figure exists
/// for: every charge the meter sums is a structural count of the document and
/// the term universe (`.len()`s, step counts, and the flat per-lemma
/// precharges in `ay_proof::checker::bv_bitblast`), never a clock, a load
/// sample, a thread count or an allocator capacity — the byte limb takes the
/// `.capacity()`s, the work limb never does. So the same document on the same
/// store reports the same figure on any machine at any load. VERIFIED, not
/// asserted: `inf-bakery-mutex-18` reports the identical ten-walk work trace
/// unloaded and under an 8-way sweep, 3/3 reps each.
///
/// Reporting only: the check's outcome, envelope and cancellation behaviour
/// are byte-identical. #strict-walk-memo replays the ORIGINAL walk's figure
/// for a memo hit, so a replayed verdict carries a replayed cost.
pub(super) fn check_with_executor_progress_reporting_work(
    executor: &Executor,
    proof: &Proof,
    datatype_decls: Option<&[(String, Vec<String>)]>,
    selector_decls: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: &[DatatypeMemberSignature],
    problem_assertions: Option<&[TermId]>,
) -> (Result<ProofQuality, ProofCheckError>, usize) {
    let should_stop = executor.make_strict_check_stop();
    check_strict_under_controls(
        executor,
        StrictWalk {
            proof,
            datatype_decls,
            selector_decls,
            datatype_member_signatures,
            problem_assertions,
        },
        &should_stop,
    )
}

/// The strict walk's document and context, as the checker reads them.
pub(super) struct StrictWalk<'a> {
    pub(super) proof: &'a Proof,
    pub(super) datatype_decls: Option<&'a [(String, Vec<String>)]>,
    pub(super) selector_decls: Option<&'a [(String, Vec<String>)]>,
    pub(super) datatype_member_signatures: &'a [DatatypeMemberSignature],
    pub(super) problem_assertions: Option<&'a [TermId]>,
}

/// [`check_with_executor_progress_reporting_work`] with the cheap stop
/// control lifted out, so a test can raise it at an exact callback.
///
/// #completed-check-accepted — the stop is honoured when the walk is admitted
/// and at every callback the checker makes before or during its steps, and
/// NEVER after the final step. This wrapper used to add one more full stop
/// poll after a successful walk; with the checker's own trailing polls it
/// turned walks that had validated every step into `Cancelled` whenever the
/// deadline landed after the last step, so the verdict on a finished
/// validation depended on the clock. A completed validation is a fact about
/// the document and is returned as one. What stays final is a refusal the
/// walk itself observed ([`StrictCheckMeter::settle`]).
fn check_strict_under_controls(
    executor: &Executor,
    walk: StrictWalk<'_>,
    should_stop: &dyn Fn() -> bool,
) -> (Result<ProofQuality, ProofCheckError>, usize) {
    check_with_caller_progress(executor, walk, should_stop, &mut |_, _| true)
}

/// Keep a cancelled walk's typed stop on the executor, so publication reports
/// the stop even after its signal has cleared (P4a.1).
fn record_walk_stop(executor: &Executor, meter: &StrictCheckMeter) {
    if let Some(stop) = meter.stop {
        executor.note_certification_stop(stop);
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
fn check_partial_with_executor_progress_and_meter(
    executor: &Executor,
    proof: &Proof,
    want_quality: WantQuality,
    meter: StrictCheckMeter,
) -> MeteredPartialCheck {
    let should_stop = executor.make_strict_check_stop();
    check_partial_under_controls(executor, proof, want_quality, meter, &should_stop)
}

/// The diagnostic walk under explicit controls. Like the strict gate
/// (#completed-check-accepted), the stop is polled when the walk is admitted
/// and at the checker's own callbacks, never after a walk that validated every
/// step: the partial checker makes no callback after its final step, and the
/// post-walk poll this wrapper used to add is gone. The admission poll keeps
/// a caller that is ALREADY stopping from starting a walk whose steps might
/// never call back (`ProofStep::Resolution` is validated unmetered).
fn check_partial_under_controls(
    executor: &Executor,
    proof: &Proof,
    want_quality: WantQuality,
    mut meter: StrictCheckMeter,
    should_stop: &dyn Fn() -> bool,
) -> MeteredPartialCheck {
    let stopped = strided_memory_poll(&should_stop, executor.memory_limit());
    let (summary, quality, error) = {
        let mut progress = |work_delta: usize, byte_delta: usize| {
            meter.charge_while_running(
                work_delta,
                byte_delta,
                || stopped.poll(),
                || describe_stop_signal(executor),
                || {
                    Some(
                        stopped
                            .reason()
                            .unwrap_or_else(|| typed_stop_signal(executor)),
                    )
                },
            )
        };
        if progress(0, 0) {
            match want_quality {
                WantQuality::Yes => ay_proof::check_proof_partial_with_quality_and_progress(
                    proof,
                    &executor.ctx.terms,
                    &mut progress,
                ),
                // #diagnostic-envelope AMENDMENT. The fused quality walk ends
                // with `quantifier::validate_sko_forall_uniqueness`, an
                // UNMETERED whole-proof Skolem traversal that legacy
                // `check_proof_partial` never ran. The two callers that discard
                // the quality must not pay for it -- one of them is the hottest
                // walk in this whole lane -- so they take the quality-free
                // metered entry point, which is `check_proof_partial` plus a
                // meter and nothing else.
                WantQuality::No => {
                    let (summary, error) = ay_proof::check_proof_partial_with_progress(
                        proof,
                        &executor.ctx.terms,
                        &mut progress,
                    );
                    (summary, None, error)
                }
            }
        } else {
            let summary = PartialProofCheck {
                total_steps: proof.steps.len() as u32,
                ..Default::default()
            };
            (summary, None, Some(ProofCheckError::ResourceLimit))
        }
    };
    // NAME the refusing party, do not merely name the error. `ResourceLimit`
    // also arrives from budgets INSIDE the checker (`checker::lra_farkas`,
    // `checker::nia_*`), which are a property of the proof and were already
    // reachable before this envelope existed. `meter.refusal` is the only thing
    // that knows the difference, and its scope has just ended.
    let envelope_refusal = meter.refusal;
    record_walk_stop(executor, &meter);
    let error = meter.settle(error.map_or(Ok(()), Err)).err();
    let quality = quality.filter(|_| error.is_none());
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

impl MeteredPartialCheck {
    /// Whether the caller-owned envelope (either limb) refused the walk.
    pub(in crate::executor) fn envelope_refused(&self) -> bool {
        self.envelope_refusal.is_some()
    }
}

#[cfg(test)]
#[path = "strict_check_progress/tests.rs"]
mod tests;

#[cfg(test)]
#[path = "strict_check_progress/solve_stop_tests.rs"]
mod solve_stop_tests;

#[cfg(test)]
#[path = "strict_check_progress/completion_tests.rs"]
mod completion_tests;

#[cfg(test)]
#[path = "strict_check_progress/original_owner_tests.rs"]
mod original_owner_tests;
