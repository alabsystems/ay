// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One caller-owned resource and cancellation envelope for strict proof checks.

use ay_core::{Proof, TermId};
use ay_proof::{DatatypeMemberSignature, ProofCheckError, ProofQuality};

use crate::executor::Executor;

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
enum StrictCheckRefusal {
    Cancelled,
    BudgetRefused,
}

struct StrictCheckMeter {
    work: usize,
    bytes: usize,
    max_work: usize,
    max_bytes: usize,
    refusal: Option<StrictCheckRefusal>,
}

fn executor_stopped(executor: &Executor, should_stop: &impl Fn() -> bool) -> bool {
    should_stop()
        || crate::memory::memory_exceeded(executor.memory_limit())
        || ay_sys::process_memory_exceeded()
}

impl StrictCheckMeter {
    fn production() -> Self {
        Self::with_limits(MAX_CHECK_WORK, MAX_CHECK_BYTES)
    }

    fn with_limits(max_work: usize, max_bytes: usize) -> Self {
        Self {
            work: 0,
            bytes: 0,
            max_work,
            max_bytes,
            refusal: None,
        }
    }

    fn charge(&mut self, work_delta: usize, byte_delta: usize) -> bool {
        let Some(work) = self.work.checked_add(work_delta) else {
            return false;
        };
        let Some(bytes) = self.bytes.checked_add(byte_delta) else {
            return false;
        };
        if work > self.max_work || bytes > self.max_bytes {
            return false;
        }
        self.work = work;
        self.bytes = bytes;
        true
    }

    fn charge_while_running(
        &mut self,
        work_delta: usize,
        byte_delta: usize,
        stopped: impl FnOnce() -> bool,
    ) -> bool {
        if stopped() {
            self.refusal.get_or_insert(StrictCheckRefusal::Cancelled);
            probe_strict_check_refusal(|| {
                "cancelled: interrupt, solve deadline, or memory limit".to_string()
            });
            return false;
        }
        if self.charge(work_delta, byte_delta) {
            return true;
        }
        self.refusal
            .get_or_insert(StrictCheckRefusal::BudgetRefused);
        probe_strict_check_refusal(|| {
            format!(
                "budget: work {}+{} of {}, bytes {}+{} of {}",
                self.work, work_delta, self.max_work, self.bytes, byte_delta, self.max_bytes
            )
        });
        false
    }
}

/// Print the refusing limb's exact numbers under `AY_PROBE_STRICT_CHECK`.
///
/// The limb IDENTITY now reaches callers as a distinct error variant
/// ([`StrictCheckRefusal`] -> `ProofCheckError::Cancelled` vs
/// `ProofCheckError::ResourceLimit`); this probe adds the calibration figures
/// behind it — how much of the envelope was consumed and by what delta.
/// Diagnostic only: no behaviour depends on it.
fn probe_strict_check_refusal(message: impl FnOnce() -> String) {
    if ay_core::misc_cli_flags().probe_strict_check {
        eprintln!(
            "--probe-strict-check: strict-check envelope refused: {}",
            message()
        );
    }
}

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
    const STOP_POLL_INTERVAL: u64 = 1_024;
    let mut ops: u64 = 0;
    let mut progress = |work_delta: usize, byte_delta: usize| {
        ops = ops.wrapping_add(1);
        // Poll on the FIRST charge (so an already-active interrupt / passed
        // deadline / breached memory limit is honored immediately), on every
        // zero-delta charge (the explicit post-validator checkpoints), and every
        // STOP_POLL_INTERVAL charges thereafter (bounding mid-check detection
        // latency to a tiny slice of metered work).
        let poll_stop =
            ops == 1 || (work_delta == 0 && byte_delta == 0) || ops % STOP_POLL_INTERVAL == 0;
        if poll_stop {
            meter.charge_while_running(work_delta, byte_delta, || {
                executor_stopped(executor, &should_stop)
            })
        } else {
            meter.charge_while_running(work_delta, byte_delta, || false)
        }
    };
    let outcome = ay_proof::check_proof_strict_with_typed_context_and_progress(
        proof,
        &executor.ctx.terms,
        datatype_decls,
        selector_decls,
        datatype_member_signatures,
        problem_assertions,
        &mut progress,
    );
    // Release the meter borrow, then name WHICH limb refused. The checker only
    // sees a `bool`, so the distinction has to be recovered here — this is the
    // one place that knows both limbs.
    drop(progress);
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
mod tests {
    use super::*;
    use crate::api::{Logic, Solver, Sort};
    use std::cell::Cell;
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    #[test]
    fn aggregate_meter_refuses_cross_call_limit_and_overflow() {
        let mut meter = StrictCheckMeter::with_limits(10, 8);
        assert!(meter.charge(6, 5));
        assert!(meter.charge(4, 3));
        assert!(!meter.charge(1, 0));

        let mut overflow = StrictCheckMeter::with_limits(usize::MAX, usize::MAX);
        assert!(overflow.charge(usize::MAX, usize::MAX));
        assert!(!overflow.charge(1, 0));
        assert!(!overflow.charge(0, 1));
    }

    #[test]
    fn control_is_polled_on_every_charge_including_zero_delta() {
        let polls = Cell::new(0usize);
        let mut meter = StrictCheckMeter::with_limits(10, 10);
        assert!(meter.charge_while_running(1, 1, || {
            polls.set(polls.get() + 1);
            false
        }));
        assert!(!meter.charge_while_running(0, 0, || {
            polls.set(polls.get() + 1);
            true
        }));
        assert_eq!(polls.get(), 2);
    }

    #[test]
    fn executor_strict_derivation_check_polls_active_interrupt() {
        let mut executor = Executor::new();
        executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);

        assert_eq!(
            executor.check_proof_strict_derivation_with_datatypes(&Proof::new()),
            Err(ProofCheckError::Cancelled)
        );
    }

    #[test]
    fn executor_strict_check_polls_active_interrupt() {
        let mut executor = Executor::new();
        executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);

        assert_eq!(
            executor.check_proof_strict_with_datatypes(&Proof::new()),
            Err(ProofCheckError::Cancelled)
        );
    }

    #[test]
    fn executor_strict_derivation_check_polls_active_deadline() {
        let mut executor = Executor::new();
        executor.set_solve_controls(None, Some(ay_core::time::Instant::now()));

        assert_eq!(
            executor.check_proof_strict_derivation_with_datatypes(&Proof::new()),
            Err(ProofCheckError::Cancelled)
        );
    }

    #[test]
    fn executor_strict_derivation_check_polls_executor_memory_limit() {
        let mut executor = Executor::new();
        executor.set_memory_limit(Some(1));

        assert_eq!(
            executor.check_proof_strict_derivation_with_datatypes(&Proof::new()),
            Err(ProofCheckError::Cancelled)
        );
    }

    /// Regression for the verification condition `(x & 15) <u 16` over a free
    /// 64-bit `x`, as emitted by the proof-IR frontend.
    ///
    /// The generated three-step proof contains one proof-producing
    /// `BvBitBlast` lemma. Its published 768 MiB conservative precharge used to
    /// exceed this caller's entire 512 MiB envelope, so 29 proof-surgery and
    /// publication probes all rejected the same valid proof as `ResourceLimit`
    /// (the old pre-mint statistics snapshot reported only 28).
    #[test]
    fn strict_publication_admits_one_wide_bv_bitblast_lemma() {
        let mut solver = Solver::try_new(Logic::All).expect("solver construction");
        solver.set_produce_proofs(true);
        let x = solver.declare_const("resource_mask_x", Sort::bitvec(64));
        let mask = solver.bv_const(15, 64);
        let bound = solver.bv_const(16, 64);
        let masked = solver.bvand(x, mask);
        let comparison = solver.bvult(masked, bound);

        // Match the proof-IR frontend's canonical Bool -> BV1 -> Bool schema
        // normalization.
        let one = solver.bv_const(1, 1);
        let zero = solver.bv_const(0, 1);
        let encoded = solver.ite(comparison, one, zero);
        let holds = solver.eq(encoded, one);
        let negated = solver.not(holds);
        solver.assert_term(negated);

        let result = solver.check_sat();
        assert!(
            result.is_unsat(),
            "the mask theorem must publish UNSAT, not {:?}: {:?}",
            solver.unknown_reason(),
            solver.statistics()
        );
        assert!(
            result.was_unsat_strictly_verified(),
            "publication must consume the strict proof capability, not an independent fallback"
        );
        assert!(!result.was_unsat_independently_verified());
        assert_eq!(
            solver.last_proof().map(|proof| proof.len()),
            Some(3),
            "the regression must continue exercising the wide BV lemma proof"
        );
        let invocations = solver
            .statistics()
            .get_int("proof.strict_check_invocations")
            .expect("strict-check invocation counter");
        // The final published snapshot includes the bounded BV-authored repair
        // path, its fixed post-repair gates, and certificate minting. Before the
        // envelope fix, the all-member rejection storm took 29 checks and never
        // published UNSAT; successful promotion stays within the current
        // 17-check bound while permitting future removal of redundant gates.
        assert!(
            invocations <= 17,
            "accepted proof exceeded the bounded publication pipeline: {invocations}"
        );
    }
}
