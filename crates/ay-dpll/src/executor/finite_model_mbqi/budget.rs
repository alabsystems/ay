// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite-model lane budgets and session accounting.

use ay_core::time::Instant;
use std::time::Duration;

/// Maximum synth/verify refinement rounds before failing closed.
///
/// Each round costs one counterexample probe per universal plus one ground
/// re-solve. The declined queries converge in a handful of rounds (the pinned
/// counterexample search excludes one model value per round and the satisfying
/// region of these invariants is large), so a small cap buys the decisions
/// without letting a pathological instance burn the query budget.
pub(super) const MAX_FINITE_MODEL_ROUNDS: usize = 12;

/// Per-sub-solve budget in milliseconds.
///
/// Both obligations are quantifier-free and mostly ground: `verify_i` has one
/// free constant per binder and `confirm` is `G` under a near-total pin set.
/// A short budget keeps a hard instance from consuming the enclosing query.
pub(super) const FINITE_MODEL_PROBE_MS: u64 = 2_000;

/// Wall budget for the SUB-SOLVES of one invocation of this lane
/// (#witness-check-cost).
///
/// NOT a bound on the invocation's total spend — review measured invocations at
/// 2,981 ms (float-to-double1) and 3,582 ms (rlim_invariant) against this
/// 2,500 ms figure, and the original wording claimed the stronger property. The
/// ground re-solve sits INSIDE the account window but OUTSIDE `sub_solve_ms()`:
/// it is charged to the account, so the session rule still sees it, but it is
/// not capped by this constant. Read this as "the budget every sub-solve draws
/// from", not "the most an invocation can cost".
///
/// WHY A LANE-WIDE CAP AND NOT A PER-SUB-SOLVE ONE.
/// [`FINITE_MODEL_PROBE_MS`] already caps each sub-solve, but a pass runs many:
/// one or two refutations per universal, a counterexample probe, the residual
/// `confirm` solve, and the witness probe — and
/// [`Executor::try_finite_model_forall_refinement`] runs up to
/// [`MAX_FINITE_MODEL_ROUNDS`] passes. The per-sub-solve cap therefore bounds a
/// check-sat's exposure at tens of seconds.
///
/// WHERE 2.5 s COMES FROM. Measured, not guessed: with the budget removed and
/// `--debug-cert` reporting every invocation's wall cost, the invocations that
/// CERTIFY cost
///
/// ```text
///   file                     n     mean    p90    max
///   rlim_invariant         582    314ms  809ms  2456ms
///   float-to-double1       155    659ms 1398ms  1789ms
///   exp_loop                31   1080ms 1491ms  2349ms
/// ```
///
/// so 2.5 s admits every certificate any of the three produced, while the
/// DECLINED invocations on `exp_loop` (mean 881 ms, p90 4.5 s, max 6.0 s) are
/// exactly what it truncates. A cap of 1 s was tried first and cost 25% of
/// `float-to-double1`'s certificates and 8% of `rlim_invariant`'s — measured,
/// on the division that must hold.
///
/// FAIL CLOSED. Exhausting the budget declines the pass, i.e. publishes the
/// `unknown` the lane existed to avoid — never a weaker check and never a
/// verdict this lane would not otherwise have been entitled to.
///
/// # RAISING THIS DOES NOT BUY THE `exp_loop` NEGATED EXISTENTIALS. MEASURED.
///
/// The obvious reading of the numbers above — declines cost 4.5 s against a
/// 2.5 s cap, so widen the cap — was tried under `--fmq-lane-budget-ms` /
/// `--fmq-probe-ms` and is a NET LOSS. Two findings, both from interleaved
/// same-day runs:
///
/// * Raising THIS constant alone converts nothing. At 8,000 ms the three
///   sampled `exp_loop` negated existentials still published `unknown`, and
///   two of them got 2.4x MORE expensive (q195: 6.2 s -> 14.6 s) because the
///   pass now runs to a later decline. [`FINITE_MODEL_PROBE_MS`] is what
///   binds: it is the cap the single Float32 `fp.div` refutation overruns.
/// * Raising BOTH does convert — and still loses. At 10,000/8,000 ms on the
///   real incremental file, 33 of 35 `unknown` became `sat`, but the file
///   reached 45 FEWER check-sats in the same wall, for 283 answered against
///   the baseline's 295. In an incremental division the currency is
///   throughput, and a per-invocation budget spends it.
///
/// The wall was never economic. The lane's sub-solves were slow because ONE
/// Float32 `fp.div` bit-blasts to ~89k variables; encoding division by a
/// power of two as the reciprocal multiply (`ay_fp::div_pow2`) drops that to
/// ~18k, and those queries then certify INSIDE this 2,500 ms cap with wall to
/// spare. Fix the cost, not the budget.
pub(super) const FINITE_MODEL_LANE_BUDGET_MS: u64 = 2_500;

/// Speculative capital: what the lane may spend on DECLINES in one session
/// before it has to have paid for itself (#witness-check-cost).
///
/// The per-invocation cap alone does not fix an incremental trace, because the
/// trace multiplies it: 1,645 check-sats times a per-query cap is still a
/// budget-sized number. The session rule is
///
/// ```text
///   declined_spend <= FINITE_MODEL_LANE_SEED_MS + certified_spend
/// ```
///
/// — after the seed, the lane may spend on failures at most what it has already
/// spent on successes.
///
/// WHY THIS STATISTIC. It is scale-free: no millisecond threshold has to track
/// how fast the host is. And it separates the two divisions by two orders of
/// magnitude. Measured with the budget removed:
///
/// ```text
///   file                declined     certified   ratio needed
///   float-to-double1      16.6s        102.1s          0.16
///   rlim_invariant        61.8s        183.0s          0.34
///   exp_loop             359.4s         33.5s         10.73
/// ```
///
/// A ratio of 1 cuts `exp_loop`'s lane spend to 7% of what it was. It does NOT
/// leave both FP files alone — review measured that claim false for
/// `rlim_invariant`: its peak deficit reaches 20,057 ms against the 20,000 ms
/// seed, the latch trips at invocation ~1062, 1,297 invocations are refused,
/// and it keeps 159 certificates rather than the 582 claimed here.
/// float-to-double1 does match (153 kept, 0 latch events).
///
/// FPArith survives that at -1 answer and still clears the bar, but the margin
/// is 6, so the safety argument for this constant is empirical, not structural.
/// Note also that the latch is ABSORBING: `finite_model_lane_open` returns
/// `None` before any settle, so once a session's lane closes it can never earn
/// its way back open.
///
/// The seed is deliberately several invocations' worth: with a seed near the
/// per-invocation cap, one expensive first decline would close the lane for the
/// whole session before it ever had a chance to certify.
///
/// # THE LATCH IS WHAT `exp_loop`'S REMAINING UNKNOWNS HIT — AND OPENING IT
/// # LOSES. MEASURED.
///
/// After `ay_fp::div_pow2` made the sub-solves cheap, `exp_loop` still
/// published 231 `unknown` over its 1,645 check-sats, and `--debug-cert`
/// attributes them here rather than to any per-invocation cap: the lane logs
/// `lane closed` 265 times at `declined=47,858ms allowance=46,420ms`, and
/// because the latch is absorbing it never reopens.
///
/// Opening it is not the fix. With `--fmq-seed-ms 600000` at -T:1200, the
/// per-index yield does improve — 123 `unknown` instead of 231 — but the lane
/// spends so much on declines that the file no longer FINISHES: 1,303
/// check-sats reached instead of 1,645, and 1,180 answered against 1,414. A
/// net loss of 234, from the constant this doc most invites raising.
///
/// So the residue behind this latch is not cheap wall away. It needs the
/// declines themselves to get cheaper — the same lesson as
/// [`FINITE_MODEL_LANE_BUDGET_MS`] — or a session rule that can tell a
/// productive query from an unproductive one before it has paid.
pub(super) const FINITE_MODEL_LANE_SEED_MS: u64 = 20_000;

/// Session-scoped spend and yield for this lane (#witness-check-cost).
///
/// Lives here rather than as loose `Executor` fields so the rule and the state
/// it reads are one unit. Deliberately NOT reset per check-sat: the whole point
/// is that an incremental trace which the lane never pays back stops paying for
/// it, and a per-call reset would restore the compounding cost exactly.
/// `reset-assertions` starts a new problem, so it does clear the account.
#[derive(Clone, Debug, Default)]
pub(in crate::executor) struct LaneAccount {
    /// Wall spent on invocations that returned nothing, in milliseconds.
    pub(super) declined_ms: u64,
    /// Wall spent on invocations that returned a certificate.
    pub(super) certified_ms: u64,
    /// How many certificates that was — trace only, the rule reads the times.
    pub(super) certificates: u64,
    /// Test-only override of the per-invocation cap
    /// ([`FINITE_MODEL_LANE_BUDGET_MS`] when `None`).
    ///
    /// Exists so the lane's barrier test can drive an ALREADY-SPENT account
    /// through the real lane on a fixture that certifies today. Never set on
    /// any production path.
    pub(in crate::executor) budget_ms_override: Option<u64>,
}

impl LaneAccount {
    /// Fresh speculative capital for a new problem.
    pub(in crate::executor) fn reset(&mut self) {
        *self = Self::default();
    }
}

/// The spend limit for one lane invocation.
///
/// Constructed at the lane's entry points ONLY, so every sub-solve of a
/// check-sat's pass — across refinement rounds — draws on the same account.
#[derive(Clone, Copy, Debug)]
pub(super) struct LaneBudget {
    opened: Instant,
    deadline: Instant,
    /// Ceiling for ONE sub-solve out of this account
    /// ([`FINITE_MODEL_PROBE_MS`] unless `--fmq-probe-ms` overrides it).
    probe_ms: u64,
}

impl LaneBudget {
    /// Open an account worth `budget_ms` from now.
    ///
    /// `budget_ms == 0` yields an account that is already spent, which is what
    /// the barrier test drives.
    pub(super) fn start(budget_ms: u64) -> Self {
        let opened = Instant::now();
        Self {
            opened,
            deadline: opened + Duration::from_millis(budget_ms),
            probe_ms: ay_core::misc_cli_flags()
                .fmq_probe_ms
                .unwrap_or(FINITE_MODEL_PROBE_MS),
        }
    }

    /// Milliseconds left, saturating at zero.
    pub(super) fn remaining_ms(&self) -> u64 {
        let now = Instant::now();
        if now >= self.deadline {
            0
        } else {
            u64::try_from((self.deadline - now).as_millis()).unwrap_or(u64::MAX)
        }
    }

    /// Milliseconds actually spent since the account was opened.
    pub(super) fn elapsed_ms(&self) -> u64 {
        u64::try_from(self.opened.elapsed().as_millis()).unwrap_or(u64::MAX)
    }

    /// Nothing left to spend.
    pub(super) fn spent(&self) -> bool {
        self.remaining_ms() == 0
    }

    /// Budget for ONE sub-solve: never more than the lane still has.
    ///
    /// Handing a sub-solve the full [`FINITE_MODEL_PROBE_MS`] out of an account
    /// with less than that left is how a "bounded" pass overruns its cap by an
    /// order of magnitude, so the two limits are combined here rather than at
    /// each call site.
    pub(super) fn sub_solve_ms(&self) -> u64 {
        self.remaining_ms().min(self.probe_ms)
    }
}
