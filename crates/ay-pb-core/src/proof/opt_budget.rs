// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! How a certified-optimization run divides its wall clock between SEARCH and
//! CERTIFICATION.
//!
//! THE SECOND COPY THIS EXISTS TO DELETE. The OPT-LIN certificate *chain* was
//! unified into `super::cert::certify_opt_lin_any_interruptible` (one
//! definition, four callers) and its per-route scheduler into
//! `super::route_budget::CertRouteBudget`. The BUDGET that decides how much
//! clock that chain is handed was left behind, copied verbatim into both
//! binaries: `crates/ay/src/cmd_pb.rs` and `crates/ay-pb/src/bin/ay.rs` each
//! carried the same eleven constants, the same `CertOptBudgetSplit`, the same
//! `compute_cert_opt_budget_split`, `certify_reserve`, `native_cap_expired` and
//! `extend_native_deadline` — and the same tests for all of it, twice.
//!
//! AND IT HAD ALREADY DRIFTED. Measured on tree `66304318f`, the two copies
//! differed in three behavioural ways, all of them present only in the
//! competition binary:
//!
//! ```text
//!   opt_cert_portfolio_enabled()      the `--no-opt-cert-portfolio` kill switch
//!   objective_range_fits_i64(obj)     skip the reserve when the range overflows
//!   cert_native_cap_ms_override()     the `--cert-native-cap-ms` pin
//! ```
//!
//! Two of the three are ay-pb-only FLAGS, so they are policy the caller owns,
//! not drift to be flattened; they are passed in as [`CertOptBudgetPolicy`].
//! The third was a genuine one-sided guard. It is now on both paths, and it is
//! UNOBSERVABLE on this corpus — but not for the reason first recorded here.
//! `objective_range_fits_i64` tests for `i128` accumulator overflow, and the
//! original claim ("inert by a wide margin; the largest objective sum in a
//! 140-instance sample is 2.8e-17 of `i128::MAX`") was a sample statement
//! promoted to a corpus statement: on the full `census/optlin-555.list`,
//! 2 of 555 objectives DO overflow `i128` (`factor` N=440 and N=480, binary
//! objectives `2^0..2^240`, past the limit by 1.98e28x and 2.08e34x), and the
//! nearest non-overflowing family member (N=240) sits ~64x from the limit.
//! The guard still cannot move a verdict, because the whole `factor` family is
//! refused `s UNSUPPORTED` upstream (`portfolio.rs` returns
//! `unsupported_solution()` immediately on overflow) before any budget is
//! computed — measured on both base and head, ~0.05 s. Adopting the guard is
//! still right: reserving certificate budget for an instance the portfolio
//! will refuse is pure waste. The drift-without-notice story stands — that is
//! the argument for one definition, not against it.
//!
//! # Soundness
//!
//! Nothing in this module derives anything. It hands out DEADLINES, and every
//! consumer of those deadlines treats them as an extra disjunct in a
//! `should_stop` predicate it already polls. Every certificate emitter is
//! fail-closed on interruption: it returns `None`, never a truncated proof. So
//! the strongest thing a budget computed here can do is make a route decline
//! EARLIER — it can turn a proof into no-proof, never no-proof into a proof,
//! and never one proof into a different one. Whatever is emitted is still
//! re-checked by the pinned external VeriPB checker before any CERTIFIED claim.

use std::cell::Cell;
use std::time::{Duration, Instant};

use crate::solver::objective_range_fits_i64;
use crate::types::{PbInstance, PbObjective};

/// Fraction of the remaining budget the native proof-logging CDCL gets before
/// the certified pipeline behind it is allowed to start.
pub const OPT_CERT_NATIVE_SLICE_DIV: u32 = 6;
/// As [`OPT_CERT_NATIVE_SLICE_DIV`], for instances large enough that parsing
/// and encoding dominate; the native phase is given proportionally less.
pub const OPT_CERT_NATIVE_SLICE_DIV_HUGE: u32 = 12;
/// Ceiling the improvement grace may extend the native slice to.
pub const OPT_CERT_NATIVE_CEIL_DIV: u32 = 3;
/// As [`OPT_CERT_NATIVE_CEIL_DIV`], for huge instances.
pub const OPT_CERT_NATIVE_CEIL_DIV_HUGE: u32 = 6;
/// Fraction of the remaining budget granted per VERIFIED improving incumbent.
pub const OPT_CERT_IMPROVE_GRACE_DIV: u32 = 12;
/// Absolute cap on a single improvement grace extension.
pub const OPT_CERT_IMPROVE_GRACE_MAX_MS: u64 = 30_000;
/// Fraction of the remaining budget reserved for the out-of-band certification
/// re-solve behind the fallback portfolio.
pub const OPT_CERT_CERTIFY_RESERVE_DIV: u32 = 8;
/// Floor on that reserve.
pub const OPT_CERT_CERTIFY_RESERVE_MIN_MS: u64 = 10_000;
/// Ceiling on that reserve.
pub const OPT_CERT_CERTIFY_RESERVE_MAX_MS: u64 = 300_000;
/// Variable count at or above which an instance counts as "huge".
pub const OPT_CERT_HUGE_MIN_VARS: u32 = 900_000;
/// Constraint count at or above which an instance counts as "huge".
pub const OPT_CERT_HUGE_MIN_CONSTRAINTS: usize = 1_000_000;

/// Caller-owned policy for [`compute_cert_opt_budget_split`].
///
/// These are the parts that are legitimately per-binary: the competition binary
/// exposes `--no-opt-cert-portfolio` and `--cert-native-cap-ms`, the shipped CLI
/// exposes neither. Passing them in keeps ONE budget definition while letting a
/// caller that has the flags honour them — the alternative (a second copy of the
/// whole computation) is what this module exists to delete.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertOptBudgetPolicy {
    /// `false` restores native-only behaviour (the pipeline is ineligible).
    pub enabled: bool,
    /// Pins BOTH the initial slice and the hard ceiling to this many
    /// milliseconds, with no improvement grace. Test/tuning override.
    pub native_cap_ms: Option<u64>,
}

impl Default for CertOptBudgetPolicy {
    /// The shipped default: pipeline on, no cap override.
    fn default() -> Self {
        Self {
            enabled: true,
            native_cap_ms: None,
        }
    }
}

/// How the certified-optimization budget is split between the native
/// proof-logging CDCL and the out-of-band certification stage behind it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertOptBudgetSplit {
    /// Initial wall-clock deadline for the native proof-logging slice.
    /// `None` = uncapped (no timeout, or the split does not apply).
    pub native_deadline: Option<Instant>,
    /// Ceiling the improvement grace may extend `native_deadline` to.
    pub native_hard_limit: Option<Instant>,
    /// Extension granted on each VERIFIED strictly-improving incumbent.
    pub improve_grace: Duration,
}

impl CertOptBudgetSplit {
    /// A split that caps nothing: no timeout, or the pipeline does not apply.
    #[must_use]
    pub const fn uncapped() -> Self {
        Self {
            native_deadline: None,
            native_hard_limit: None,
            improve_grace: Duration::ZERO,
        }
    }

    /// Whether the certified-optimization pipeline applies at all.
    #[must_use]
    pub fn eligible(&self) -> bool {
        self.native_deadline.is_some()
    }
}

/// Decides whether the certified-optimization budget split applies and sizes the
/// native slice.
///
/// Eligibility: `policy.enabled`, a timeout exists (an unbounded run keeps the
/// unbounded-native semantics), the objective is single-literal linear — the
/// OPT-LIN certification helpers' whole domain, so on anything else the reserve
/// would buy nothing and only take time from the search — and the objective
/// range does not overflow (the portfolio bails `Unsupported` instantly on
/// overflow, which would discard the whole fallback budget).
#[must_use]
pub fn compute_cert_opt_budget_split(
    instance: &PbInstance,
    objective: &PbObjective,
    timeout_dur: Option<Duration>,
    start: Instant,
    policy: CertOptBudgetPolicy,
) -> CertOptBudgetSplit {
    let Some(timeout) = timeout_dur else {
        return CertOptBudgetSplit::uncapped();
    };
    if !policy.enabled
        || !objective.terms.iter().all(|term| term.lits.len() == 1)
        || !objective_range_fits_i64(objective)
    {
        return CertOptBudgetSplit::uncapped();
    }

    let now = Instant::now();
    let remaining = timeout.saturating_sub(start.elapsed());
    split_from_remaining(instance, remaining, now, policy)
}

fn split_from_remaining(
    instance: &PbInstance,
    remaining: Duration,
    now: Instant,
    policy: CertOptBudgetPolicy,
) -> CertOptBudgetSplit {
    if let Some(cap_ms) = policy.native_cap_ms {
        let cap = Duration::from_millis(cap_ms);
        return CertOptBudgetSplit {
            native_deadline: Some(now + cap),
            native_hard_limit: Some(now + cap),
            improve_grace: Duration::ZERO,
        };
    }

    let huge = instance_is_huge(instance);
    let (slice_div, ceil_div) = if huge {
        (
            OPT_CERT_NATIVE_SLICE_DIV_HUGE,
            OPT_CERT_NATIVE_CEIL_DIV_HUGE,
        )
    } else {
        (OPT_CERT_NATIVE_SLICE_DIV, OPT_CERT_NATIVE_CEIL_DIV)
    };
    CertOptBudgetSplit {
        native_deadline: Some(now + remaining / slice_div),
        native_hard_limit: Some(now + remaining / ceil_div),
        improve_grace: (remaining / OPT_CERT_IMPROVE_GRACE_DIV)
            .min(Duration::from_millis(OPT_CERT_IMPROVE_GRACE_MAX_MS)),
    }
}

/// Reserve kept for the out-of-band certification re-solve behind the fallback
/// portfolio: `remaining/8` clamped to `[10s, 300s]`, never more than half of
/// what is left.
///
/// NOTE THE SHAPE, it is not a constant fraction. The `10s` floor dominates
/// small budgets and the `300s` ceiling dominates large ones, so the reserve is
/// 50% of a 5s or 20s budget, 16.7% of 60s, 12.5% of 300s and 8.3% of an hour.
#[must_use]
pub fn certify_reserve(remaining: Duration) -> Duration {
    (remaining / OPT_CERT_CERTIFY_RESERVE_DIV)
        .max(Duration::from_millis(OPT_CERT_CERTIFY_RESERVE_MIN_MS))
        .min(Duration::from_millis(OPT_CERT_CERTIFY_RESERVE_MAX_MS))
        .min(remaining / 2)
}

/// Whether the native slice's current deadline has passed.
#[must_use]
pub fn native_cap_expired(deadline: &Cell<Option<Instant>>) -> bool {
    deadline.get().is_some_and(|dl| Instant::now() >= dl)
}

/// Whether an instance counts as "huge" for the budget split — the one
/// definition, so a caller that has to REPORT the divisor cannot disagree with
/// the one [`compute_cert_opt_budget_split`] applied.
#[must_use]
pub fn instance_is_huge(instance: &PbInstance) -> bool {
    instance.num_vars >= OPT_CERT_HUGE_MIN_VARS
        || instance.constraints.len() >= OPT_CERT_HUGE_MIN_CONSTRAINTS
}

/// Where the length of the proof-logging slice actually came from.
///
/// THIS EXISTS BECAUSE THE NOTE PRINTED FALSE ARITHMETIC. The first version
/// hardcoded [`OPT_CERT_NATIVE_SLICE_DIV`] into its text, but the slice has
/// three provenances, and two of them are not that divisor:
/// [`OPT_CERT_NATIVE_SLICE_DIV_HUGE`] on a huge instance, and no divisor at all
/// when `--cert-native-cap-ms` pins the slice. Measured: on
/// `normalized-simp-nonunif-100_100.02.opb` (21566 vars / 1_314_050
/// constraints, one of 30 huge instances in `census/optlin-555.list`) the
/// hardcoded form printed
///
/// ```text
///   cut after 5121 ms by the certificate BUDGET SPLIT (declared --timeout 60000 ms / 6)
/// ```
///
/// and `60000 / 6 = 10000`, not 5121. A diagnostic whose arithmetic does not
/// check out is worse than no diagnostic, so the provenance is now passed in
/// rather than assumed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofSliceOrigin {
    /// The default policy: `remaining / div` of the budget left when the split
    /// was taken. `huge` records which of the two divisors applied.
    Divisor {
        /// The divisor actually applied.
        div: u32,
        /// Whether it was the huge-instance divisor.
        huge: bool,
    },
    /// The slice was pinned by `--cert-native-cap-ms`; no divisor applied.
    CapOverride {
        /// The pinned value, in milliseconds.
        cap_ms: u64,
    },
}

impl ProofSliceOrigin {
    /// The provenance [`compute_cert_opt_budget_split`] will apply for this
    /// policy and instance size. Derived from the same inputs as the split
    /// itself so the two cannot drift.
    #[must_use]
    pub fn from_policy(policy: CertOptBudgetPolicy, huge: bool) -> Self {
        match policy.native_cap_ms {
            Some(cap_ms) => Self::CapOverride { cap_ms },
            None if huge => Self::Divisor {
                div: OPT_CERT_NATIVE_SLICE_DIV_HUGE,
                huge: true,
            },
            None => Self::Divisor {
                div: OPT_CERT_NATIVE_SLICE_DIV,
                huge: false,
            },
        }
    }
}

/// The slice the proof-logging phase actually received, and where its length
/// came from. Built by the caller that owns the split, so the note never has to
/// guess.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofSliceProvenance {
    /// How much wall clock the phase actually got.
    pub slice: Duration,
    /// Where that length came from.
    pub origin: ProofSliceOrigin,
    /// `Some(initial)` when an improvement grace extended the slice, so the
    /// note reports the extension rather than misattributing the final length
    /// to the divisor alone.
    pub grace_extended_from: Option<Duration>,
}

impl ProofSliceProvenance {
    /// The clause naming where the slice came from, in the note's voice.
    fn origin_clause(&self, timeout_ms: u128) -> String {
        let base = match self.origin {
            ProofSliceOrigin::Divisor { div, huge: false } => format!(
                "the default split hands this phase remaining/{div} of the declared \
                 --timeout {timeout_ms} ms"
            ),
            ProofSliceOrigin::Divisor { div, huge: true } => format!(
                "the HUGE-instance split hands this phase remaining/{div} of the declared \
                 --timeout {timeout_ms} ms"
            ),
            ProofSliceOrigin::CapOverride { cap_ms } => format!(
                "the slice was pinned to {cap_ms} ms by --cert-native-cap-ms, no divisor \
                 applied; the declared --timeout is {timeout_ms} ms"
            ),
        };
        match self.grace_extended_from {
            Some(initial) => format!(
                "{base}, and an improvement grace extended it from {} ms",
                initial.as_millis()
            ),
            None => base,
        }
    }
}

/// Renders the one-line diagnostic for the pathology this split can cause, or
/// `None` when it did not occur.
///
/// # The pathology
///
/// The proof-logging phase is handed a FRACTION of the declared budget (see
/// [`ProofSliceOrigin`]), and on the decision path it is the only phase that can
/// emit a refutation. So on that path whether an instance certifies is a
/// function of the SLICE, not of the declared budget, and `--timeout` acts as a
/// search parameter rather than as a stopping condition. Measured on
/// `normalized-50-750-false-45-90-4-8000opt` (DECISION form — this instance has
/// no objective; see the scope note below), one frozen binary, one input, only
/// `--timeout` varying:
///
/// ```text
///    60000 ms -> slice 10.0 s -> ran the full 60.1 s, 0 proof bytes, s UNKNOWN
///   120000 ms -> slice 20.0 s -> ran the full 120.1 s, 0 proof bytes, s UNKNOWN
///   240000 ms -> slice 40.0 s -> DONE in 18.1 s, 13065906 bytes, s UNSATISFIABLE
///   400000 ms -> slice 66.7 s -> DONE in 17.3 s, 13065906 bytes, s UNSATISFIABLE
/// ```
///
/// A four-times-larger declared budget made the run 6.6x FASTER in wall time,
/// and the two proofs are byte-identical, so the phase does identical work — the
/// budget decides only whether it is allowed to FINISH. Pinning the slice with
/// `--cert-native-cap-ms 55000` while leaving `--timeout 60000` alone reproduces
/// the certificate in 17.3 s, which isolates the cause to this split and
/// exonerates the memory governor.
///
/// # Scope
///
/// That measurement is a DECISION-path measurement. Every one of the 555
/// instances in `census/optlin-555.list` has an objective, so none of them reach
/// the decision path, and the note fires on the OPT-LIN path for a different
/// reason: there the slice bounds the native proof-logging CDCL that runs BEFORE
/// the certified fallback, and a miss recorded while the slice was spent and the
/// declared budget was not is likewise not a statement about the declared
/// budget.
///
/// The note is the distinguishing signal for a cut that was previously SILENT —
/// the run exits at the declared budget with nothing to separate it from an
/// honest timeout. It is diagnostic only: no caller may branch on it, and
/// emitting it cannot change a verdict.
#[must_use]
pub fn proof_slice_cut_note(
    provenance: ProofSliceProvenance,
    native_deadline: Option<Instant>,
    timeout_dur: Option<Duration>,
    start: Instant,
) -> Option<String> {
    // Fires only when the SLICE is what stopped the phase: its deadline has
    // passed while the caller's declared budget still has time on it. When the
    // declared budget is also spent this is an honest timeout and says nothing.
    let deadline = native_deadline?;
    if Instant::now() < deadline {
        return None;
    }
    let timeout = timeout_dur?;
    let elapsed = start.elapsed();
    let unused = timeout.checked_sub(elapsed)?;
    if unused.is_zero() {
        return None;
    }
    // The lever only helps while it would actually WIDEN the slice; suggesting
    // a cap below the one already in force would be advice to make it worse.
    let timeout_ms = timeout.as_millis();
    let suggested = timeout.as_millis().saturating_sub(5_000).max(1);
    let advice = match provenance.origin {
        ProofSliceOrigin::CapOverride { cap_ms } if u128::from(cap_ms) >= suggested => format!(
            "The slice is already pinned at {cap_ms} ms, so raise BOTH --cert-native-cap-ms \
             and the declared --timeout to hand the proof phase more wall clock."
        ),
        _ => format!(
            "Re-run with --cert-native-cap-ms {suggested} to hand the proof phase the whole \
             budget."
        ),
    };
    // The claim is deliberately the WEAKEST one that is always true. Saying
    // "this miss is caused by the split" would overclaim on an instance the
    // full budget could not certify either. What is always true is the
    // measurement fact: the proof phase did not receive the declared budget, so
    // a miss on this run is not evidence about the declared budget.
    Some(format!(
        "PROOF-SLICE-EXPIRED: the proof-logging phase was cut after {} ms by the certificate \
         BUDGET SPLIT ({}), with {} ms of the declared budget still unused. The proof phase did \
         NOT receive the declared budget, so if this run reports no certificate that is not \
         evidence that {timeout_ms} ms is insufficient. {advice}",
        provenance.slice.as_millis(),
        provenance.origin_clause(timeout_ms),
        unused.as_millis(),
    ))
}

/// Extends the native slice after a verified incumbent improvement: monotone,
/// clamped at the hard ceiling, no-op when uncapped or grace-free.
pub fn extend_native_deadline(deadline: &Cell<Option<Instant>>, split: &CertOptBudgetSplit) {
    let (Some(current), Some(hard)) = (deadline.get(), split.native_hard_limit) else {
        return;
    };
    if split.improve_grace.is_zero() {
        return;
    }
    let extended = (Instant::now() + split.improve_grace).min(hard);
    if extended > current {
        deadline.set(Some(extended));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbConstraint, PbRel, PbTerm};

    fn lin_objective(n: u32) -> PbObjective {
        PbObjective {
            terms: (1..=n)
                .map(|v| PbTerm {
                    coeff: 1,
                    lits: vec![crate::types::PbLit {
                        var: v,
                        negated: false,
                    }],
                })
                .collect(),
        }
    }

    fn instance(num_vars: u32, num_constraints: usize) -> PbInstance {
        PbInstance {
            num_vars,
            num_constraints: num_constraints as u32,
            constraints: (0..num_constraints)
                .map(|_| PbConstraint {
                    terms: vec![PbTerm {
                        coeff: 1,
                        lits: vec![crate::types::PbLit {
                            var: 1,
                            negated: false,
                        }],
                    }],
                    rel: PbRel::Ge,
                    rhs: 0,
                })
                .collect(),
            objective: None,
        }
    }

    #[test]
    fn split_sizes_the_native_slice_and_ceiling() {
        let inst = instance(10, 4);
        let obj = lin_objective(10);
        let now = Instant::now();
        let budget = Duration::from_secs(600);
        let split = compute_cert_opt_budget_split(
            &inst,
            &obj,
            Some(budget),
            now,
            CertOptBudgetPolicy::default(),
        );
        assert!(split.eligible());
        let slice = split.native_deadline.unwrap() - now;
        let ceiling = split.native_hard_limit.unwrap() - now;
        // R/6 and R/3, within the wall-clock noise of computing them.
        assert!(slice >= Duration::from_secs(95) && slice <= Duration::from_secs(105));
        assert!(ceiling >= Duration::from_secs(195) && ceiling <= Duration::from_secs(205));
        // min(R/12, 30s) = 30s
        assert_eq!(split.improve_grace, Duration::from_secs(30));
    }

    /// THE REGRESSION THIS WHOLE MODULE EXISTS FOR, asserted once for every
    /// caller. Before the split existed, `solve_optimization_with_proof` gave
    /// the native proof-logging CDCL the caller's whole `timeout_dur` and then
    /// called the certificate stage with the SAME `start`/`timeout_dur`, so the
    /// stage's budget was `B - B = 0` for every `B` and every
    /// `*_interruptible` helper returned `None` on its first check. The
    /// property that matters is not "the numbers are these numbers" but "what
    /// is left for certification is STRICTLY POSITIVE".
    ///
    /// This lived in BOTH binaries' test files, which is precisely why a drift
    /// between the two implementations passed both suites.
    #[test]
    fn split_leaves_the_certificate_stage_a_real_budget() {
        let inst = instance(2, 1);
        let obj = lin_objective(2);
        for budget in [
            Duration::from_secs(5),
            Duration::from_secs(20),
            Duration::from_secs(60),
            Duration::from_secs(600),
        ] {
            let start = Instant::now();
            let split = compute_cert_opt_budget_split(
                &inst,
                &obj,
                Some(budget),
                start,
                CertOptBudgetPolicy::default(),
            );
            let deadline = split
                .native_deadline
                .expect("a bounded, single-literal-linear run must be eligible");
            let hard = split
                .native_hard_limit
                .expect("ceiling present when capped");
            let overall = start + budget;
            assert!(
                deadline < overall,
                "native slice must end before the overall deadline ({budget:?})"
            );
            assert!(
                hard < overall,
                "even the extended ceiling must end before the overall deadline ({budget:?})"
            );
            assert!(
                deadline < hard,
                "the ceiling must be able to extend the slice ({budget:?})"
            );
            assert!(
                certify_reserve(budget) > Duration::ZERO,
                "certification reserve must be positive at {budget:?}"
            );
            assert!(
                certify_reserve(budget) <= budget / 2,
                "the reserve must never take more than half the budget ({budget:?})"
            );
        }
    }

    #[test]
    fn split_is_uncapped_without_a_timeout() {
        let inst = instance(10, 4);
        let obj = lin_objective(10);
        let split = compute_cert_opt_budget_split(
            &inst,
            &obj,
            None,
            Instant::now(),
            CertOptBudgetPolicy::default(),
        );
        assert!(!split.eligible());
        assert_eq!(split, CertOptBudgetSplit::uncapped());
    }

    #[test]
    fn split_declines_a_nonlinear_objective() {
        let inst = instance(10, 4);
        let nonlinear = PbObjective {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![
                    crate::types::PbLit {
                        var: 1,
                        negated: false,
                    },
                    crate::types::PbLit {
                        var: 2,
                        negated: false,
                    },
                ],
            }],
        };
        let split = compute_cert_opt_budget_split(
            &inst,
            &nonlinear,
            Some(Duration::from_secs(60)),
            Instant::now(),
            CertOptBudgetPolicy::default(),
        );
        assert!(!split.eligible());
    }

    /// The kill switch is POLICY, not drift: `enabled: false` must restore the
    /// uncapped native-only behaviour on any caller that asks for it.
    #[test]
    fn split_honours_the_disabled_policy() {
        let inst = instance(10, 4);
        let obj = lin_objective(10);
        let split = compute_cert_opt_budget_split(
            &inst,
            &obj,
            Some(Duration::from_secs(60)),
            Instant::now(),
            CertOptBudgetPolicy {
                enabled: false,
                native_cap_ms: None,
            },
        );
        assert!(!split.eligible());
    }

    /// `--cert-native-cap-ms` pins slice AND ceiling and drops the grace.
    #[test]
    fn split_honours_the_native_cap_override() {
        let inst = instance(10, 4);
        let obj = lin_objective(10);
        let now = Instant::now();
        let split = compute_cert_opt_budget_split(
            &inst,
            &obj,
            Some(Duration::from_secs(600)),
            now,
            CertOptBudgetPolicy {
                enabled: true,
                native_cap_ms: Some(1_500),
            },
        );
        assert!(split.eligible());
        assert_eq!(split.native_deadline, split.native_hard_limit);
        assert_eq!(split.improve_grace, Duration::ZERO);
        let cap = split.native_deadline.unwrap() - now;
        assert!(cap >= Duration::from_millis(1_400) && cap <= Duration::from_millis(1_600));
    }

    /// A huge instance gets proportionally LESS native time, not more.
    #[test]
    fn split_shrinks_the_native_slice_on_huge_instances() {
        let obj = lin_objective(4);
        let now = Instant::now();
        let budget = Duration::from_secs(600);
        let small = compute_cert_opt_budget_split(
            &instance(10, 4),
            &obj,
            Some(budget),
            now,
            CertOptBudgetPolicy::default(),
        );
        let huge = compute_cert_opt_budget_split(
            &instance(OPT_CERT_HUGE_MIN_VARS, 4),
            &obj,
            Some(budget),
            now,
            CertOptBudgetPolicy::default(),
        );
        assert!(huge.native_deadline.unwrap() < small.native_deadline.unwrap());
        assert!(huge.native_hard_limit.unwrap() < small.native_hard_limit.unwrap());
    }

    #[test]
    fn certify_reserve_clamps() {
        // floor: R/8 = 1.25s, but the 10s floor then the R/2 cap wins.
        assert_eq!(
            certify_reserve(Duration::from_secs(10)),
            Duration::from_secs(5)
        );
        // middle: R/8 = 100s, inside [10s, 300s].
        assert_eq!(
            certify_reserve(Duration::from_secs(800)),
            Duration::from_secs(100)
        );
        // ceiling: R/8 = 375s, clamped to 300s.
        assert_eq!(
            certify_reserve(Duration::from_mins(50)),
            Duration::from_secs(300)
        );
        // degenerate: nothing left to reserve.
        assert_eq!(certify_reserve(Duration::ZERO), Duration::ZERO);
        // never more than half.
        for secs in [1u64, 5, 20, 60, 300, 3600] {
            let r = Duration::from_secs(secs);
            assert!(
                certify_reserve(r) <= r / 2,
                "reserve exceeded half at {secs}s"
            );
        }
    }

    #[test]
    fn extend_native_deadline_is_monotone_and_clamped() {
        let now = Instant::now();
        let split = CertOptBudgetSplit {
            native_deadline: Some(now + Duration::from_secs(10)),
            native_hard_limit: Some(now + Duration::from_secs(20)),
            improve_grace: Duration::from_secs(30),
        };
        let cell = Cell::new(split.native_deadline);
        extend_native_deadline(&cell, &split);
        // grace (30s) overshoots the ceiling, so it clamps there.
        assert_eq!(cell.get(), split.native_hard_limit);
        // monotone: a second call cannot move it backwards.
        extend_native_deadline(&cell, &split);
        assert_eq!(cell.get(), split.native_hard_limit);

        // uncapped split: no-op, never installs a deadline.
        let free: Cell<Option<Instant>> = Cell::new(None);
        extend_native_deadline(&free, &CertOptBudgetSplit::uncapped());
        assert_eq!(free.get(), None);
    }

    #[test]
    fn native_cap_expired_only_when_a_deadline_has_passed() {
        assert!(!native_cap_expired(&Cell::new(None)));
        assert!(!native_cap_expired(&Cell::new(Some(
            Instant::now() + Duration::from_secs(60)
        ))));
        assert!(native_cap_expired(&Cell::new(Some(
            Instant::now()
                .checked_sub(Duration::from_secs(1))
                .expect("fixture instant supports one-second subtraction")
        ))));
    }

    /// Convenience: the default (small-instance) provenance.
    fn default_prov(slice: Duration) -> ProofSliceProvenance {
        ProofSliceProvenance {
            slice,
            origin: ProofSliceOrigin::Divisor {
                div: OPT_CERT_NATIVE_SLICE_DIV,
                huge: false,
            },
            grace_extended_from: None,
        }
    }

    /// The note must fire on exactly the pathology and on nothing else: the
    /// slice is spent while the DECLARED budget still has time on it.
    #[test]
    fn proof_slice_cut_note_fires_only_when_the_slice_outran_the_deadline() {
        let prov = default_prov(Duration::from_secs(10));
        let budget = Duration::from_secs(60);
        let expired = Some(
            Instant::now()
                .checked_sub(Duration::from_secs(1))
                .expect("fixture instant supports one-second subtraction"),
        );
        let live = Some(Instant::now() + Duration::from_secs(30));

        // THE PATHOLOGY: slice spent 1 s ago, 50 s of the declared budget left.
        let start = Instant::now()
            .checked_sub(Duration::from_secs(10))
            .expect("fixture instant supports ten-second subtraction");
        let note = proof_slice_cut_note(prov, expired, Some(budget), start)
            .expect("slice spent with budget remaining must produce the note");
        assert!(note.starts_with("PROOF-SLICE-EXPIRED:"), "{note}");
        assert!(note.contains("10000 ms"), "reports the slice: {note}");
        assert!(
            note.contains("60000 ms"),
            "reports the declared budget: {note}"
        );
        assert!(
            note.contains("--cert-native-cap-ms"),
            "names the decoupling lever: {note}"
        );

        // NOT the pathology: the slice has not been reached.
        assert!(proof_slice_cut_note(prov, live, Some(budget), start).is_none());
        // NOT the pathology: no slice at all (uncapped run).
        assert!(proof_slice_cut_note(prov, None, Some(budget), start).is_none());
        // NOT the pathology: no declared budget, so nothing was cut short of one.
        assert!(proof_slice_cut_note(prov, expired, None, start).is_none());
        // NOT the pathology: an HONEST timeout — the declared budget is spent
        // too, so the slice is not what stopped the phase.
        let long_ago = Instant::now()
            .checked_sub(Duration::from_secs(90))
            .expect("fixture instant supports ninety-second subtraction");
        assert!(proof_slice_cut_note(prov, expired, Some(budget), long_ago).is_none());
    }

    /// THE DEFECT THIS PAIRS WITH: the note used to hardcode
    /// `OPT_CERT_NATIVE_SLICE_DIV`, so on a HUGE instance it printed
    /// "60000 ms / 6" over a slice of ~5000 ms — arithmetic that does not check
    /// out. The note must name the divisor that was actually applied, and it
    /// must never name a divisor the run did not use.
    #[test]
    fn proof_slice_cut_note_reports_the_huge_divisor_not_the_default() {
        let budget = Duration::from_secs(60);
        let start = Instant::now()
            .checked_sub(Duration::from_secs(6))
            .expect("fixture instant supports six-second subtraction");
        let expired = Some(
            Instant::now()
                .checked_sub(Duration::from_millis(1))
                .expect("fixture instant supports one-millisecond subtraction"),
        );
        let prov = ProofSliceProvenance {
            slice: Duration::from_millis(5_121),
            origin: ProofSliceOrigin::Divisor {
                div: OPT_CERT_NATIVE_SLICE_DIV_HUGE,
                huge: true,
            },
            grace_extended_from: None,
        };
        let note = proof_slice_cut_note(prov, expired, Some(budget), start).expect("fires");
        assert!(note.contains("remaining/12"), "names /12: {note}");
        assert!(note.contains("HUGE-instance"), "says why /12: {note}");
        assert!(
            !note.contains("remaining/6"),
            "must not claim the default divisor on a huge instance: {note}"
        );
        assert!(note.contains("5121 ms"), "reports the real slice: {note}");
    }

    /// The second uncovered case: `--cert-native-cap-ms` pins the slice and NO
    /// divisor applies, so the note may not describe the length as a fraction
    /// of the declared budget.
    #[test]
    fn proof_slice_cut_note_reports_a_pinned_slice_as_pinned() {
        let budget = Duration::from_secs(60);
        let start = Instant::now()
            .checked_sub(Duration::from_secs(6))
            .expect("fixture instant supports six-second subtraction");
        let expired = Some(
            Instant::now()
                .checked_sub(Duration::from_millis(1))
                .expect("fixture instant supports one-millisecond subtraction"),
        );
        let prov = ProofSliceProvenance {
            slice: Duration::from_millis(5_000),
            origin: ProofSliceOrigin::CapOverride { cap_ms: 5_000 },
            grace_extended_from: None,
        };
        let note = proof_slice_cut_note(prov, expired, Some(budget), start).expect("fires");
        assert!(note.contains("pinned to 5000 ms"), "{note}");
        assert!(note.contains("no divisor applied"), "{note}");
        assert!(
            !note.contains("remaining/"),
            "a pinned slice is not a fraction of the budget: {note}"
        );
        // The lever advice must still widen the slice.
        assert!(note.contains("--cert-native-cap-ms 55000"), "{note}");

        // ...and it must NOT advise a value below the pin already in force.
        let pinned_high = ProofSliceProvenance {
            slice: Duration::from_secs(58),
            origin: ProofSliceOrigin::CapOverride { cap_ms: 58_000 },
            grace_extended_from: None,
        };
        let note = proof_slice_cut_note(pinned_high, expired, Some(budget), start).expect("fires");
        assert!(
            !note.contains("--cert-native-cap-ms 55000"),
            "must not advise shrinking a 58000 ms pin to 55000: {note}"
        );
        assert!(note.contains("already pinned at 58000 ms"), "{note}");
    }

    /// Third case: an improvement grace extended the slice, so the final length
    /// is not the divisor's output and the note says so.
    #[test]
    fn proof_slice_cut_note_reports_a_grace_extension() {
        let budget = Duration::from_secs(60);
        let start = Instant::now()
            .checked_sub(Duration::from_secs(21))
            .expect("fixture instant supports twenty-one-second subtraction");
        let expired = Some(
            Instant::now()
                .checked_sub(Duration::from_millis(1))
                .expect("fixture instant supports one-millisecond subtraction"),
        );
        let prov = ProofSliceProvenance {
            slice: Duration::from_secs(20),
            origin: ProofSliceOrigin::Divisor {
                div: OPT_CERT_NATIVE_SLICE_DIV,
                huge: false,
            },
            grace_extended_from: Some(Duration::from_millis(10_000)),
        };
        let note = proof_slice_cut_note(prov, expired, Some(budget), start).expect("fires");
        assert!(
            note.contains("20000 ms"),
            "reports the slice it got: {note}"
        );
        assert!(
            note.contains("improvement grace extended it from 10000 ms"),
            "attributes the extra: {note}"
        );
    }

    /// The provenance a caller reports must be the one the split applied. This
    /// is the cross-check that keeps the note honest without the caller having
    /// to re-derive the rule.
    #[test]
    fn slice_origin_tracks_the_split_it_describes() {
        let now = Instant::now();
        let budget = Duration::from_secs(600);

        for (vars, huge) in [(10u32, false), (OPT_CERT_HUGE_MIN_VARS, true)] {
            let inst = instance(vars, 4);
            assert_eq!(instance_is_huge(&inst), huge);
            let split = split_from_remaining(&inst, budget, now, CertOptBudgetPolicy::default());
            let origin = ProofSliceOrigin::from_policy(
                CertOptBudgetPolicy::default(),
                instance_is_huge(&inst),
            );
            let ProofSliceOrigin::Divisor { div, huge: h } = origin else {
                panic!("default policy must be a divisor origin");
            };
            assert_eq!(h, huge);
            assert_eq!(
                split.native_deadline,
                Some(now + budget / div),
                "reported divisor {div} must exactly reproduce the native slice"
            );
        }

        // A pin is a pin, on any instance size.
        let policy = CertOptBudgetPolicy {
            enabled: true,
            native_cap_ms: Some(1_500),
        };
        assert_eq!(
            ProofSliceOrigin::from_policy(policy, true),
            ProofSliceOrigin::CapOverride { cap_ms: 1_500 }
        );
        assert_eq!(
            ProofSliceOrigin::from_policy(policy, false),
            ProofSliceOrigin::CapOverride { cap_ms: 1_500 }
        );
    }
}
