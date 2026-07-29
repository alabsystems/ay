// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `SharedBounds` — the parallel-portfolio bound bus (design §2.7 / §3.1 of
//! the development design notes).
//!
//! One instance is shared (via `Arc`) between the parallel-optimization
//! coordinator and its COMPLETE worker engines:
//!
//! * **UP** (unchanged): workers stream `Improvement`s to the coordinator over
//!   the mpsc channel; the bus plays no part in that direction.
//! * **DOWN** (this module): the COORDINATOR — and only the coordinator — is
//!   the bus writer. After each `sanitize_optimization_incumbent`-verified
//!   improvement it publishes the (value, model) pair here, and COMPLETE
//!   workers may READ the upper bound as a prune-only cutoff
//!   (`native_oll`'s `external_ub_cutoff`). Workers never write the bus, so
//!   they remain exactly as verdict/bus-write-incapable as before.
//!
//! # Soundness contract
//!
//! * `ub`/`incumbent` are only ever published by the coordinator AFTER
//!   `sanitize_optimization_incumbent` re-verified the model against the
//!   ORIGINAL constraints and recomputed the exact objective. The bus `ub` is
//!   therefore always the objective value of a genuinely feasible model — a
//!   TRUE upper bound on the optimum. Consumers (the `native_oll` prune row)
//!   rely on exactly this "verified-publisher" invariant.
//! * `publish_incumbent` takes **i128** and **REJECTS (no-publish)** any value
//!   that does not fit the i64 transport — it never `as`-casts / truncates
//!   (§2.7 "reject-not-truncate"). A truncated ub would be a *lower* — i.e.
//!   unsound — cutoff.
//! * A bus `ub` that is absent (or was rejected on overflow) reads as `None`
//!   == **"no cutoff"**, never as "0/unbounded-good".
//! * `publish_lb` is **typed-by-source**: it accepts only a
//!   [`GlobalSoundFloor`], whose constructors are `pub(crate)` and exist ONLY
//!   for audited, globally-sound floor derivations (see the constructor docs).
//!   External code can read the bus but cannot fabricate a floor — locked by
//!   the `tests/ui/shared_bounds_lb_requires_audited_source.rs` compile-fail.
//! * The `ub == lb` OPTIMUM upgrade decision NEVER combines a `Relaxed`-read
//!   `ub` with a separately-read incumbent: it LOCKS the incumbent slot
//!   ([`SharedBounds::locked_incumbent`]), THEN reads `lb`, then RE-VERIFIES
//!   the locked model from raw bits (S3 ordering, design §3.1); see
//!   `portfolio::shared_bounds_optimum_upgrade`.
//! * The bus deliberately carries NO publish counter / epoch. Change
//!   detection, if ever needed, must be a properly-ordered seqlock
//!   (Acquire/Release-paired reads bracketing the data); the previously-shipped
//!   `Relaxed` epoch counter could not serve that role — as the 2026-07 review
//!   noted, `publish_lb` bumped it OUTSIDE the incumbent `Mutex` with `Relaxed`
//!   ordering, so an "unchanged epoch" never proved an unchanged bus — and it
//!   was deleted as dead code / a latent misuse trap.

use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

/// Sentinel for "no upper bound published". `i64::MAX` can therefore never be
/// a live bus value; a publish of exactly `i64::MAX` is rejected (indistinct
/// from absent — and useless as a cutoff anyway), which is fail-closed.
const UB_ABSENT: i64 = i64::MAX;
/// Sentinel for "no lower bound published" (mirror of [`UB_ABSENT`]).
const LB_ABSENT: i64 = i64::MIN;

/// PROCESS-SCOPED REPORTING SINK for the best dual any engine has proven.
///
/// # Why a global rather than a threaded handle
///
/// The engine that actually drives the dual on OLL-dominant instances runs
/// inside `solve_optimization_portfolio` -> `..._inner` -> `try_pre_native_oll`,
/// a chain that begins at a PUBLIC entry point carrying no bus. Threading a bus
/// handle down it would change several public signatures purely for
/// observability, while the bus-holding worker (`native-oll-opt`) is a
/// different instance that may prove far less.
///
/// This value can never affect a verdict: it is written only by
/// [`publish_reported_dual_global`], read only for output, and — unlike
/// [`SharedBounds::lb`] — no upgrade, prune, or cutoff consults it. Callers
/// must [`reset_reported_dual_global`] at the start of a solve so a value can
/// never leak from a previous one.
static REPORTED_DUAL_GLOBAL: AtomicI64 = AtomicI64::new(LB_ABSENT);

/// Publishes a REPORTING-ONLY dual bound. Monotone (keeps the max); returns
/// whether it raised the value. Rejected on i64 overflow. See
/// [`REPORTED_DUAL_GLOBAL`] for why this cannot affect soundness.
pub fn publish_reported_dual_global(value: i128) -> bool {
    let Ok(value64) = i64::try_from(value) else {
        return false;
    };
    if value64 == LB_ABSENT {
        return false;
    }
    value64 > REPORTED_DUAL_GLOBAL.fetch_max(value64, Ordering::Relaxed)
}

/// Best reported dual this process has seen, or `None`. Output/telemetry only.
pub fn reported_dual_global() -> Option<i128> {
    match REPORTED_DUAL_GLOBAL.load(Ordering::Relaxed) {
        LB_ABSENT => None,
        value => Some(i128::from(value)),
    }
}

/// Clears the sink. Call at the start of a solve: the value is monotone, so a
/// stale bound from a previous instance would otherwise persist and be reported
/// against the wrong problem.
pub fn reset_reported_dual_global() {
    REPORTED_DUAL_GLOBAL.store(LB_ABSENT, Ordering::Relaxed);
}

/// A lower bound on the objective that is sound over ALL feasible points of
/// the ORIGINAL instance (a "global-sound floor"), typed by source.
///
/// The inner value is private and there is deliberately NO public constructor:
/// every constructor is `pub(crate)`, named for its audited derivation, and
/// documented with that derivation's soundness argument. This is the
/// "typed-by-source" enforcement of design §2.7/§3.1 — `publish_lb` cannot be
/// fed a heuristic / per-worker / non-global bound without adding (and
/// auditing) a new constructor here, which is a reviewed change to THIS file.
pub struct GlobalSoundFloor {
    value: i128,
}

impl GlobalSoundFloor {
    /// AUDITED SOURCE: `crate::cdcl::objective_lower_bound_from_constraints`.
    ///
    /// That floor is derived purely from the ORIGINAL constraint set
    /// (direct / cardinality-covering / surrogate-aggregation bounds) with
    /// checked arithmetic, and is proven sound by:
    /// * the Kani/model-checker-consumer harness `portfolio::kani_optimality_upgrade`
    ///   (`gate_soundness_structural_floor`: the floor never overshoots the
    ///   true optimum), and
    /// * the deductive-checks lemmas `optimum_gate_sound` /
    ///   `optimum_achieved_and_minimal` licensing the `value <= floor =>
    ///   optimal` gate the coordinator applies against it.
    ///
    /// It is the same floor the sequential path already trusts for its
    /// SATISFIABLE -> OPTIMUM upgrade (`portfolio.rs` root
    /// surrogate-aggregation upgrade and `sanitize_optimization_solution`).
    pub(crate) fn from_structural_constraint_floor(value: i128) -> Self {
        Self { value }
    }
}

/// The parallel-portfolio bound bus (design §3.1). See the module docs for the
/// writer/reader contract.
///
/// `ub`/`lb` are stored as `AtomicI64` purely as a TRANSPORT OPTIMIZATION
/// (`std` has no `AtomicI128`); the objective pipeline is i128 throughout, and
/// both boundaries reject-not-truncate. Reads for pruning are wait-free
/// `Relaxed` loads; the incumbent model travels through the `Mutex` slot,
/// which is also the lock the OPTIMUM upgrade decision holds while it
/// re-verifies (S3).
pub struct SharedBounds {
    /// Best VERIFIED incumbent objective value, or [`UB_ABSENT`]. Written only
    /// by the coordinator while holding `incumbent`; read wait-free (Relaxed)
    /// by pruning consumers.
    ub: AtomicI64,
    /// Best GLOBAL-SOUND objective floor, or [`LB_ABSENT`]. Monotonically
    /// non-decreasing; written only through the typed [`GlobalSoundFloor`].
    lb: AtomicI64,
    /// REPORTING-ONLY dual bound, or [`LB_ABSENT`]. Structurally severed from
    /// `lb`: no soundness decision reads this slot. See
    /// [`SharedBounds::publish_reported_dual`].
    reported_dual: AtomicI64,
    /// The model attaining `ub`. Kept in lockstep with `ub` under this Mutex
    /// (every writer holds it); the OPTIMUM upgrade decision locks it for the
    /// whole lock -> read-lb -> re-verify sequence.
    incumbent: Mutex<Option<Arc<[bool]>>>,
}

impl SharedBounds {
    /// Creates an empty bus: no ub (no cutoff), no lb (no floor), no incumbent.
    pub(crate) fn new() -> Self {
        Self {
            ub: AtomicI64::new(UB_ABSENT),
            lb: AtomicI64::new(LB_ABSENT),
            reported_dual: AtomicI64::new(LB_ABSENT),
            incumbent: Mutex::new(None),
        }
    }

    /// Wait-free `Relaxed` read of the published upper bound for PRUNING.
    ///
    /// Absent — never published, rejected on i128->i64 overflow, or the
    /// sentinel-colliding `i64::MAX` — reads as `None` == **"no cutoff"**
    /// (never "0/unbounded-good"). The i64->i128 widening is lossless
    /// (`i128::from`); the bus value is never `as`-cast.
    pub fn ub(&self) -> Option<i128> {
        match self.ub.load(Ordering::Relaxed) {
            UB_ABSENT => None,
            value => Some(i128::from(value)),
        }
    }

    /// Wait-free `Relaxed` read of the published global-sound floor. Absent
    /// reads as `None` == "no floor" (never an upgrade license).
    pub fn lb(&self) -> Option<i128> {
        match self.lb.load(Ordering::Relaxed) {
            LB_ABSENT => None,
            value => Some(i128::from(value)),
        }
    }

    /// COORDINATOR-ONLY (see module docs): publishes a
    /// sanitize-VERIFIED incumbent (exact objective `value`, its `model`) to
    /// the bus. Returns whether the bus adopted it.
    ///
    /// REJECT-NOT-TRUNCATE (§2.7): a `value` that does not fit the i64
    /// transport (or collides with the absent sentinel) is REJECTED — the bus
    /// keeps its previous state and consumers keep reading "no cutoff" /
    /// the previous cutoff. It is never `as`-cast: a truncated ub could be
    /// LOWER than any feasible value, i.e. an unsound cutoff.
    ///
    /// Non-improving publishes (value >= current ub) are ignored, so the bus
    /// ub is strictly decreasing and `ub`/`incumbent` stay a consistent pair
    /// (both only ever replaced together, under the Mutex).
    pub(crate) fn publish_incumbent(&self, value: i128, model: &[bool]) -> bool {
        let Ok(value64) = i64::try_from(value) else {
            // Overflow: reject (no-publish). Consumers read "no cutoff".
            return false;
        };
        if value64 == UB_ABSENT {
            // Sentinel collision: indistinguishable from "absent" on the wire;
            // reject (fail-closed — and worthless as a cutoff regardless).
            return false;
        }
        let Ok(mut slot) = self.incumbent.lock() else {
            // Poisoned slot (a publisher panicked): fail closed, publish
            // nothing further.
            return false;
        };
        let current = self.ub.load(Ordering::Relaxed);
        if current != UB_ABSENT && current <= value64 {
            return false;
        }
        *slot = Some(Arc::from(model));
        self.ub.store(value64, Ordering::Relaxed);
        true
    }

    /// Publishes a GLOBAL-SOUND objective floor (typed-by-source; see
    /// [`GlobalSoundFloor`]). Monotonic: the bus keeps the max of all
    /// published floors. Returns whether the bus adopted (raised) it.
    ///
    /// REJECT-NOT-TRUNCATE mirror of `publish_incumbent`: a floor outside the
    /// i64 transport is rejected — the bus keeps the weaker previous floor
    /// (fail-closed: a missing floor only ever suppresses the OPTIMUM
    /// upgrade, never licenses one).
    pub fn publish_lb(&self, floor: GlobalSoundFloor) -> bool {
        let Ok(value64) = i64::try_from(floor.value) else {
            return false;
        };
        if value64 == LB_ABSENT {
            return false;
        }
        let previous = self.lb.fetch_max(value64, Ordering::Relaxed);
        value64 > previous
    }

    /// Locks and returns the incumbent slot for the S3-ordered OPTIMUM
    /// upgrade decision (lock incumbent -> read lb -> re-verify). Returns
    /// `None` on a poisoned slot (fail-closed: no upgrade).
    pub(crate) fn locked_incumbent(&self) -> Option<MutexGuard<'_, Option<Arc<[bool]>>>> {
        self.incumbent.lock().ok()
    }

    /// REPORTING ONLY. Publishes a worker's best dual bound for HUMAN/telemetry
    /// consumption. Monotonic (keeps the max), rejected on i64 overflow.
    ///
    /// # This is deliberately NOT a [`GlobalSoundFloor`]
    ///
    /// The values that flow here (e.g. the core-guided OLL accumulator) are
    /// floors over the CURRENT SOLVER STATE, not necessarily over the original
    /// instance: OLL's persistent solver may carry an external-UB prune row,
    /// hardening units, or — when the opt-in LP reduced-cost fixer is armed —
    /// level-0 units that delete optimal TIES. Any of those can let the
    /// accumulator exceed the true optimum, which as a `lb` would be an
    /// unretractable false-OPTIMUM license (the upgrade gate `value <= floor`
    /// is one-sided and monotone).
    ///
    /// So this channel is structurally severed from soundness: it is written
    /// through its own slot, and [`SharedBounds::lb`] — the only value the
    /// OPTIMUM upgrade reads — never observes it. A wrong value here can
    /// mislead a human or a benchmark table; it cannot mint a wrong answer.
    /// Promoting any of it to a real floor requires a new audited
    /// [`GlobalSoundFloor`] constructor plus the guards in that audit.
    pub fn publish_reported_dual(&self, value: i128) -> bool {
        let Ok(value64) = i64::try_from(value) else {
            return false;
        };
        if value64 == LB_ABSENT {
            return false;
        }
        value64 > self.reported_dual.fetch_max(value64, Ordering::Relaxed)
    }

    /// Best REPORTED (non-licensing) dual bound, for output/telemetry only.
    /// Never consulted by the OPTIMUM upgrade — see
    /// [`SharedBounds::publish_reported_dual`].
    pub fn reported_dual(&self) -> Option<i128> {
        match self.reported_dual.load(Ordering::Relaxed) {
            LB_ABSENT => None,
            value => Some(i128::from(value)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_bus_reads_no_cutoff_and_no_floor() {
        let bus = SharedBounds::new();
        assert_eq!(bus.ub(), None, "absent ub must read as NO CUTOFF");
        assert_eq!(bus.lb(), None, "absent lb must read as NO FLOOR");
        assert!(bus.locked_incumbent().expect("unpoisoned").is_none());
    }

    #[test]
    fn publish_incumbent_rejects_values_outside_i64() {
        let bus = SharedBounds::new();
        let model = vec![true, false];

        // Too large / too small for the i64 transport: REJECT, never truncate.
        assert!(!bus.publish_incumbent(i128::from(i64::MAX) + 1, &model));
        assert!(!bus.publish_incumbent(i128::from(i64::MIN) - 1, &model));
        assert!(!bus.publish_incumbent(i128::MAX, &model));
        assert!(!bus.publish_incumbent(i128::MIN, &model));
        // Sentinel collision is rejected too.
        assert!(!bus.publish_incumbent(i128::from(i64::MAX), &model));

        // The consumer view after every rejection: NO CUTOFF, empty slot —
        // exactly as if nothing was ever published.
        assert_eq!(bus.ub(), None);
        assert!(bus.locked_incumbent().expect("unpoisoned").is_none());
    }

    #[test]
    fn publish_incumbent_stores_pair_and_only_improves() {
        let bus = SharedBounds::new();
        assert!(bus.publish_incumbent(10, &[true, true]));
        assert_eq!(bus.ub(), Some(10));
        assert_eq!(
            bus.locked_incumbent().expect("unpoisoned").as_deref(),
            Some(&[true, true][..])
        );

        // Non-improving (equal or worse) publishes are ignored; the
        // (ub, incumbent) pair stays consistent.
        assert!(!bus.publish_incumbent(10, &[false, false]));
        assert!(!bus.publish_incumbent(11, &[false, false]));
        assert_eq!(bus.ub(), Some(10));
        assert_eq!(
            bus.locked_incumbent().expect("unpoisoned").as_deref(),
            Some(&[true, true][..])
        );

        // A strict improvement replaces both halves of the pair.
        assert!(bus.publish_incumbent(7, &[false, true]));
        assert_eq!(bus.ub(), Some(7));
        assert_eq!(
            bus.locked_incumbent().expect("unpoisoned").as_deref(),
            Some(&[false, true][..])
        );

        // Negative objective values are legal bus values.
        assert!(bus.publish_incumbent(-3, &[true, false]));
        assert_eq!(bus.ub(), Some(-3));
    }

    #[test]
    fn publish_lb_is_typed_monotonic_and_rejects_overflow() {
        let bus = SharedBounds::new();
        assert!(bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(3)));
        assert_eq!(bus.lb(), Some(3));

        // Monotonic max: lowering attempts are ignored.
        assert!(!bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(1)));
        assert_eq!(bus.lb(), Some(3));
        assert!(bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(9)));
        assert_eq!(bus.lb(), Some(9));

        // Out-of-transport floors are rejected; the weaker floor is kept
        // (fail-closed: never a fabricated/truncated floor).
        assert!(
            !bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(
                i128::from(i64::MAX) + 1
            ))
        );
        assert!(
            !bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(
                i128::from(i64::MIN) - 1
            ))
        );
        assert!(
            !bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(
                i128::from(i64::MIN)
            ))
        );
        assert_eq!(bus.lb(), Some(9));
    }
}
