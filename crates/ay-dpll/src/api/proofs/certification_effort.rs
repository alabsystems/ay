// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The deferred-trust discharge's one count, and the stops that remain (P4a.1).
//!
//! # The count
//!
//! Every nested solve the discharge runs is bounded by conflicts drawn from
//! the OUTER query's own allowance, never by a clock: the query's `:rlimit`
//! when it set one (tighter of it and the ground allowance, as the step (4)
//! precedent does), the ground conflict allowance otherwise. The outer search
//! already ran under that per-SAT-solve bound, so this is the same count in
//! the same unit, not a second one. Nested solves run on the caller's thread,
//! in proof order, so what each one is granted, and so what it decides, is a
//! function of the query alone.
//!
//! The shares of the one count:
//!
//! * step (3), the per-clause discharge: ONE pool of `allowance / POOL_SHARE`
//!   per certification. Every nested solve of every clause draws what is left
//!   and debits what it spent; an empty pool declines with "certification
//!   effort exhausted (spent S of A)", deterministically;
//! * the forged-UNSAT guard: `allowance / GUARD_SHARE`. It is downgrade-only,
//!   so a smaller share can cost at most a downgrade;
//! * step (4)'s whole-problem re-solve: its own limits
//!   (`WHOLE_PROBLEM_RECONFIRMATION_LIMITS` in `executor/unsat_cert.rs`),
//!   a factor over the ground conflict allowance — it re-decides without
//!   the first solve's strengthenings, a deliberately harder search
//!   (#neq-step4-reprice).
//!
//! A decision cap rides along at the ground budget's own ratio
//! ([`DECISIONS_PER_CONFLICT`]), never wider than the outer query's.
//!
//! Accepted gap: the `:rlimit` is per SAT solve and one nested check-sat can
//! run several, so a lane can overshoot the pool. The overshoot is bounded and
//! deterministic.
//!
//! # Round trips
//!
//! A conflict grant bounds each SAT solve of a nested check, not how many
//! solves its DPLL(T) split loop runs: every refinement round arms its SAT
//! solve with the grant again, relative to the solver's own counters. A
//! re-solve whose rounds spend few conflicts therefore ran until it finished
//! or the backstop stopped it. Measured on the deductive-checks set-fold obligation
//! (`tests/fixtures/deductive_checks_set_fold_singleton_obligation.smt2`, release,
//! `:rlimit 400000`): the forged-UNSAT guard ran 3750 round trips, 630 of its
//! 50 000 conflicts, for 21.4 s on an X925 core and 38.9 s on an A725 core,
//! so under deductive-checks's 30 s deadline the backstop decided that query
//! (`unknown`, timeout, on both kinds of core) and a faster host decided it
//! `unsat`.
//!
//! So the guard and every pool lane also run under a grant of split-loop
//! round trips ([`EffortShare::round_trips`]), a count in the unit the split
//! loops already report (`ay_core::resource::enter_work_grant`), entered
//! below the Certify node around the nested solve
//! (`TrustClauseDischargeControls::in_round_trip_grant`). A spent grant stops
//! the solve at the round trip after the last granted one, at the same round
//! on every host, and the solve's `Unknown` names
//! `DeterministicResourceBudget`: a decline, never a stop. Step (4)'s
//! re-solve keeps its own limits and has no round-trip grant; step (4a)'s
//! question and the closed-sentence refutations run on round-trip counts of
//! their own ([`redecision`] says which, and why step (4) has none).
//!
//! # The stops that remain
//!
//! Each is true exhaustion or a backstop, and each reaches the caller as a
//! STOP, never as a rejection ([`EnvelopeStop`]): the caller's interrupt, the
//! outer backstop (the certification deadline on the executor path; none on
//! the proof-export path), process memory and a portfolio lane's memory share,
//! and term-store memory.
//!
//! # The Certify node (GuardTree step S2, DR-39)
//!
//! A certification runs in a Certify node of the GuardTree, built only by
//! [`certify_node`]. It is `CancelOnly`: it sees every cancel above it (the
//! executor interrupt, the process cancel, the lane's memory share) but not
//! the search's deadline, and keeps its own envelope. Proof assembly runs in
//! one, and every nested solve the discharge arms is a `Full` child of the
//! discharge's (`arm_certification_grant`), so a nested certification
//! check-sat obeys that envelope and those cancels and nothing of the search
//! around it, which before S2 its unchained check stop did by hand.

use std::cell::Cell;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use ay_core::resource::{current_guard, ChildSpec, DeadlineSource, Guard, NodeLabel};
use ay_core::time::Instant;

use crate::executor_types::{UnknownOrigin, UnknownReason};
use crate::Executor;

mod redecision;
pub(crate) use redecision::{FirstSolveWork, CLOSED_SENTENCE_REFUTATION_ROUND_TRIPS};

/// The share of the allowance step (3)'s per-clause pool gets
/// (`allowance / POOL_SHARE`).
///
/// PROVISIONAL. It is a share of the one count, not a second count, and it is
/// fitted once, on aterm-codec (plan T-e, by the caller of P4a.1), so that
/// every clause an idle host accepts today still fits. Change it only with
/// that measurement.
pub(crate) const POOL_SHARE: u64 = 4;

/// The share of the allowance the forged-UNSAT guard gets
/// (`allowance / GUARD_SHARE`, at least one conflict). It replaced a 250 ms
/// wall budget that existed only for cost: `group_quantifiers` took 2.7 s with
/// it and 20.1 s without.
const GUARD_SHARE: u64 = 8;

/// The split-loop round trips the forged-UNSAT guard's re-solve may run, the
/// count that replaced its 250 ms wall as the bound on its rounds (its
/// conflict share bounds each round's SAT solve only).
///
/// CALIBRATED, over the corpus that reaches the guard: ay-dpll's lib tests,
/// `group_quantifiers`, `group_proofs`, `group_regression`, `group_auflia`,
/// `group_lia`, `group_bv`, `group_arrays`, `group_theory_misc`, the
/// `deductive_checks_*` targets and `certification_determinism`, on A725 cores. The
/// most round trips any guard re-solve there ran inside the former 250 ms
/// wall was 209: the ground core of
/// `executor_tests::smt::set_fold_pinned_read_proof_fold`, which finishes in
/// 209. Every other guard re-solve finishes in at most 187, except the
/// deductive-checks set-fold obligation (3750), which the wall cut after 38 rounds on
/// an A725 core and 74 on an X925 core. 512 is more than twice 209. It also
/// covers a re-solve from outside the corpus that a reviewer measured
/// finishing 342 round trips inside 250 ms (debug, X925).
///
/// Known residual: rounds are not equally cheap. Outside the corpus, a
/// re-solve of more than 512 rounds averaging under 0.5 ms each would get
/// fewer rounds here than the wall gave it. That costs at most a downgrade
/// the guard would have forced (the guard only ever downgrades), and steps
/// (2) to (4) still have to accept on their own evidence. None was observed.
pub(crate) const GUARD_ROUND_TRIPS: u64 = 512;

/// The split-loop round trips each pool lane's nested solve may run (the
/// entailment lane, the standalone lane, the native BV and array solves),
/// per lane, as the one-second wall per lane that it replaced was.
///
/// CALIBRATED over the same corpus: no lane solve ran more than 143 round
/// trips in all (a standalone lane in `group_auflia`; the entailment lane's
/// most was 60, the native solves' 12), so 512, more than three times 143,
/// covers each of them whole, wherever the former wall cut it. A lane that
/// runs out declines, which fails closed.
pub(crate) const LANE_ROUND_TRIPS: u64 = 512;

/// The ground budget's own decisions-per-conflict ratio (24M / 400k), so a
/// conflict grant carries a decision cap in the same proportion.
const DECISIONS_PER_CONFLICT: u64 =
    Executor::DEFAULT_GROUND_DECISION_ALLOWANCE / Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE;

/// The deferred-trust discharge's one count: conflicts drawn from the outer
/// query's allowance, never a clock. One per certification.
#[derive(Debug)]
pub(crate) struct CertificationEffort {
    allowance: u64,
    pool_size: u64,
    pool: Cell<u64>,
    spent: Cell<u64>,
    exhausted: Cell<bool>,
    decision_cap: Option<u64>,
    first_solve: FirstSolveWork,
}

impl Default for CertificationEffort {
    /// The ground allowance, for a caller with no outer query.
    fn default() -> Self {
        Self::with_allowance(Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE, None)
    }
}

impl CertificationEffort {
    /// The account of a certification of `outer`'s query.
    pub(crate) fn for_query(outer: &Executor) -> Self {
        let ground = Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE;
        let allowance = outer
            .resource_limit()
            .map_or(ground, |limit| limit.min(ground));
        Self {
            first_solve: FirstSolveWork::of(outer),
            ..Self::with_allowance(allowance, outer.decision_limit())
        }
    }

    pub(crate) fn with_allowance(allowance: u64, decision_cap: Option<u64>) -> Self {
        let pool_size = allowance / POOL_SHARE;
        Self {
            allowance,
            pool_size,
            pool: Cell::new(pool_size),
            spent: Cell::new(0),
            exhausted: Cell::new(false),
            decision_cap,
            first_solve: FirstSolveWork::default(),
        }
    }

    /// The first solve's counted work, which sizes step (4a)'s counts (none
    /// for a caller with no outer query: the floors apply).
    pub(crate) fn first_solve(&self) -> FirstSolveWork {
        self.first_solve
    }

    /// The forged-UNSAT guard's grant.
    pub(crate) fn guard_grant(&self) -> u64 {
        (self.allowance / GUARD_SHARE).max(1)
    }

    /// Step (4)'s grant: the whole allowance, as before.
    pub(crate) fn reconfirm_grant(&self) -> u64 {
        self.allowance
    }

    /// The grant of one nested solve on `share`: what is left of the pool, or
    /// a fixed share. `None`: nothing to run on (an empty pool, a zero
    /// allowance, or an outer decision cap of zero).
    pub(crate) fn grant(&self, share: EffortShare) -> Option<u64> {
        if self.decision_cap == Some(0) {
            return None;
        }
        match share {
            EffortShare::Pool => self.draw(),
            EffortShare::Guard => Some(self.guard_grant()),
            EffortShare::Reconfirm => Some(self.reconfirm_grant()).filter(|&grant| grant > 0),
        }
    }

    /// Charge what a nested solve on `share` spent (only the pool keeps an
    /// account; a fixed share is its own bound).
    pub(crate) fn settle(&self, share: EffortShare, conflicts: u64) {
        if share == EffortShare::Pool {
            self.debit(conflicts);
        }
    }

    /// What is left of step (3)'s pool, or `None` once it is spent (which is
    /// remembered: see [`Self::exhaustion`]).
    pub(crate) fn draw(&self) -> Option<u64> {
        let left = self.pool.get();
        if left == 0 {
            self.exhausted.set(true);
            return None;
        }
        Some(left)
    }

    /// Charge `conflicts` a pool draw spent.
    pub(crate) fn debit(&self, conflicts: u64) {
        self.spent.set(self.spent.get().saturating_add(conflicts));
        self.pool.set(self.pool.get().saturating_sub(conflicts));
    }

    /// Conflicts the pool's draws have spent so far.
    pub(crate) fn spent(&self) -> u64 {
        self.spent.get()
    }

    /// "certification effort exhausted (spent S of A)" once a draw found the
    /// pool empty, for the decline that results.
    pub(crate) fn exhaustion(&self) -> Option<String> {
        self.exhausted.get().then(|| {
            format!(
                "certification effort exhausted (spent {} of {})",
                self.spent(),
                self.pool_size
            )
        })
    }

    /// The decision cap that rides with a conflict `grant`.
    pub(crate) fn decision_grant(&self, grant: u64) -> u64 {
        let derived = grant.saturating_mul(DECISIONS_PER_CONFLICT);
        self.decision_cap.map_or(derived, |cap| cap.min(derived))
    }

    /// Arm a fresh nested executor with `grant` conflicts (and its decision
    /// cap), the caller's interrupt and its backstop, its checks under
    /// `certify`. The default ground budget is switched off so it cannot
    /// replace the grant, and quantified solving may not relax the backstop.
    pub(crate) fn arm(
        &self,
        exec: &mut Executor,
        grant: u64,
        backstop: Option<Instant>,
        interrupt: Option<Arc<AtomicBool>>,
        certify: Option<Guard>,
    ) {
        exec.arm_certification_grant(
            grant,
            self.decision_grant(grant),
            backstop,
            interrupt,
            certify,
        );
    }

    /// Arm a fresh native proof-checking solver the same way. Its interrupt
    /// is passed at the solve itself.
    pub(crate) fn arm_native(
        &self,
        solver: &mut super::super::Solver,
        grant: u64,
        backstop: Option<Instant>,
        certify: Option<Guard>,
    ) {
        solver.arm_certification_grant(grant, self.decision_grant(grant), backstop, certify);
    }
}

/// A certification's node (DR-39), built here and nowhere else: `CancelOnly`,
/// with `interrupt` as its external flag, `envelope` as its own deadline and
/// the lane share as its memory, below the thread's current node (the root's
/// on a thread in none).
///
/// Its allotment is DR-39's: fixed now, out of the tick budget B of the
/// check it certifies, as P4a.1's shares of B ([`certify_allotment`]), and
/// deducted from nothing (GT2's `CancelOnly` clause). No check has a tick
/// budget before step S6, so until then it has none and certification keeps
/// its counts in conflicts ([`CertificationEffort`]).
///
/// It hangs below the current node, not the check's own node, while the
/// counts are what they are before S6: a work ceiling or grant the
/// certification runs in still bounds it and counts it
/// (`ay_core::resource`'s caps reach through `CancelOnly`), as the thread's
/// counters did, because DR-39 rejects a certification bounded by a clock
/// alone. S6 moves it to the check's node with its own allotment.
pub(crate) fn certify_node(interrupt: Option<Arc<AtomicBool>>, envelope: DeadlineSource) -> Guard {
    let current = current_guard();
    let budget = current
        .as_ref()
        .and_then(|node| node.nearest(NodeLabel::Check))
        .and_then(|check| check.allotment());
    let spec = ChildSpec::new(NodeLabel::Certify)
        .cancel_only()
        .with_deadline(envelope)
        .with_lane_share()
        .with_rlimit(budget.map(certify_allotment));
    let spec = match interrupt {
        Some(flag) => spec.with_external(flag),
        None => spec,
    };
    match current {
        Some(parent) => parent.child(spec),
        None => Guard::root_child(spec),
    }
}

/// What DR-39 reserves for Certify out of a check's tick budget B: step
/// (3)'s pool B / [`POOL_SHARE`], the forged-UNSAT guard's B / `GUARD_SHARE`
/// (at least one), and step (4)'s re-solve, the whole of B.
fn certify_allotment(budget: u64) -> u64 {
    (budget / POOL_SHARE)
        .saturating_add((budget / GUARD_SHARE).max(1))
        .saturating_add(budget)
}

/// Which share of the one count a nested solve runs on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EffortShare {
    /// Step (3)'s per-clause pool: draw what is left, debit what is spent.
    Pool,
    /// The forged-UNSAT guard's fixed share.
    Guard,
    /// Step (4)'s whole-problem re-solve: the whole allowance.
    Reconfirm,
}

impl EffortShare {
    /// The split-loop round trips a nested solve on this share may run
    /// ([`GUARD_ROUND_TRIPS`], [`LANE_ROUND_TRIPS`]). `None` for step (4)'s
    /// re-solve, which keeps its own limits.
    pub(crate) const fn round_trips(self) -> Option<u64> {
        match self {
            Self::Guard => Some(GUARD_ROUND_TRIPS),
            Self::Pool => Some(LANE_ROUND_TRIPS),
            Self::Reconfirm => None,
        }
    }
}

/// A stop that ended discharge lanes: true exhaustion or a backstop, never
/// evidence about the proof. Published as `Unknown(Interrupted | Timeout |
/// MemoryLimit | ResourceLimit | Unknown)`, never as a rejection. Opaque caller
/// stops remain Unknown rather than inventing an interrupt or memory cause.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EnvelopeStop {
    /// The caller's interrupt.
    Interrupt,
    /// The outer backstop (a wall/CPU limit), or a lane-local wall clock that
    /// ended a lane whose decline the funnel then returned.
    Backstop,
    /// The executor's or the process's memory ceiling (an RSS reading).
    ProcessMemory,
    /// A portfolio lane's or captured GuardTree node's memory share.
    LaneShare,
    /// The term-store memory ceiling (a count of term-store bytes).
    TermMemory,
    /// An explicit original caller withdrew permission without naming a cause.
    Caller,
    /// A caller-owned GuardTree work count was already spent.
    WorkLimit,
}

impl EnvelopeStop {
    /// How the stop is published: its `Unknown` origin, reason and detail.
    /// `TermMemory` keeps the "term-store memory ceiling" phrase consumers
    /// read to tell the count from an RSS reading.
    pub(crate) fn unknown(self) -> (UnknownOrigin, UnknownReason, &'static str) {
        match self {
            Self::Interrupt => (
                UnknownOrigin::InterruptFlag,
                UnknownReason::Interrupted,
                "interrupt requested while UNSAT certification was running",
            ),
            Self::Backstop => (
                UnknownOrigin::SolveDeadline,
                UnknownReason::Timeout,
                "a wall-clock or CPU limit stopped UNSAT certification before it decided",
            ),
            Self::ProcessMemory => (
                UnknownOrigin::MemoryBudget,
                UnknownReason::MemoryLimit,
                "process memory ceiling exceeded while UNSAT certification was running",
            ),
            Self::LaneShare => (
                UnknownOrigin::MemoryBudget,
                UnknownReason::MemoryLimit,
                "a resource memory share exceeded while UNSAT certification was running",
            ),
            Self::TermMemory => (
                UnknownOrigin::MemoryBudget,
                UnknownReason::MemoryLimit,
                "executor term-store memory ceiling exceeded while UNSAT certification was \
                 running",
            ),
            Self::Caller => (
                UnknownOrigin::UntaggedSolverUnknown,
                UnknownReason::Unknown,
                "the original caller stopped UNSAT certification without a typed cause",
            ),
            Self::WorkLimit => (
                UnknownOrigin::DeterministicResourceBudget,
                UnknownReason::ResourceLimit,
                "the original caller's work budget stopped UNSAT certification",
            ),
        }
    }

    /// The stop a nested solve's `Unknown` origin names, if it is one. A
    /// deadline is classified by the caller (`backstop_passed`): the outer
    /// backstop's, or a lane-local clock's.
    pub(crate) fn of_nested_origin(
        origin: Option<UnknownOrigin>,
        term_store_tripped: bool,
    ) -> Option<NestedStop> {
        match origin? {
            UnknownOrigin::InterruptFlag => Some(NestedStop::Envelope(Self::Interrupt)),
            UnknownOrigin::SolveDeadline => Some(NestedStop::Deadline),
            UnknownOrigin::MemoryBudget => Some(NestedStop::Envelope(if term_store_tripped {
                Self::TermMemory
            } else if ay_sys::current_memory_group_soft_tripped() {
                Self::LaneShare
            } else {
                Self::ProcessMemory
            })),
            _ => None,
        }
    }
}

impl std::fmt::Display for EnvelopeStop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.unknown().2)
    }
}

/// What a nested solve's `Unknown` says about the envelope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NestedStop {
    /// An envelope stop the nested solve observed.
    Envelope(EnvelopeStop),
    /// A wall-clock deadline: the outer backstop's or a lane-local one's.
    Deadline,
}

#[cfg(test)]
#[path = "certification_effort_tests.rs"]
mod tests;
