// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counted rounds of the eager-persistent split-loop arm (P4a, T2).
//!
//! The arm (`pipeline_incremental_split_eager_persistent_macros.rs`) slices one
//! SAT search into rounds: when a round's slice runs out and nothing new was
//! learned, the next round resumes or continues the same search (#8256, #8399).
//! The slice used to be a wall-clock window (120 s, then 30 s, 15 s, or 500 ms
//! plus 200 ms per iteration), so how many rounds a query took, where each
//! resume landed and whether a stall escalated all followed the host's speed,
//! and the search itself had no `:rlimit` at all.
//!
//! Now every bound the arm itself sets is a count:
//!
//! * A round's own slice is a number of DECISIONS (theory-heavy LRA search is
//!   conflict-light, so a conflict slice would barely move): the former window
//!   at [`DECISIONS_PER_MS`]. Iteration 0 has no slice of its own.
//! * The search the rounds slice is bounded by the check-sat's `:rlimit`
//!   conflict allowance and its decision companion, the ones every other
//!   split-loop arm arms (`effective_conflict_allowance`,
//!   `effective_decision_allowance`). When that allowance stops the search, the
//!   arm publishes `unknown` (`resourceout`); when only the round's slice
//!   stopped it, the arm continues the search.
//!
//! The arm reads no clock of its own. The far backstop (`make_should_stop`:
//! the interrupt and the solve deadline) still ends a search, and its firing
//! is published as that stop. One wall clock inside the SAT solve is not the
//! arm's and is not yet closed: unless `--sat-deterministic-inproc` is on (it
//! is off by default), ay-sat caps its restart inprocessing rounds and its
//! lookahead by wall time, so on a loaded host such a pass can stop early,
//! leave a different clause database and move where the counts stop the
//! search. That is ay-sat's residual for every lane (`ay_sat::determinism`
//! says which walls the flag counts instead); it never ends a search or
//! decides a verdict by itself.
//!
//! Until GuardTree S6 (the development design notes) `:rlimit` keeps its
//! per-SAT-solve meaning. Here one SAT solve is one search: a round after the
//! clause set changed (a split, a refinement, a lemma, a blocking clause)
//! starts a new search with a fresh allowance, and the rounds that resume or
//! continue a search draw on what its allowance has left.

use ay_sat::{SatUnknownReason, Solver as SatSolver};

/// Decisions per millisecond of eager-persistent SAT search, the rate that
/// turns the former per-round wall windows into decision slices: the pooled
/// `:decisions` over `:time.dpll.sat_solve` (`ay -st --stats-full -T:120`,
/// plain posture, origin/main ffaba97f62 release build, one process at a time
/// on an 18-core host at load 20-30, 2026-10-10) over the QF_LRA files the
/// arm's comments name, 15,189,543 decisions in 479.9 s:
///
/// | file | decisions | SAT search | per ms |
/// |---|---:|---:|---:|
/// | sc-8.induction2 | 12,204 | 0.35 s | 35 |
/// | sc-8.induction3 | 9,847 | 0.55 s | 18 |
/// | simple_startup_10nodes.bug.induct | 4,790,568 | 119.9 s | 40 |
/// | simple_startup_14nodes.bug.induct | 5,684,933 | 119.9 s | 47 |
/// | simple_startup_7nodes.abstract.induct | 3,794,417 | 119.9 s | 32 |
/// | 0165-labyrinth-13-0 | 862,756 | 116.1 s | 7 |
/// | 0067-labyrinth-18-0 | 34,818 | 3.1 s | 11 |
///
/// The labyrinths solve (or time out) in iteration 0, which has no slice, so
/// the rate only sizes the rounds after a split.
pub(crate) const DECISIONS_PER_MS: u64 = 32;

/// The former window of a resume round (#8256).
const RESUME_WINDOW_MS: u64 = 30_000;
/// The former window of a continue round (#8399's stall fallback).
const CONTINUE_WINDOW_MS: u64 = 15_000;
/// The former window of any other round after the first: 500 ms plus 200 ms
/// per iteration, at most 30 s.
const SPLIT_WINDOW_BASE_MS: u64 = 500;
const SPLIT_WINDOW_STEP_MS: u64 = 200;
const SPLIT_WINDOW_CAP_MS: u64 = 30_000;

/// How a round enters the SAT search.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RoundEntry {
    /// `solve_interruptible_with_extension`. Every full solve restarts the
    /// solver's per-solve decision counter at zero.
    Full,
    /// `continue_solving_with_extension`: trail reset, counters kept.
    Continue,
    /// `resume_solving_with_extension`: counters and learned clauses kept; the
    /// trail restarts from level 0.
    Resume,
}

impl RoundEntry {
    /// The entry the arm's two flags select (resume wins, as in the arm).
    pub(crate) fn of(resume: bool, continue_solving: bool) -> Self {
        if resume {
            Self::Resume
        } else if continue_solving {
            Self::Continue
        } else {
            Self::Full
        }
    }
}

/// The round's own decision slice: none at iteration 0, which has only its
/// search's allowance, and otherwise the calibrated round size at
/// [`DECISIONS_PER_MS`], divided by `divisor` (1 in every production build:
/// `ay_core::resource::round_seam::slice_divisor`; a determinism test shrinks
/// it), and never below one decision.
pub(crate) fn round_slice(iteration: usize, entry: RoundEntry, divisor: u64) -> Option<u64> {
    if iteration == 0 {
        return None;
    }
    let window_ms = match entry {
        RoundEntry::Resume => RESUME_WINDOW_MS,
        RoundEntry::Continue => CONTINUE_WINDOW_MS,
        RoundEntry::Full => {
            let iteration = u64::try_from(iteration).unwrap_or(u64::MAX);
            SPLIT_WINDOW_BASE_MS
                .saturating_add(SPLIT_WINDOW_STEP_MS.saturating_mul(iteration))
                .min(SPLIT_WINDOW_CAP_MS)
        }
    };
    Some((window_ms.saturating_mul(DECISIONS_PER_MS) / divisor.max(1)).max(1))
}

/// The solver's counters a round is armed and settled against.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SolverCounts {
    /// `num_conflicts`, the counter the conflict budget is compared with.
    pub(crate) conflicts: u64,
    /// `num_decisions`, the counter the decision budget is compared with.
    pub(crate) decisions: u64,
    /// `total_num_conflicts`: monotone across every reset, since a full reset
    /// folds `num_conflicts` into it and an incremental one keeps it.
    pub(crate) lifetime_conflicts: u64,
    /// Whether a full solve can keep `num_conflicts` running: only an IC3-mode
    /// solver (the incremental QF_LRA engine lane's) does, on its incremental
    /// reset. Every other reset restarts it at zero.
    pub(crate) full_solve_may_keep_conflicts: bool,
}

impl SolverCounts {
    pub(crate) fn of(solver: &SatSolver) -> Self {
        Self {
            conflicts: solver.num_conflicts(),
            decisions: solver.num_decisions(),
            lifetime_conflicts: solver.total_num_conflicts(),
            full_solve_may_keep_conflicts: solver.is_ic3_mode(),
        }
    }
}

/// What the current search may still spend.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct SearchAllowance {
    /// The lifetime conflict count at which the conflict allowance is spent.
    conflicts_end: Option<u64>,
    /// Decisions still allowed. Charged per round, because a full solve
    /// restarts `num_decisions` at zero and an IC3-mode incremental reset does
    /// so without adding it to the solver's lifetime decision count.
    decisions_left: Option<u64>,
}

impl SearchAllowance {
    /// A new search's allowance: `conflicts` and `decisions` from now (`None`
    /// is unbounded).
    pub(crate) fn fresh(conflicts: Option<u64>, decisions: Option<u64>, now: SolverCounts) -> Self {
        Self {
            conflicts_end: conflicts.map(|n| now.lifetime_conflicts.saturating_add(n)),
            decisions_left: decisions,
        }
    }

    fn conflicts_left(&self, now: SolverCounts) -> Option<u64> {
        self.conflicts_end
            .map(|end| end.saturating_sub(now.lifetime_conflicts))
    }

    fn spent(&self, now: SolverCounts) -> bool {
        self.decisions_left == Some(0) || self.conflicts_left(now) == Some(0)
    }
}

/// One round's armed budgets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RoundBudget {
    /// For `set_conflict_budget`: absolute, against `num_conflicts`.
    pub(crate) conflict_target: Option<u64>,
    /// For `set_decision_budget`: absolute, against `num_decisions`.
    pub(crate) decision_target: Option<u64>,
    /// `num_decisions` at the round's start as its solve counts it.
    decision_base: u64,
    /// The decision target is the round's own slice, tighter than what the
    /// search has left.
    slice_binds: bool,
}

/// Arm a round: the conflicts the search has left and the smaller of the
/// round's slice and the decisions the search has left, each counted from
/// where the round's solve starts its counter.
///
/// A full solve restarts `num_decisions` at zero, and `num_conflicts` too
/// unless the solver is in IC3 mode (whose incremental reset keeps it running,
/// and whose fallback full reset restarts it: there the target, counted from
/// now, allows at most the earlier count more, and the measured spend ends the
/// search at the next round). A resume or continue keeps both counters.
pub(crate) fn arm_round(
    search: &SearchAllowance,
    slice: Option<u64>,
    entry: RoundEntry,
    now: SolverCounts,
) -> RoundBudget {
    let (conflict_base, decision_base) = match entry {
        RoundEntry::Full if now.full_solve_may_keep_conflicts => (now.conflicts, 0),
        RoundEntry::Full => (0, 0),
        RoundEntry::Continue | RoundEntry::Resume => (now.conflicts, now.decisions),
    };
    let conflict_target = search
        .conflicts_left(now)
        .map(|left| conflict_base.saturating_add(left));
    let (decisions, slice_binds) = match (slice, search.decisions_left) {
        (Some(slice), Some(left)) if slice < left => (Some(slice), true),
        (Some(slice), None) => (Some(slice), true),
        (_, left) => (left, false),
    };
    RoundBudget {
        conflict_target,
        decision_target: decisions.map(|n| decision_base.saturating_add(n)),
        decision_base,
        slice_binds,
    }
}

/// Settle a round after its solve: charge its decisions to the search, and
/// answer whether the round's OWN slice is what stopped the solve, so the arm
/// continues the search. Anything else that ended the solve on a budget is the
/// search's allowance (or a count the arm does not own), which the arm
/// publishes as `resourceout`; a search with nothing left never continues.
pub(crate) fn settle_round(
    search: &mut SearchAllowance,
    budget: &RoundBudget,
    stop: Option<SatUnknownReason>,
    after: SolverCounts,
) -> bool {
    let spent = after.decisions.saturating_sub(budget.decision_base);
    if let Some(left) = search.decisions_left.as_mut() {
        *left = left.saturating_sub(spent);
    }
    let slice_reached = budget
        .decision_target
        .is_some_and(|target| after.decisions >= target);
    let conflicts_reached = budget
        .conflict_target
        .is_some_and(|target| after.conflicts >= target);
    stop == Some(SatUnknownReason::ResourceBudget)
        && budget.slice_binds
        && slice_reached
        && !conflicts_reached
        && !search.spent(after)
}

#[cfg(test)]
#[path = "eager_persistent_rounds_tests.rs"]
mod tests;
