// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What a CHC proof run's meter publishes ([`ChcRunWork`]).

use ay_core::resource::{Exhausted, WorkSnapshot};

/// The metered work of one CHC proof run (guard-tree.md §13).
///
/// `ticks` is the run node's ledger: the one count an effort bounds. The other
/// fields say what it is made of, and what the search reached. Without an
/// effort none of them decided anything in the run; with one, `stop` is the
/// count's (or a backstop's) latched stop. A structural size is not here:
/// ay-chc has none before P4a slice 11's `query_size`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcRunWork {
    /// Every tick charged to the run's node and below it (a nested run's
    /// included): `sat_ticks + smt_entries + theory_rounds + pdr_iterations
    /// + obligations` when no run is nested in it, before GuardTree S6.
    /// From S6 an executor sub-check's Check node ticks too, and its ticks
    /// reach this ledger (GT5), so `ticks` is at least that sum.
    pub ticks: u64,
    /// ay-sat search ticks of the SAT solves ay-chc ran itself.
    pub sat_ticks: u64,
    /// Calls of `SmtContext`-family entry points (a query handed from one
    /// entry to another counts at each).
    pub smt_entries: u64,
    /// DPLL(T) rounds of ay-chc's own theory loops.
    pub theory_rounds: u64,
    /// PDR main-loop iterations.
    pub pdr_iterations: u64,
    /// Proof obligations PDR processed.
    pub obligations: u64,
    /// Frames of the last PDR search the run stepped (0 if none ran).
    pub frames: u64,
    /// Lemmas in those frames when it was last stepped.
    pub lemmas: u64,
    /// Work reported to the process ledger while the run's node was current
    /// on its thread (GT5): executor lanes, ay-sat's own solves. A run
    /// under an effort is never the current node (the module doc), so its
    /// ledger holds only what runs nested in it reported.
    pub ledger: WorkSnapshot,
    /// The run's tick budget, its node's allotment: the caller's effort B,
    /// capped by the remainder of a node that counts around the run; `None`
    /// without an effort.
    pub effort: Option<u64>,
    /// Under an effort, the sub-checks the closed executor route answered
    /// `unknown` (P4a slice 8): each executor session it refused, each
    /// internal `unknown` that `check_sat`'s executor fallback would have
    /// retried, and each BMC run (an unsafe precheck, a counterexample
    /// replay, the acyclic certificate) it did not start
    /// (`BmcSolver::closed_under_effort`). An upper bound on the answers the
    /// closed route cost the run, which slice 14 recovers; 0 without an
    /// effort.
    pub closed_route_checks: u64,
    /// Under an effort, what stopped the run, as its node latched it:
    /// `Rlimit` once the run spent its effort (the count's stop, the same on
    /// every host); otherwise a backstop's, never the count's: `Deadline`
    /// (the run's solve timeout, its node's own deadline), `Cancelled` (the
    /// run's token, or a cancel of the chain above it), `Memory` (the process
    /// memory budget). A charge latches it where the work is stopped (a
    /// clock on the stride, GT3), and a run that ended without a verdict is
    /// settled at its close, so a backstop that fired after the last charge
    /// is named too (`RunMeter::settle`). `None` without an effort, or when
    /// nothing stopped the run: it decided, or its search gave up on its own.
    pub stop: Option<Exhausted>,
}

impl ChcRunWork {
    /// The totals as a JSON object (field names as above).
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "ticks": self.ticks,
            "sat_ticks": self.sat_ticks,
            "smt_entries": self.smt_entries,
            "theory_rounds": self.theory_rounds,
            "pdr_iterations": self.pdr_iterations,
            "obligations": self.obligations,
            "frames": self.frames,
            "lemmas": self.lemmas,
            "ledger": {
                "sat_conflicts": self.ledger.sat_conflicts,
                "sat_decisions": self.ledger.sat_decisions,
                "split_round_trips": self.ledger.split_round_trips,
                "deadline_shares": self.ledger.deadline_shares,
                "deadline_shares_spent": self.ledger.deadline_shares_spent,
            },
            "closed_route_checks": self.closed_route_checks,
            "effort": self.effort,
            "stop": self.stop.map(Exhausted::reason),
        })
    }
}
