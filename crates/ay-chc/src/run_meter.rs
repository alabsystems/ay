// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The work of one CHC proof run, metered on a GuardTree node (P4a slice 7;
//! the development design notes §13).
//!
//! A proof run (`engines::solve_pdr_proof` and its string and file forms,
//! `engines::solve_bmc_proof`, `engines::prove_external_invariant_model`)
//! opens a `Run` node with no allotment and enters it on its thread for the
//! run's extent (GT4). The run charges that node, in ticks:
//!
//! * the ay-sat search ticks of every SAT solve ay-chc runs itself (the
//!   DPLL(T) loop's, which carries the bit-blasted BV clauses, and the
//!   assumption, Horn-session and incremental-PDR loops'), read off the
//!   solver around each solve;
//! * 1 per call of an `SmtContext`-family entry point (an SMT entry). An
//!   entry that hands its query to another entry (an empty assumption list
//!   to `check_sat`, an executor `unknown` to a fresh query) is charged at
//!   each, so one query may cost 2;
//! * 1 per DPLL(T) round, PDR main-loop iteration and processed proof
//!   obligation.
//!
//! Work reported to the process ledger while the node is the thread's
//! current node goes to its ledger too (GT5): the executor lanes a sub-check
//! runs, ay-sat's own reports at its stop polls, restarts and solve ends. An
//! executor lane charges no tick before GuardTree S6, so its search is in the
//! node's ledger as conflicts and decisions and costs the run 1 tick, its SMT
//! entry.
//!
//! **Without an effort the count decides nothing.** `Guard::record_ticks`
//! reads no limit and latches no reason, and the node has no deadline, flag,
//! allotment or memory share of its own. It hangs below the thread's current
//! node (the root on a thread in none), so every limit around the run still
//! reaches everything below it. A poll inside an executor sub-check reads what
//! it read before the node existed; one made in the run node itself on a
//! thread that was in no node would now read the root's process-memory
//! condition besides the process cancel, and ay-chc makes no poll there that
//! reads it newly (guard-tree.md §13 says why). Below a node that counts (an
//! allotment) the run opens no node and is not metered: a node there would
//! take the whole remainder, and its charges would shrink every sub-check's
//! grant. The totals ([`ChcRunWork`]) are published on the run
//! (`ChcPdrProofRun::work`) and enter none of its metadata, artifacts or
//! digests: they are a function of the search's trajectory, which a clock can
//! still steer (the census in guard-tree.md §13).
//!
//! **With an effort B (P4a slice 8, guard-tree.md §14) the count is the run's
//! one stop.** The run's node is allotted B ticks (`with_rlimit`): a `Full`
//! child of the counting run around it on this thread, else of the thread's
//! current node, so a node that counts above the run caps B by its own
//! remainder. Every charge is a `Guard::tick`, which latches the first stop
//! it reads (`Rlimit` once the run has spent B), and the charge's caller acts
//! on it: an SMT entry and a DPLL(T) round answer `unknown`, and the PDR
//! loops stop through `is_cancelled`, which reads the latched stop
//! ([`run_stopped`]). Every SAT solve ay-chc runs itself is armed with the
//! run's remainder as its caller tick stop and its per-solver counted
//! inprocessing ([`sat_solve`]). The node is not entered on the thread: an
//! entered node with an allotment would make every executor check-sat opened
//! in the run a `Full` child granted its whole remainder, and put the
//! executor's deadline shares on GuardTree S6's tick path; not entered, an
//! executor check hangs where it hung before slice 7. Under an effort no
//! sub-check takes the executor route, and no BMC runs ([`counting`],
//! [`close_route`]: slice 14 opens both as children of this node, after S6).
//! A run with no effort inside a counting run opens no node of its own and
//! draws on that one (its work is `None`): the one count bounds everything
//! inside B.
//!
//! Only a node a run opened is charged, on the thread that opened it. A check
//! on another thread, or outside every run (the CLI's portfolio, a consumer's
//! own `SmtContext`), charges nothing; the portfolio's worker nodes are
//! GuardTree S5's, children of a node like this one.

use std::cell::{Cell, RefCell};

use ay_core::resource::{current_guard, ChildSpec, EnterScope, Exhausted, Guard, NodeLabel};
use ay_core::time::Instant;

mod work;
pub use work::ChcRunWork;

/// A unit step the run is charged 1 tick for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Step {
    /// A call of an `SmtContext`-family entry point.
    SmtEntry,
    /// A DPLL(T) round.
    TheoryRound,
    /// A PDR main-loop iteration.
    PdrIteration,
    /// A processed proof obligation.
    Obligation,
}

#[derive(Default)]
struct Counts {
    sat_ticks: Cell<u64>,
    smt_entries: Cell<u64>,
    theory_rounds: Cell<u64>,
    pdr_iterations: Cell<u64>,
    obligations: Cell<u64>,
    frames: Cell<u64>,
    lemmas: Cell<u64>,
    closed_route_checks: Cell<u64>,
}

fn bump(cell: &Cell<u64>, by: u64) {
    cell.set(cell.get().saturating_add(by));
}

/// An open run. `node` is `None` for a run that is not metered (one opened
/// with no effort below a node that counts and is not a run's): it stands on
/// the stack so that the charges made inside it reach no run around it
/// either.
struct Open {
    id: u64,
    node: Option<Guard>,
    /// The charges are ticks against `node`'s allotment, whose stops are
    /// acted on (an effort): this run's own, or the counting run's it draws
    /// on.
    counting: bool,
    /// `node` is this run's own, so it publishes the node's work; `false` for
    /// a run with no effort drawing on the counting run around it.
    owns_node: bool,
    counts: Counts,
}

thread_local! {
    /// The runs open on this thread, innermost last.
    static RUNS: RefCell<Vec<Open>> = const { RefCell::new(Vec::new()) };
    /// Identities of meters opened on this thread.
    static NEXT_ID: Cell<u64> = const { Cell::new(0) };
}

/// `f` on the node and counts of the innermost run open on this thread, and
/// whether its charges count, if it is metered; `None` otherwise. `f` must
/// not open or close a run.
fn with_run<R>(f: impl FnOnce(&Guard, &Counts, bool) -> R) -> Option<R> {
    RUNS.try_with(|runs| {
        let runs = runs.try_borrow().ok()?;
        match runs.last()? {
            Open {
                node: Some(node),
                counts,
                counting,
                ..
            } => Some(f(node, counts, *counting)),
            Open { node: None, .. } => None,
        }
    })
    .ok()
    .flatten()
}

/// Spend `cost` on the run's node: a tick whose stop is the caller's to act
/// on under an effort, else a charge that reads nothing.
fn spend(node: &Guard, counting: bool, cost: u64) -> Result<(), Exhausted> {
    if counting {
        node.tick(cost)
    } else {
        node.record_ticks(cost);
        Ok(())
    }
}

/// Charge the innermost open run 1 tick for `step`. `Err` only under an
/// effort: the run must stop (its latched stop, `Rlimit` once B is spent),
/// and the caller answers `unknown` or ends its loop.
pub(crate) fn charge(step: Step) -> Result<(), Exhausted> {
    with_run(|node, counts, counting| {
        let cell = match step {
            Step::SmtEntry => &counts.smt_entries,
            Step::TheoryRound => &counts.theory_rounds,
            Step::PdrIteration => &counts.pdr_iterations,
            Step::Obligation => &counts.obligations,
        };
        bump(cell, 1);
        spend(node, counting, 1)
    })
    .unwrap_or(Ok(()))
}

/// Charge the innermost open run the search ticks a SAT solve spent. `Err`
/// as for [`charge`]: the solve's answer stands, and the next charge or
/// `is_cancelled` ends the work.
fn charge_sat_ticks(spent: u64) -> Result<(), Exhausted> {
    if spent == 0 {
        return Ok(());
    }
    with_run(|node, counts, counting| {
        bump(&counts.sat_ticks, spent);
        spend(node, counting, spent)
    })
    .unwrap_or(Ok(()))
}

/// Charge the innermost open run `cost` search ticks, as a SAT solve's
/// charge does: for tests that need a run to have spent a given count.
#[cfg(test)]
pub(crate) fn charge_ticks_for_tests(cost: u64) -> Result<(), Exhausted> {
    charge_sat_ticks(cost)
}

/// Run one SAT solve ay-chc runs itself, and charge the innermost open run
/// what it spent: the difference of the solver's lifetime search ticks
/// around it (every solve entry zeroes the per-solve count). Under an effort
/// the solve is armed first ([`Armed`]), with the run's remainder as its
/// caller tick stop (`Solver::set_search_tick_stop`; the solve entries this
/// crate calls start their count from zero, so the remainder, not the count
/// plus it) and its per-solver counted inprocessing
/// (`Solver::set_deterministic_inproc`, never the process-wide switch), so
/// the solve ends at the same tick on every host.
pub(crate) fn sat_solve<R>(
    sat: &mut ay_sat::Solver,
    solve: impl FnOnce(&mut ay_sat::Solver) -> R,
) -> R {
    let stop =
        with_run(|node, _, counting| counting.then(|| node.remaining().unwrap_or(0))).flatten();
    let armed = Armed::arm(sat, stop);
    let before = armed.sat.lifetime_search_ticks();
    let result = solve(&mut *armed.sat);
    let spent = armed.sat.lifetime_search_ticks().saturating_sub(before);
    drop(armed);
    // A stop is read where the work goes on: the solve's answer stands.
    let _ = charge_sat_ticks(spent);
    result
}

/// A SAT solver armed for one solve under an effort ([`sat_solve`]). The caller
/// tick stop and the per-solver counted inprocessing it had are put back when
/// this drops, on an unwind too: a panic `catch_ay_panics` catches inside a
/// solve on a persistent solver (a Horn session's, an incremental PDR
/// context's) leaves it as it was, never armed with a stale remainder.
struct Armed<'a> {
    sat: &'a mut ay_sat::Solver,
    /// The stop and the counted switch to put back; `None`: nothing was armed.
    before: Option<(Option<u64>, bool)>,
}

impl<'a> Armed<'a> {
    fn arm(sat: &'a mut ay_sat::Solver, stop: Option<u64>) -> Self {
        let before = stop.map(|stop| {
            let before = (sat.caller_search_tick_stop(), sat.deterministic_inproc());
            sat.set_search_tick_stop(Some(stop));
            sat.set_deterministic_inproc(true);
            before
        });
        Self { sat, before }
    }
}

impl Drop for Armed<'_> {
    fn drop(&mut self) {
        if let Some((stop, counted)) = self.before {
            self.sat.set_search_tick_stop(stop);
            self.sat.set_deterministic_inproc(counted);
        }
    }
}

/// Whether the innermost open run counts (it has an effort, or draws on a
/// run that does): its sub-checks stay on ay-chc's internal path, and the
/// executor route is not taken (P4a slice 8; slice 14 opens it as a child
/// of the run's node after GuardTree S6).
pub(crate) fn counting() -> bool {
    with_run(|_, _, counting| counting).unwrap_or(false)
}

/// Note a sub-check the closed executor route answered `unknown` in the
/// innermost counting run (`ChcRunWork::closed_route_checks`); `true` when a
/// counting run is open, so the caller closes the route.
pub(crate) fn close_route() -> bool {
    with_run(|_, counts, counting| {
        if counting {
            bump(&counts.closed_route_checks, 1);
        }
        counting
    })
    .unwrap_or(false)
}

/// Whether the innermost open run counts and its node latched a stop: the
/// run must end (`is_cancelled`).
pub(crate) fn run_stopped() -> bool {
    with_run(|node, _, counting| counting && node.stopped().is_some()).unwrap_or(false)
}

/// The ticks the innermost counting run has spent against its effort, or
/// `None` when the innermost run does not count: under an effort the PDR
/// frame stall is measured in them.
pub(crate) fn counted_ticks() -> Option<u64> {
    with_run(|node, _, counting| counting.then(|| node.ticks())).flatten()
}

/// Record where the innermost open run's PDR search is: its frame count and
/// the lemmas in them. The last reading stands.
pub(crate) fn note_frames(frames: usize, lemmas: usize) {
    with_run(|_, counts, _| {
        counts.frames.set(u64::try_from(frames).unwrap_or(u64::MAX));
        counts.lemmas.set(u64::try_from(lemmas).unwrap_or(u64::MAX));
    });
}

/// One run's meter: its node is charged until [`Self::close`] (or a drop,
/// which publishes nothing), entered on this thread when the run has no
/// effort. A meter opened with no effort below a node that counts and is not
/// a run's opens no node, and nothing charged inside it reaches any run.
#[must_use = "the run's node closes when its meter is dropped"]
pub(crate) struct RunMeter {
    id: u64,
    // Dropped after `Drop::drop` has removed the run's entry, on this thread.
    _inside: Option<EnterScope>,
}

/// The node of the innermost run open on this thread, if that run counts.
fn counting_run() -> Option<Guard> {
    with_run(|node, _, counting| counting.then(|| node.clone())).flatten()
}

impl RunMeter {
    /// Open a run's node. With an effort B: a `Run` node allotted B, whose
    /// own deadline is the run's `backstop` (its solve timeout), below the
    /// counting run around it on this thread or else the thread's current
    /// node (the root on a thread in none), not entered. With none: inside a
    /// counting run, no node of its own (it draws on that run's); else a
    /// `Run` node with nothing of its own below the thread's current node,
    /// entered, or nothing at all below a node that counts. Without an effort
    /// the backstop is not read: the node decides nothing (§13).
    ///
    /// The backstop on the node only names a stop the run's own clocks
    /// already make (the solve deadline every check on the thread reads), so
    /// a backstop that fires is published as one, never as an `unknown` the
    /// search reached itself (plan R4): a charge past it latches `Deadline`
    /// on the clock stride, and [`Self::settle`] reads it once more at the end.
    pub(crate) fn open(effort: Option<u64>, backstop: Option<Instant>) -> Self {
        let around = counting_run();
        let (node, counting, owns_node, inside) = match (effort, around) {
            (Some(effort), around) => {
                let spec = ChildSpec::new(NodeLabel::Run)
                    .with_rlimit(Some(effort))
                    .with_deadline(backstop.into());
                let node = match around.or_else(current_guard) {
                    Some(parent) => parent.child(spec),
                    None => Guard::root_child(spec),
                };
                (Some(node), true, true, None)
            }
            (None, Some(around)) => (Some(around), true, false, None),
            (None, None) => {
                let parent = current_guard();
                // Below a node with an allotment a child with no request is
                // granted the whole remainder, the sub-checks' grants would
                // come out of what the run's charges leave, and the count
                // would decide. Not metering is the run as it was before the
                // meter existed.
                let counted = parent
                    .as_ref()
                    .is_some_and(|node| node.allotment().is_some());
                let node = (!counted).then(|| {
                    let spec = ChildSpec::new(NodeLabel::Run);
                    match parent {
                        Some(parent) => parent.child(spec),
                        None => Guard::root_child(spec),
                    }
                });
                let inside = node.as_ref().map(Guard::enter);
                (node, false, true, inside)
            }
        };
        let id = NEXT_ID.with(|next| {
            let id = next.get();
            next.set(id.wrapping_add(1));
            id
        });
        let _ = RUNS.try_with(|runs| {
            runs.borrow_mut().push(Open {
                id,
                node,
                counting,
                owns_node,
                counts: Counts::default(),
            });
        });
        Self {
            id,
            _inside: inside,
        }
    }

    /// Settle a run under an effort that ended without a verdict: when no
    /// charge latched a stop on its node, latch the one that ended it, so
    /// [`ChcRunWork::stop`] names it. `cancelled` is the run's own token,
    /// which the node does not read (§13: a flag it latched would outlive
    /// `CancellationToken::reset`); otherwise the node reads what it reads at
    /// a tick (`Guard::exhausted`: the cancel chain, B, its backstop deadline,
    /// the process memory budget). A backstop that fired after the run's last
    /// clock stride, or after its last charge, is then published as itself.
    /// Without an effort, or with a stop latched, nothing.
    pub(crate) fn settle(&self, cancelled: bool) {
        let id = self.id;
        let _ = RUNS.try_with(|runs| {
            let Ok(runs) = runs.try_borrow() else {
                return;
            };
            let Some(Open {
                node: Some(node),
                counting: true,
                owns_node: true,
                ..
            }) = runs.iter().rfind(|run| run.id == id)
            else {
                return;
            };
            if node.stopped().is_some() {
                return;
            }
            if cancelled {
                // The node closes right after: raising its own flag reaches
                // nothing below it, and latches `Cancelled`.
                node.cancel();
            }
            let _ = node.exhausted();
        });
    }

    /// Remove this meter's run from the thread's stack.
    fn take(&self) -> Option<Open> {
        let id = self.id;
        RUNS.try_with(|runs| {
            let mut runs = runs.borrow_mut();
            let at = runs.iter().rposition(|run| run.id == id)?;
            Some(runs.remove(at))
        })
        .ok()
        .flatten()
    }

    /// The run's totals: `None` for a run that was not metered (opened with
    /// no effort below a node that counts, or inside a counting run, or its
    /// entry gone).
    pub(crate) fn close(self) -> Option<ChcRunWork> {
        let open = self.take()?;
        let node = open.node.as_ref().filter(|_| open.owns_node)?;
        let counts = &open.counts;
        Some(ChcRunWork {
            ticks: node.ledger_ticks(),
            sat_ticks: counts.sat_ticks.get(),
            smt_entries: counts.smt_entries.get(),
            theory_rounds: counts.theory_rounds.get(),
            pdr_iterations: counts.pdr_iterations.get(),
            obligations: counts.obligations.get(),
            frames: counts.frames.get(),
            lemmas: counts.lemmas.get(),
            ledger: node.ledger(),
            closed_route_checks: counts.closed_route_checks.get(),
            effort: open.counting.then(|| node.allotment()).flatten(),
            stop: open.counting.then(|| node.stopped()).flatten(),
        })
    }
}

impl Drop for RunMeter {
    fn drop(&mut self) {
        // Dropped outside the borrow: it may hold the node's last handle.
        drop(self.take());
    }
}

#[cfg(test)]
#[path = "run_meter/tests.rs"]
mod tests;
