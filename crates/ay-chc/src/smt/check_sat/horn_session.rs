// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `HornSmt` router gate body (design §2.11; #horn-smt-session Rung 1).
//!
//! `SmtContext::check_sat` calls [`SmtContext::route_to_session`] AFTER its
//! four fail-closed guards (no-progress breaker, lane deadline, term memory,
//! bit-blast budget) and BEFORE the executor-first branch, under the gate
//! `lane::session_mode() > 0 && self.lane == SmtLane::Search &&
//! !lane::verification_mode_active()`. The body re-checks that condition as
//! the lock-L2 tripwire, creates the session lazily, runs WP-3's
//! `try_session`, and then does the WP-4 bookkeeping: the process-wide board
//! counters (`lane::totals`), the `--chc-session-dump` recorder, the
//! `--chc-session-audit <n>` cross-check of session UNSATs on a fresh
//! `Verification`-lane context, and the `--chc-session-strict` panics.
//!
//! Soundness posture: a `Sat` from the session has already passed the strict
//! evaluation of the ORIGINAL expression inside `try_session` (INV-S3); an
//! `Unsat` is search guidance whose only consumers are `Search`-lane engines
//! whose verdicts are re-derived by pinned verifiers (INV-S1/S2). The audit
//! turns a disagreeing UNSAT into `Unknown` (fail-closed) and counts it.

use std::sync::atomic::Ordering;
use std::time::Duration;

use ay_core::time::Instant;

use crate::smt::context::SmtContext;
use crate::smt::lane;
use crate::smt::session::dump::{DumpRecord, SessionDump};
use crate::smt::session::{shim, SessionStats};
use crate::smt::types::SmtResult;
use crate::ChcExpr;

/// The per-query deltas the dump and the totals need.
#[derive(Clone, Copy, Default)]
struct Snap {
    sat: u64,
    unknown_budget: u64,
    unknown_unsupported: u64,
    unknown_theory_incomplete: u64,
    unknown_poisoned: u64,
    delta_conjuncts: u64,
    assumptions_sum: u64,
    decisions_sum: u64,
    reentries: u64,
    rebuilds: u64,
    ext_full_reset_hits: u64,
    ext_incremental_reset_hits: u64,
    mints_originals: u64,
    unit_kills: u64,
}

impl Snap {
    fn of(s: &SessionStats) -> Self {
        Self {
            sat: s.sat,
            unknown_budget: s.unknown_budget,
            unknown_unsupported: s.unknown_unsupported,
            unknown_theory_incomplete: s.unknown_theory_incomplete,
            unknown_poisoned: s.unknown_poisoned,
            delta_conjuncts: s.delta_conjuncts,
            assumptions_sum: s.assumptions_per_query.sum(),
            decisions_sum: s.decisions_per_query.sum(),
            reentries: s.reentries,
            rebuilds: s.rebuilds,
            ext_full_reset_hits: s.ext_full_reset_hits,
            ext_incremental_reset_hits: s.ext_incremental_reset_hits,
            mints_originals: s.mints_originals,
            unit_kills: s.unit_kills,
        }
    }
}

/// The numeric part of `ThreadId`'s Debug form (`ThreadId(7)` -> 7); there is
/// no stable accessor.
fn thread_no() -> u64 {
    let s = format!("{:?}", std::thread::current().id());
    s.trim_start_matches(|c: char| !c.is_ascii_digit())
        .trim_end_matches(|c: char| !c.is_ascii_digit())
        .parse()
        .unwrap_or(0)
}

/// Default audit budget when the routed query carried none.
const AUDIT_DEFAULT_BUDGET: Duration = Duration::from_secs(2);

impl SmtContext {
    /// The router gate (design §2.11): session enabled, a `Search`-lane
    /// context (INV-S1) and no live `ScopedVerificationMode` on this thread
    /// (INV-S2).
    pub(crate) fn session_gate_open(&self) -> bool {
        lane::session_mode() > 0 && self.session_designated() && !lane::verification_mode_active()
    }

    /// Rung-4 wiring for the SMT entry points that do not run through
    /// [`SmtContext::check_sat`] (`IncrementalQueryContext`,
    /// `PersistentExecutorSmtContext`, ...): the same gate and the same
    /// router body, with `budget` as the per-check budget of this one query.
    /// `None` = the session did not answer (gate closed, a fail-closed
    /// preflight tripped, or a mode-1 fall-through) — the caller's own path
    /// runs unchanged. A `Some` answer carries exactly the guarantees of a
    /// routed `check_sat` answer (INV-S3 for `Sat`; `Unsat` is search
    /// guidance for `Search`-lane consumers only).
    pub(crate) fn try_session_route(
        &mut self,
        expr: &ChcExpr,
        budget: Option<Duration>,
    ) -> Option<SmtResult> {
        if !self.session_gate_open() {
            return None;
        }
        // `check_sat`'s fail-closed preflight: the caller's own path answers
        // these (its guards return `Unknown`).
        if crate::smt::no_progress_breaker_tripped()
            || self.deadlines_expired()
            || self.exact_term_memory_exceeded()
        {
            return None;
        }
        let prev = self.check_timeout.get();
        if budget.is_some() {
            self.check_timeout.set(budget);
        }
        let routed = self.route_to_session(expr);
        self.check_timeout.set(prev);
        routed
    }

    /// Rung 4: `check_sat_with_assumption_conjuncts` for SEARCH consumers that
    /// need only a CONJUNCT-level core over `assumptions` (PDR's IUC
    /// generalization, PDKind's explanation) — never for the Farkas /
    /// interpolation consumers (the session core carries no Farkas; Rung 3).
    ///
    /// Under the gate, `background ∧ assumptions` goes through the router like
    /// a `check_sat` query. A session `Unsat` core names session conjuncts;
    /// assumption `i` is reported needed iff any conjunct of it is in that core
    /// (or it is trivially false), so the reported core is a superset of a
    /// sufficient one and the consumer's shrink stays justified. `Sat` is the
    /// router's strictly verified model. Anything the session does not decide
    /// runs the legacy method unchanged.
    pub(crate) fn check_sat_with_assumption_conjuncts_search(
        &mut self,
        background: &[ChcExpr],
        assumptions: &[ChcExpr],
    ) -> SmtResult {
        if crate::run_meter::charge(crate::run_meter::Step::SmtEntry).is_err() {
            return SmtResult::Unknown;
        }
        // Census (`--chc-session-coverage`): nothing is built when it is off.
        let _census = lane::census::coverage_enabled().then(|| {
            let exprs: Vec<&ChcExpr> = background.iter().chain(assumptions).collect();
            lane::CensusFrame::enter(
                lane::SmtEntry::AssumptionConjuncts,
                Some(self.census_lane()),
                &exprs,
            )
        });
        if self.session_gate_open() {
            let all = ChcExpr::and_all(background.iter().chain(assumptions).cloned());
            match self.try_session_route(&all, None) {
                Some(SmtResult::Sat(model)) => return SmtResult::Sat(model),
                Some(SmtResult::UnsatWithCore(core)) => {
                    return SmtResult::UnsatWithCore(crate::smt::types::UnsatCore {
                        conjuncts: needed_assumptions(assumptions, Some(&core.conjuncts)),
                        ..Default::default()
                    });
                }
                Some(SmtResult::Unsat | SmtResult::UnsatWithFarkas(_)) => {
                    return SmtResult::UnsatWithCore(crate::smt::types::UnsatCore {
                        conjuncts: needed_assumptions(assumptions, None),
                        ..Default::default()
                    });
                }
                Some(SmtResult::Unknown) | None => {}
            }
        }
        self.check_sat_with_assumption_conjuncts(background, assumptions)
    }

    /// Route `expr` to this context's `HornSmt` session (created lazily).
    /// `None` = not answered here, run the legacy bridge (mode-1 fall-through
    /// on `Unsupported | Poisoned | TheoryIncomplete`).
    pub(super) fn route_to_session(&mut self, expr: &ChcExpr) -> Option<SmtResult> {
        let mode = lane::session_mode();
        if mode == 0 {
            return None;
        }
        // Lock L2 / risk R8 tripwire: the gate's own condition makes this
        // unreachable; a future caller that skips the gate is counted and
        // refused.
        if !self.session_designated() || lane::verification_mode_active() {
            lane::note_construction_in_verification("SmtContext::route_to_session");
            return None;
        }
        // Lock L1: the stub wrong-UNSAT backend (tests only).
        #[cfg(test)]
        if lane::stub::wrong_unsat_active() {
            return Some(SmtResult::Unsat);
        }
        let totals = lane::totals();
        let t0 = Instant::now();
        let budget = shim::session_budget(self);
        let mut session = match self.session.take() {
            Some(s) => s,
            None => {
                totals.sessions_created.fetch_add(1, Ordering::Relaxed);
                shim::new_session_for(self)
            }
        };
        let before = Snap::of(session.stats());
        let routed = shim::try_session(&mut session, self, expr, mode);
        let after = Snap::of(session.stats());
        let elapsed = t0.elapsed();
        self.session = Some(session);

        // --- classify -------------------------------------------------------
        let (lane_result, unknown_reason): (&str, &str) = match &routed {
            Some(SmtResult::Sat(_)) => ("sat", "-"),
            Some(
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_),
            ) => ("unsat", "-"),
            Some(_) => ("unknown", unknown_class(&before, &after)),
            None => ("fallthrough", unknown_class(&before, &after)),
        };
        let strict_demotion = after.sat > before.sat && lane_result == "unknown";
        lane::census::note_route(match lane_result {
            "sat" | "unsat" => lane::RouteMark::Decided,
            "unknown" => lane::RouteMark::Unknown,
            _ => lane::RouteMark::Fallthrough,
        });

        // --- process-wide totals --------------------------------------------
        totals.routed.fetch_add(1, Ordering::Relaxed);
        match lane_result {
            "sat" => {
                totals.sat.fetch_add(1, Ordering::Relaxed);
            }
            "unsat" => {
                totals.unsat.fetch_add(1, Ordering::Relaxed);
            }
            "fallthrough" => {
                totals.fallthrough.fetch_add(1, Ordering::Relaxed);
            }
            _ => {}
        }
        if strict_demotion {
            totals.strict_demotions.fetch_add(1, Ordering::Relaxed);
        }
        let add = |a: &std::sync::atomic::AtomicU64, d: u64| {
            if d > 0 {
                a.fetch_add(d, Ordering::Relaxed);
            }
        };
        add(
            &totals.unknown_budget,
            after.unknown_budget - before.unknown_budget,
        );
        add(
            &totals.unknown_unsupported,
            after.unknown_unsupported - before.unknown_unsupported,
        );
        add(
            &totals.unknown_theory_incomplete,
            after.unknown_theory_incomplete - before.unknown_theory_incomplete,
        );
        add(
            &totals.unknown_poisoned,
            after.unknown_poisoned - before.unknown_poisoned,
        );
        add(
            &totals.delta_conjuncts,
            after.delta_conjuncts - before.delta_conjuncts,
        );
        add(&totals.reentries, after.reentries - before.reentries);
        add(&totals.rebuilds, after.rebuilds - before.rebuilds);
        add(
            &totals.mints_originals,
            after.mints_originals - before.mints_originals,
        );
        add(&totals.unit_kills, after.unit_kills - before.unit_kills);
        add(
            &totals.ext_full_reset_hits,
            after
                .ext_full_reset_hits
                .saturating_sub(before.ext_full_reset_hits),
        );
        add(
            &totals.ext_incremental_reset_hits,
            after
                .ext_incremental_reset_hits
                .saturating_sub(before.ext_incremental_reset_hits),
        );
        let n_assumptions = after.assumptions_sum - before.assumptions_sum;
        let decisions = after.decisions_sum - before.decisions_sum;
        let elapsed_us = u64::try_from(elapsed.as_micros()).unwrap_or(u64::MAX);
        totals.query_us.record(elapsed_us);
        if lane_result != "fallthrough" || after.unknown_unsupported == before.unknown_unsupported {
            totals.assumptions_per_query.record(n_assumptions);
            totals.decisions_per_query.record(decisions);
        }
        if let Some(b) = budget {
            if elapsed > b {
                let over = elapsed
                    .checked_sub(b)
                    .expect("elapsed time was checked above the budget");
                totals
                    .overrun_us
                    .record(u64::try_from(over.as_micros()).unwrap_or(u64::MAX));
            }
        }

        // --- dump -----------------------------------------------------------
        if let Some(dump) = SessionDump::global() {
            if let Ok(mut d) = dump.lock() {
                d.record(&DumpRecord {
                    thread: thread_no(),
                    expr,
                    lane_result,
                    elapsed,
                    n_conj: expr.conjuncts().len(),
                    n_delta: after.delta_conjuncts - before.delta_conjuncts,
                    n_assumptions,
                    decisions,
                    unknown_reason,
                });
            }
        }

        // --- strict posture ---------------------------------------------------
        assert!(
            !(lane::session_strict() && matches!(unknown_reason, "poisoned" | "theory_incomplete")),
            "chc-session-strict: session answered {unknown_reason} ({lane_result}) for {}",
            crate::smt::session::dump::script_for(expr, false)
        );

        // --- audit of session UNSATs on a fresh Verification context ---------
        if lane_result == "unsat" {
            let every = lane::session_audit_every();
            if every > 0 && totals.unsat.load(Ordering::Relaxed).is_multiple_of(every) {
                totals.audits.fetch_add(1, Ordering::Relaxed);
                let mut fresh = SmtContext::new();
                let check =
                    fresh.check_sat_with_timeout(expr, budget.unwrap_or(AUDIT_DEFAULT_BUDGET));
                if matches!(check, SmtResult::Sat(_)) {
                    totals.audit_disagreements.fetch_add(1, Ordering::Relaxed);
                    let msg = format!(
                        "HornSmt session answered UNSAT where the legacy bridge answers SAT:\n{}",
                        crate::smt::session::dump::script_for(expr, false)
                    );
                    assert!(!lane::session_strict(), "chc-session-strict: {msg}");
                    tracing::error!("{msg}");
                    // Fail closed: neither side is trusted on a disagreement.
                    return Some(SmtResult::Unknown);
                }
            }
        }

        if matches!(lane_result, "sat" | "unsat") {
            crate::smt::note_solve_progress();
        }
        routed
    }
}

/// Which Unknown class a query landed in, from the stats delta.
fn unknown_class(before: &Snap, after: &Snap) -> &'static str {
    if after.unknown_poisoned > before.unknown_poisoned {
        "poisoned"
    } else if after.unknown_theory_incomplete > before.unknown_theory_incomplete {
        "theory_incomplete"
    } else if after.unknown_unsupported > before.unknown_unsupported {
        "unsupported"
    } else if after.unknown_budget > before.unknown_budget {
        "budget"
    } else if after.sat > before.sat {
        // A session `Sat` demoted by the strict evaluator of the original expr.
        "strict_demotion"
    } else {
        "-"
    }
}

/// The assumptions a session core justifies (see
/// `check_sat_with_assumption_conjuncts_search`): every assumption with a
/// conjunct in `core`, or trivially false; `None` (no core) = all of them.
fn needed_assumptions(assumptions: &[ChcExpr], core: Option<&[ChcExpr]>) -> Vec<ChcExpr> {
    let Some(core) = core else {
        return assumptions.to_vec();
    };
    assumptions
        .iter()
        .filter(
            |a| match crate::smt::session::convert_memo::split_conjuncts(a) {
                Err(_) => true,
                Ok(parts) => parts.iter().any(|p| core.iter().any(|c| c == &**p)),
            },
        )
        .cloned()
        .collect()
}
