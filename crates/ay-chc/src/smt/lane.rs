// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lane and verification-mode pins for the `HornSmt` session (design §2.11,
//! §7; contract C6; owner WP-4 / D).
//!
//! Two independent mechanisms keep the session off every verdict-bearing
//! query (design §7.1):
//!
//! * **INV-S1, construction-time**: [`SmtLane`] on `SmtContext` — Rung 0's
//!   type (`smt/context.rs`), re-exported here so contract C6 has ONE lane
//!   type. `Verification` is the default of `SmtContext::new()` /
//!   `ChcProblem::make_smt_context()` / `PdrConfig::default()` /
//!   `BmcConfig::default()`; engines opt into `Search` (`PdrSolver::solve()`
//!   pins its own context at entry, portfolio `run_engine`, the adaptive
//!   probes, the Kind/TPA/LAWI/PDKind/IMC/DAR helper contexts). Every
//!   validator constructor inherits `Verification` (locked by
//!   `tests_rung0_bridge_hygiene`).
//! * **INV-S2, call-time**: [`ScopedVerificationMode`] — a thread-scoped
//!   guard, the shape of `ScopedSmtDeadline` (`smt/deadline.rs`), installed
//!   at the entry of every verifier in the §7.2 pin table. While any guard is
//!   alive on the thread the router never routes to a session, whatever the
//!   context's lane: the same `PdrSolver` context serves search AND its own
//!   in-engine `verify_model*` calls (design F14), and Rung 0 moved the Kind
//!   fresh cross-checks and `engine_utils::check_sat_with_timeout` onto the
//!   Search lane, so S1 alone no longer separates them.
//!
//! The router gate (`smt/check_sat/mod.rs`) is
//! `session_mode() > 0 && lane == Search && !verification_mode_active()`.
//!
//! Flags (design §8; all CLI-owned, `MiscCliFlags`, no env fallback):
//! `--chc-session <0|1|2>` (`chc_session`; 0 = off, 1 = session with legacy
//! fall-through on `Unsupported | Poisoned | TheoryIncomplete`, 2 = session
//! only), `--chc-session-strict <l2|full>` (`chc_session_strict`; `full` = any
//! non-Budget Unknown, any audit disagreement and any routing under
//! verification mode PANIC — the harness posture; `l2` = only the lock-L2
//! tripwire panics), `--chc-session-audit <n>` (`chc_session_audit`; every
//! N-th session UNSAT is re-solved on a fresh `Verification` context; a
//! disagreement is counted and the query answers `Unknown`),
//! `--chc-session-stats` (`chc_session_stats`; one `[CHC-SESSION]` line per
//! process at the end of the CLI run; the board's inputs),
//! `--chc-session-dump <dir>` / `--chc-session-dump-max <n>`
//! (`chc_session_dump` / `chc_session_dump_max`; `session/dump.rs`).
//!
//! Process-wide counters ([`SessionTotals`]) are folded by the router after
//! every routed query so they survive engine cancellation and
//! `process::exit`; `constructions_in_verification` is the lock-L2 counter
//! and MUST stay 0.

use std::cell::Cell;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;

pub(crate) use super::context::SmtLane;

pub(crate) mod census;
pub(crate) use census::{CensusFrame, RouteMark, ScopedCensusRole, ScopedEngineLabel, SmtEntry};

thread_local! {
    /// Depth of live [`ScopedVerificationMode`] guards on this thread.
    static VERIFICATION_DEPTH: Cell<u32> = const { Cell::new(0) };
    /// Per-thread override of [`session_mode`] (tests and the differential
    /// harness switch modes inside one process; the env/CLI value is read
    /// once).
    static SESSION_MODE_OVERRIDE: Cell<Option<u8>> = const { Cell::new(None) };
}

/// RAII guard: while alive on this thread, [`verification_mode_active`] is
/// `true` and the router refuses the session on every context (INV-S2).
///
/// Nests (a depth counter); `!Send` so the depth can never be decremented
/// from another thread.
#[must_use = "the verification pin protects only while the guard is alive"]
pub(crate) struct ScopedVerificationMode {
    _not_send: PhantomData<*const ()>,
}

impl ScopedVerificationMode {
    /// Install the pin for the enclosing scope.
    pub(crate) fn install() -> Self {
        VERIFICATION_DEPTH.with(|d| d.set(d.get().saturating_add(1)));
        Self {
            _not_send: PhantomData,
        }
    }
}

impl Drop for ScopedVerificationMode {
    fn drop(&mut self) {
        VERIFICATION_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

/// `true` while any [`ScopedVerificationMode`] guard is alive on this thread.
#[inline]
pub(crate) fn verification_mode_active() -> bool {
    VERIFICATION_DEPTH.with(Cell::get) > 0
}

/// Current guard depth (tests).
#[cfg(test)]
pub(crate) fn verification_depth() -> u32 {
    VERIFICATION_DEPTH.with(Cell::get)
}

/// The session mode: the `--chc-session` CLI flag (`MiscCliFlags::chc_session`),
/// else 0 (off; the default until Rung 4). Read once per process; a
/// thread-local [`ScopedSessionMode`] override wins.
pub(crate) fn session_mode() -> u8 {
    if let Some(m) = SESSION_MODE_OVERRIDE.with(Cell::get) {
        return m;
    }
    static MODE: OnceLock<u8> = OnceLock::new();
    *MODE.get_or_init(|| ay_core::misc_cli_flags().chc_session.unwrap_or(0).min(2))
}

/// Thread-scoped override of [`session_mode`] (restored on drop). Used by the
/// unit tests, the soundness locks and the differential harness.
#[must_use = "the override lasts only while the guard is alive"]
pub(crate) struct ScopedSessionMode {
    prev: Option<u8>,
    _not_send: PhantomData<*const ()>,
}

impl ScopedSessionMode {
    pub(crate) fn set(mode: u8) -> Self {
        let prev = SESSION_MODE_OVERRIDE.with(|c| c.replace(Some(mode.min(2))));
        Self {
            prev,
            _not_send: PhantomData,
        }
    }
}

impl Drop for ScopedSessionMode {
    fn drop(&mut self) {
        let prev = self.prev;
        SESSION_MODE_OVERRIDE.with(|c| c.set(prev));
    }
}

/// `--chc-session-strict <l2|full>`: `full` = harness posture — any poisoned
/// / theory-incomplete answer, any audit disagreement and any session use
/// under verification mode panic; `l2` = only the lock-L2 tripwire panics
/// (what the `group_*` suites run under with the session on, where a
/// theory-incomplete fall-through is a normal event). Read once.
fn strict_level() -> u8 {
    static LEVEL: OnceLock<u8> = OnceLock::new();
    *LEVEL.get_or_init(|| {
        match ay_core::misc_cli_flags()
            .chc_session_strict
            .as_deref()
            .map(str::trim)
        {
            Some("1" | "full" | "on" | "true") => 2,
            Some("l2") => 1,
            _ => 0,
        }
    })
}

/// Full harness posture (`--chc-session-strict full`).
pub(crate) fn session_strict() -> bool {
    strict_level() >= 2
}

/// `--chc-session-audit <n>`: every N-th session UNSAT is re-solved on a
/// fresh `Verification`-lane context (0 / unset = off).
pub(crate) fn session_audit_every() -> u64 {
    ay_core::misc_cli_flags().chc_session_audit.unwrap_or(0)
}

/// `--chc-session-stats`: print the process totals at the end of a CLI run.
pub(crate) fn session_stats_enabled() -> bool {
    ay_core::misc_cli_flags().chc_session_stats
}

/// Lock-free log2 histogram (the atomic twin of `session::LogHistogram`):
/// bucket 0 holds 0, bucket `i >= 1` holds `[2^(i-1), 2^i)`; quantiles are
/// bucket upper bounds.
pub(crate) struct AtomicLogHistogram {
    buckets: [AtomicU64; 65],
    count: AtomicU64,
    sum: AtomicU64,
    max: AtomicU64,
}

impl AtomicLogHistogram {
    const fn new() -> Self {
        Self {
            buckets: [const { AtomicU64::new(0) }; 65],
            count: AtomicU64::new(0),
            sum: AtomicU64::new(0),
            max: AtomicU64::new(0),
        }
    }

    pub(crate) fn record(&self, v: u64) {
        let bucket = if v == 0 {
            0
        } else {
            (u64::BITS - v.leading_zeros()) as usize
        };
        self.buckets[bucket].fetch_add(1, Ordering::Relaxed);
        self.count.fetch_add(1, Ordering::Relaxed);
        self.sum.fetch_add(v, Ordering::Relaxed);
        self.max.fetch_max(v, Ordering::Relaxed);
    }

    pub(crate) fn count(&self) -> u64 {
        self.count.load(Ordering::Relaxed)
    }

    pub(crate) fn sum(&self) -> u64 {
        self.sum.load(Ordering::Relaxed)
    }

    pub(crate) fn max(&self) -> u64 {
        self.max.load(Ordering::Relaxed)
    }

    /// Upper bound of the bucket holding the `q`-quantile sample; 0 when empty.
    pub(crate) fn quantile(&self, q: f64) -> u64 {
        let count = self.count();
        if count == 0 {
            return 0;
        }
        let target = ((q.clamp(0.0, 1.0) * count as f64).ceil() as u64).max(1);
        let mut seen = 0u64;
        for (i, n) in self.buckets.iter().enumerate() {
            seen += n.load(Ordering::Relaxed);
            if seen >= target {
                return match i {
                    0 => 0,
                    64.. => u64::MAX,
                    _ => (1u64 << i) - 1,
                };
            }
        }
        self.max()
    }
}

/// Process-wide session counters (design §10.4 board inputs). Folded by the
/// router after every routed query.
pub(crate) struct SessionTotals {
    /// Queries the gate handed to a session (incl. fall-throughs).
    pub(crate) routed: AtomicU64,
    pub(crate) sat: AtomicU64,
    pub(crate) unsat: AtomicU64,
    /// Session `Sat` demoted by the strict evaluator of the ORIGINAL expr.
    pub(crate) strict_demotions: AtomicU64,
    pub(crate) unknown_budget: AtomicU64,
    pub(crate) unknown_unsupported: AtomicU64,
    pub(crate) unknown_theory_incomplete: AtomicU64,
    pub(crate) unknown_poisoned: AtomicU64,
    /// Mode-1 fall-throughs to the legacy bridge.
    pub(crate) fallthrough: AtomicU64,
    pub(crate) reentries: AtomicU64,
    pub(crate) rebuilds: AtomicU64,
    pub(crate) ext_full_reset_hits: AtomicU64,
    pub(crate) ext_incremental_reset_hits: AtomicU64,
    pub(crate) mints_originals: AtomicU64,
    pub(crate) unit_kills: AtomicU64,
    pub(crate) delta_conjuncts: AtomicU64,
    /// Sessions created by the router.
    pub(crate) sessions_created: AtomicU64,
    /// Lock L2: a session created or queried while `verification_mode_active()`
    /// or on a non-`Search` context. MUST stay 0.
    pub(crate) constructions_in_verification: AtomicU64,
    pub(crate) audits: AtomicU64,
    pub(crate) audit_disagreements: AtomicU64,
    /// Wall time of one routed query (µs), gate entry to exit.
    pub(crate) query_us: AtomicLogHistogram,
    /// `elapsed - budget` (µs) when a budgeted query overran its budget.
    pub(crate) overrun_us: AtomicLogHistogram,
    pub(crate) assumptions_per_query: AtomicLogHistogram,
    pub(crate) decisions_per_query: AtomicLogHistogram,
}

impl SessionTotals {
    const fn new() -> Self {
        Self {
            routed: AtomicU64::new(0),
            sat: AtomicU64::new(0),
            unsat: AtomicU64::new(0),
            strict_demotions: AtomicU64::new(0),
            unknown_budget: AtomicU64::new(0),
            unknown_unsupported: AtomicU64::new(0),
            unknown_theory_incomplete: AtomicU64::new(0),
            unknown_poisoned: AtomicU64::new(0),
            fallthrough: AtomicU64::new(0),
            reentries: AtomicU64::new(0),
            rebuilds: AtomicU64::new(0),
            ext_full_reset_hits: AtomicU64::new(0),
            ext_incremental_reset_hits: AtomicU64::new(0),
            mints_originals: AtomicU64::new(0),
            unit_kills: AtomicU64::new(0),
            delta_conjuncts: AtomicU64::new(0),
            sessions_created: AtomicU64::new(0),
            constructions_in_verification: AtomicU64::new(0),
            audits: AtomicU64::new(0),
            audit_disagreements: AtomicU64::new(0),
            query_us: AtomicLogHistogram::new(),
            overrun_us: AtomicLogHistogram::new(),
            assumptions_per_query: AtomicLogHistogram::new(),
            decisions_per_query: AtomicLogHistogram::new(),
        }
    }

    /// One-line report (the `[CHC-SESSION]` stderr line and the board's row).
    pub(crate) fn report(&self) -> String {
        let g = |a: &AtomicU64| a.load(Ordering::Relaxed);
        let routed = g(&self.routed);
        let pct = |n: u64| {
            if routed == 0 {
                0.0
            } else {
                100.0 * n as f64 / routed as f64
            }
        };
        let ti = g(&self.unknown_theory_incomplete);
        let un = g(&self.unknown_unsupported);
        format!(
            "routed={routed} sat={} unsat={} strict_demotions={} unknown_budget={} \
             unknown_unsupported={un} unknown_theory_incomplete={ti} unknown_poisoned={} \
             ti+unsupported_pct={:.2} fallthrough={} query_us[med/p90/p99/max]={}/{}/{}/{} \
             overrun_us[n/p99/max]={}/{}/{} assumptions_med={} decisions_med={} \
             delta_conjuncts={} reentries={} rebuilds={} unit_kills={} mints_originals={} \
             ext_incremental_reset_hits={} ext_full_reset_hits={} sessions_created={} \
             constructions_in_verification={} audits={} audit_disagreements={}",
            g(&self.sat),
            g(&self.unsat),
            g(&self.strict_demotions),
            g(&self.unknown_budget),
            g(&self.unknown_poisoned),
            pct(ti + un),
            g(&self.fallthrough),
            self.query_us.quantile(0.5),
            self.query_us.quantile(0.9),
            self.query_us.quantile(0.99),
            self.query_us.max(),
            self.overrun_us.count(),
            self.overrun_us.quantile(0.99),
            self.overrun_us.max(),
            self.assumptions_per_query.quantile(0.5),
            self.decisions_per_query.quantile(0.5),
            g(&self.delta_conjuncts),
            g(&self.reentries),
            g(&self.rebuilds),
            g(&self.unit_kills),
            g(&self.mints_originals),
            g(&self.ext_incremental_reset_hits),
            g(&self.ext_full_reset_hits),
            g(&self.sessions_created),
            g(&self.constructions_in_verification),
            g(&self.audits),
            g(&self.audit_disagreements),
        )
    }
}

static TOTALS: SessionTotals = SessionTotals::new();

/// The process-wide session counters.
pub(crate) fn totals() -> &'static SessionTotals {
    &TOTALS
}

/// Lock L2 (design §7.1): record a session created or queried where it must
/// never be — under a live [`ScopedVerificationMode`] or on a non-`Search`
/// context. The router gate makes this unreachable; this is the tripwire
/// behind it (risk R8). Panics under `--chc-session-strict` and in debug
/// builds.
pub(crate) fn note_construction_in_verification(where_: &'static str) {
    TOTALS
        .constructions_in_verification
        .fetch_add(1, Ordering::Relaxed);
    debug_assert!(
        false,
        "HornSmt session used under verification mode / off the Search lane at {where_}"
    );
    if strict_level() >= 1 {
        panic!("chc-session-strict: HornSmt session used under verification mode at {where_}");
    }
    tracing::error!("HornSmt session used under verification mode at {where_}");
}

/// Lock L2 counter (process-wide).
pub(crate) fn constructions_in_verification() -> u64 {
    TOTALS.constructions_in_verification.load(Ordering::Relaxed)
}

/// The session totals as one line, `None` when no query was ever routed
/// (so a CLI run with the session off prints nothing).
pub(crate) fn totals_report() -> Option<String> {
    if TOTALS.routed.load(Ordering::Relaxed) == 0
        && TOTALS.constructions_in_verification.load(Ordering::Relaxed) == 0
    {
        return None;
    }
    Some(format!(
        "[CHC-SESSION] mode={} {}",
        session_mode(),
        TOTALS.report()
    ))
}

/// Test-only stub of the session's answer (lock L1, design §7.1 / audit pin
/// #4): while a [`stub::ScopedWrongUnsat`] guard is alive on this thread, the
/// router gate answers EVERY query it would have handed to the session with
/// `Unsat` — the stub wrong-UNSAT backend. A verdict-bearing consumer that
/// ever saw one of these answers would print a wrong `sat`; the locks assert
/// none does.
#[cfg(test)]
pub(crate) mod stub {
    use std::cell::Cell;
    use std::marker::PhantomData;

    thread_local! {
        static WRONG_UNSAT: Cell<bool> = const { Cell::new(false) };
        static HITS: Cell<u64> = const { Cell::new(0) };
    }

    #[must_use = "the stub answers only while the guard is alive"]
    pub(crate) struct ScopedWrongUnsat {
        prev: bool,
        _not_send: PhantomData<*const ()>,
    }

    impl ScopedWrongUnsat {
        pub(crate) fn install() -> Self {
            let prev = WRONG_UNSAT.with(|c| c.replace(true));
            Self {
                prev,
                _not_send: PhantomData,
            }
        }
    }

    impl Drop for ScopedWrongUnsat {
        fn drop(&mut self) {
            let prev = self.prev;
            WRONG_UNSAT.with(|c| c.set(prev));
        }
    }

    /// `true` when the stub must answer (and counts the hit).
    pub(crate) fn wrong_unsat_active() -> bool {
        let on = WRONG_UNSAT.with(Cell::get);
        if on {
            HITS.with(|h| h.set(h.get() + 1));
        }
        on
    }

    /// Stubbed answers on this thread so far.
    pub(crate) fn hits() -> u64 {
        HITS.with(Cell::get)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verification_guard_nests_and_restores() {
        assert!(!verification_mode_active());
        {
            let _a = ScopedVerificationMode::install();
            assert!(verification_mode_active());
            assert_eq!(verification_depth(), 1);
            {
                let _b = ScopedVerificationMode::install();
                assert_eq!(verification_depth(), 2);
            }
            assert!(verification_mode_active());
            assert_eq!(verification_depth(), 1);
        }
        assert!(!verification_mode_active());
    }

    #[test]
    fn verification_guard_is_thread_local() {
        let _a = ScopedVerificationMode::install();
        assert!(verification_mode_active());
        let other = std::thread::spawn(verification_mode_active).join().unwrap();
        assert!(!other, "a guard on one thread must not pin another");
    }

    #[test]
    fn session_mode_override_wins_and_restores() {
        let base = session_mode();
        {
            let _m = ScopedSessionMode::set(2);
            assert_eq!(session_mode(), 2);
            {
                let _n = ScopedSessionMode::set(1);
                assert_eq!(session_mode(), 1);
            }
            assert_eq!(session_mode(), 2);
        }
        assert_eq!(session_mode(), base);
        let _m = ScopedSessionMode::set(7);
        assert_eq!(session_mode(), 2, "modes clamp to 2");
    }

    #[test]
    fn atomic_histogram_quantiles_match_the_session_histogram() {
        let h = AtomicLogHistogram::new();
        let mut g = crate::smt::session::LogHistogram::default();
        for v in [0u64, 1, 3, 4, 7, 8, 100, 1000, 65_536] {
            h.record(v);
            g.record(v);
        }
        for q in [0.0, 0.5, 0.9, 0.99, 1.0] {
            assert_eq!(h.quantile(q), g.quantile(q), "q={q}");
        }
        assert_eq!(h.count(), 9);
        assert_eq!(h.max(), 65_536);
        assert_eq!(h.sum(), g.sum());
    }

    #[test]
    fn totals_report_names_every_board_counter() {
        let r = TOTALS.report();
        for key in [
            "routed=",
            "unknown_theory_incomplete=",
            "ti+unsupported_pct=",
            "query_us[med/p90/p99/max]=",
            "overrun_us[n/p99/max]=",
            "ext_full_reset_hits=",
            "reentries=",
            "constructions_in_verification=",
            "audit_disagreements=",
        ] {
            assert!(r.contains(key), "missing {key} in {r}");
        }
    }
}
