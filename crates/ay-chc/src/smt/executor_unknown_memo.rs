// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Timeout-class executor-unknown memo (inc-13 per-check multiplier).
//!
//! PDR blocking loops and PDKIND induction loops re-issue byte-identical
//! SMT queries after the executor already burned a full per-check budget on
//! them and returned Unknown. Measured on the lustre sat-gap class
//! (MOESI_2_e8_101 @60s): 17 of 65 executor checks were timeout-class
//! unknowns at 1.5-3.7s each, and 11 of those 17 were exact repeats of just
//! 4 distinct query texts — pure re-burn. This memo short-circuits a repeat
//! to Unknown unless the caller brings a strictly larger budget.
//!
//! Soundness: the memo only ever converts "re-run the executor and time out
//! again" into an immediate `Unknown`. `Unknown` is always a sound answer,
//! and absolutely no solver state (assertions, models, lemmas) crosses
//! queries — the skip decision is the only shared artifact. A retry with a
//! strictly larger budget (>= 2x headroom, see `should_skip`) still runs, so
//! budget escalation at deeper PDR levels is preserved.

/// One memo entry: fingerprint of the serialized query text plus the largest
/// budget (in milliseconds) the executor exhausted on it.
#[derive(Debug, Clone, Copy)]
struct MemoEntry {
    fingerprint: u64,
    timed_out_budget_ms: u64,
}

/// Bounded FIFO memo of timeout-class executor unknowns.
#[derive(Debug, Default)]
pub(crate) struct ExecutorUnknownMemo {
    entries: Vec<MemoEntry>,
    /// FIFO replacement cursor.
    next_slot: usize,
    /// Telemetry: how many executor runs were skipped.
    skips: u64,
}

/// Maximum distinct timeout-class queries remembered per `SmtContext`.
///
/// PDR re-issues cluster on a handful of pob/induction shapes; 64 distinct
/// timed-out texts is far beyond the observed 4-7 per instance.
const MEMO_CAPACITY: usize = 64;

/// Minimum budget for a timeout to be memoised. Sub-100ms budgets are
/// deadline-fragment noise (clamped remainders), not real solve attempts;
/// memoising them could mask a later honest attempt at a similar tiny budget.
const MIN_MEMO_BUDGET_MS: u64 = 100;

/// Fraction of the budget the executor must have consumed for the unknown to
/// count as a timeout (rather than a fast structural "shape unsupported"
/// unknown, which must never be memoised — fast unknowns are cheap to re-ask
/// and the internal loop may still answer differently).
const TIMEOUT_ELAPSED_FRACTION: f64 = 0.85;

/// Budget multiplier a retry must bring to bypass the memo. A strictly
/// larger budget means the caller escalated (deeper level, larger window);
/// the 1.5x headroom keeps load-jitter from defeating the memo.
const ESCALATION_FACTOR: f64 = 1.5;

impl ExecutorUnknownMemo {
    /// Should this query (by fingerprint) skip the executor at this budget?
    pub(crate) fn should_skip(&mut self, fingerprint: u64, budget_ms: u64) -> bool {
        let skip = self.entries.iter().any(|e| {
            e.fingerprint == fingerprint
                && (budget_ms as f64) < (e.timed_out_budget_ms as f64) * ESCALATION_FACTOR
        });
        if skip {
            self.skips += 1;
        }
        skip
    }

    /// Record a timeout-class unknown: the executor ran `elapsed_ms` of a
    /// `budget_ms` budget and returned Unknown. Only true timeouts at real
    /// budgets are recorded; fast structural unknowns are not.
    pub(crate) fn record_unknown(&mut self, fingerprint: u64, budget_ms: u64, elapsed_ms: u64) {
        if budget_ms < MIN_MEMO_BUDGET_MS {
            return;
        }
        if (elapsed_ms as f64) < (budget_ms as f64) * TIMEOUT_ELAPSED_FRACTION {
            return;
        }
        if let Some(e) = self
            .entries
            .iter_mut()
            .find(|e| e.fingerprint == fingerprint)
        {
            e.timed_out_budget_ms = e.timed_out_budget_ms.max(budget_ms);
            return;
        }
        let entry = MemoEntry {
            fingerprint,
            timed_out_budget_ms: budget_ms,
        };
        if self.entries.len() < MEMO_CAPACITY {
            self.entries.push(entry);
        } else {
            self.entries[self.next_slot] = entry;
            self.next_slot = (self.next_slot + 1) % MEMO_CAPACITY;
        }
    }

    /// Telemetry: number of executor runs skipped by the memo.
    #[cfg(test)]
    pub(crate) fn skip_count(&self) -> u64 {
        self.skips
    }
}

/// Fingerprint of a serialized SMT query, excluding the volatile
/// `(set-option :timeout ...)` line so the same logical query at different
/// budgets maps to one entry.
pub(crate) fn fingerprint_query_text(smt_text: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    for line in smt_text.lines() {
        if line.starts_with("(set-option :timeout") {
            continue;
        }
        line.hash(&mut h);
    }
    h.finish()
}

/// Kill switch: `AY_EXEC_UNKNOWN_MEMO=0` disables the memo.
pub(crate) fn executor_unknown_memo_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("AY_EXEC_UNKNOWN_MEMO").map_or(true, |v| v != "0"))
}

// The memo is thread-local rather than `SmtContext`-owned: PDKIND and several
// engine helpers create a FRESH `SmtContext` per query
// (`engine_utils::check_sat_with_timeout`), so a context-owned memo would
// never see the repeats. Engine threads are per-solve, so thread-locality
// scopes the memo to one engine's query stream — no cross-engine coupling.
thread_local! {
    static THREAD_MEMO: std::cell::RefCell<ExecutorUnknownMemo> =
        std::cell::RefCell::new(ExecutorUnknownMemo::default());
}

/// Thread-local skip check; see `ExecutorUnknownMemo::should_skip`.
pub(crate) fn should_skip_query(fingerprint: u64, budget_ms: u64) -> bool {
    THREAD_MEMO.with(|m| m.borrow_mut().should_skip(fingerprint, budget_ms))
}

/// Thread-local timeout-class unknown recording; see
/// `ExecutorUnknownMemo::record_unknown`.
pub(crate) fn record_unknown_query(fingerprint: u64, budget_ms: u64, elapsed_ms: u64) {
    THREAD_MEMO.with(|m| {
        m.borrow_mut()
            .record_unknown(fingerprint, budget_ms, elapsed_ms)
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skip_requires_prior_timeout_record() {
        let mut memo = ExecutorUnknownMemo::default();
        assert!(!memo.should_skip(42, 1000), "fresh query must run");
        memo.record_unknown(42, 1000, 990);
        assert!(
            memo.should_skip(42, 1000),
            "exact repeat at same budget skips"
        );
        assert!(
            memo.should_skip(42, 1400),
            "1.4x budget is within escalation headroom — still skip"
        );
        assert!(
            !memo.should_skip(42, 1501),
            "a strictly escalated budget (>=1.5x) must run"
        );
    }

    #[test]
    fn fast_structural_unknown_is_never_memoised() {
        let mut memo = ExecutorUnknownMemo::default();
        // Executor answered Unknown in 5ms of a 1000ms budget: shape
        // unsupported, not a timeout. Must not be memoised.
        memo.record_unknown(7, 1000, 5);
        assert!(!memo.should_skip(7, 1000));
    }

    #[test]
    fn tiny_budgets_are_never_memoised() {
        let mut memo = ExecutorUnknownMemo::default();
        memo.record_unknown(7, 50, 50);
        assert!(!memo.should_skip(7, 50));
    }

    #[test]
    fn distinct_fingerprints_do_not_collide() {
        let mut memo = ExecutorUnknownMemo::default();
        memo.record_unknown(1, 1000, 1000);
        assert!(!memo.should_skip(2, 1000), "different query must run");
    }

    #[test]
    fn capacity_is_bounded_fifo() {
        let mut memo = ExecutorUnknownMemo::default();
        for fp in 0..(MEMO_CAPACITY as u64 + 8) {
            memo.record_unknown(fp, 1000, 1000);
        }
        assert!(memo.entries.len() == MEMO_CAPACITY);
        // The first 8 entries were evicted FIFO.
        assert!(!memo.should_skip(0, 1000));
        assert!(memo.should_skip(MEMO_CAPACITY as u64 + 7, 1000));
    }

    #[test]
    fn escalated_budget_updates_entry_to_the_max() {
        let mut memo = ExecutorUnknownMemo::default();
        memo.record_unknown(9, 1000, 1000);
        memo.record_unknown(9, 4000, 4000);
        assert!(memo.should_skip(9, 4000));
        assert!(!memo.should_skip(9, 6001), ">=1.5x of max recorded runs");
        assert_eq!(memo.skip_count(), 1);
    }

    #[test]
    fn fingerprint_ignores_timeout_line_only() {
        let a = "(set-logic QF_LIA)\n(set-option :timeout 1500)\n(assert (> x 0))\n";
        let b = "(set-logic QF_LIA)\n(set-option :timeout 900)\n(assert (> x 0))\n";
        let c = "(set-logic QF_LIA)\n(set-option :timeout 1500)\n(assert (> x 1))\n";
        assert_eq!(fingerprint_query_text(a), fingerprint_query_text(b));
        assert_ne!(fingerprint_query_text(a), fingerprint_query_text(c));
    }
}
