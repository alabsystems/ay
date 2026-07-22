// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Thread-local theory solver observability counters (#8165).
//!
//! These counters are incremented by the Nelson-Oppen fixpoint loops and
//! other theory solver code paths, then read and reset by the DPLL(T)
//! stats collection pipeline.
//!
//! Thread-local access is ~1ns per call with no atomic overhead, which is
//! acceptable since theory solving is single-threaded.

use std::cell::Cell;

thread_local! {
    /// Total N-O fixpoint loop iterations across all check() calls.
    static NO_ROUNDS: Cell<u64> = const { Cell::new(0) };
    /// Number of times a theory check returned Unknown.
    static UNKNOWN_RETURNS: Cell<u64> = const { Cell::new(0) };
    /// Number of disequality propagations from EUF to arithmetic (#8163).
    static DISEQ_PROPAGATIONS: Cell<u64> = const { Cell::new(0) };
    /// Theory conflicts attributed to LIA.
    static CONFLICTS_LIA: Cell<u64> = const { Cell::new(0) };
    /// Theory conflicts attributed to LRA.
    static CONFLICTS_LRA: Cell<u64> = const { Cell::new(0) };
    /// Theory conflicts attributed to EUF.
    static CONFLICTS_EUF: Cell<u64> = const { Cell::new(0) };
    /// Theory conflicts attributed to Arrays.
    static CONFLICTS_ARRAYS: Cell<u64> = const { Cell::new(0) };
    /// Per-theory check() call counts.
    static CHECKS_LIA: Cell<u64> = const { Cell::new(0) };
    static CHECKS_LRA: Cell<u64> = const { Cell::new(0) };
    static CHECKS_EUF: Cell<u64> = const { Cell::new(0) };
    static CHECKS_ARRAYS: Cell<u64> = const { Cell::new(0) };
    /// Per-theory propagation counts (equalities forwarded from each theory).
    static PROPS_LIA: Cell<u64> = const { Cell::new(0) };
    static PROPS_LRA: Cell<u64> = const { Cell::new(0) };
    static PROPS_EUF: Cell<u64> = const { Cell::new(0) };
    /// Partial clauses: theory conflict/propagation terms that failed to map to SAT literals.
    static PARTIAL_CLAUSES: Cell<u64> = const { Cell::new(0) };
    /// Cross-theory replay `covered_by` reachability scans (#frame-u64-perf).
    /// Confirms the replay-canonicalization fast paths actually cut the
    /// per-round O(n^2) scan volume on grinding AUFLIA split loops.
    static REPLAY_COVERED_BY_CALLS: Cell<u64> = const { Cell::new(0) };
}

/// Increment the N-O round counter by the given amount.
#[inline]
pub(crate) fn inc_no_rounds(n: u64) {
    NO_ROUNDS.with(|c| c.set(c.get() + n));
}

/// Increment the Unknown return counter.
#[inline]
pub(crate) fn inc_unknown_returns() {
    UNKNOWN_RETURNS.with(|c| c.set(c.get() + 1));
}

/// Increment the disequality propagation counter.
#[inline]
pub(crate) fn inc_diseq_propagations(n: u64) {
    DISEQ_PROPAGATIONS.with(|c| c.set(c.get() + n));
}

/// Increment the LIA conflict counter.
#[inline]
pub(crate) fn inc_conflict_lia() {
    CONFLICTS_LIA.with(|c| c.set(c.get() + 1));
}

/// Increment the LRA conflict counter.
#[inline]
pub(crate) fn inc_conflict_lra() {
    CONFLICTS_LRA.with(|c| c.set(c.get() + 1));
}

/// Increment the EUF conflict counter.
#[inline]
pub(crate) fn inc_conflict_euf() {
    CONFLICTS_EUF.with(|c| c.set(c.get() + 1));
}

/// Increment the Arrays conflict counter.
#[inline]
pub(crate) fn inc_conflict_arrays() {
    CONFLICTS_ARRAYS.with(|c| c.set(c.get() + 1));
}

/// Increment per-theory check() call counters.
#[inline]
pub(crate) fn inc_check_lia() {
    CHECKS_LIA.with(|c| c.set(c.get() + 1));
}

#[inline]
pub(crate) fn inc_check_lra() {
    CHECKS_LRA.with(|c| c.set(c.get() + 1));
}

#[inline]
pub(crate) fn inc_check_euf() {
    CHECKS_EUF.with(|c| c.set(c.get() + 1));
}

#[inline]
pub(crate) fn inc_check_arrays() {
    CHECKS_ARRAYS.with(|c| c.set(c.get() + 1));
}

/// Increment per-theory propagation counters.
#[inline]
pub(crate) fn inc_props_lia(n: u64) {
    PROPS_LIA.with(|c| c.set(c.get() + n));
}

#[inline]
pub(crate) fn inc_props_lra(n: u64) {
    PROPS_LRA.with(|c| c.set(c.get() + n));
}

#[inline]
pub(crate) fn inc_props_euf(n: u64) {
    PROPS_EUF.with(|c| c.set(c.get() + n));
}

/// Increment the partial clause counter.
#[inline]
pub(crate) fn inc_partial_clauses() {
    PARTIAL_CLAUSES.with(|c| c.set(c.get() + 1));
}

/// Increment the cross-theory replay covered_by scan counter.
#[inline]
pub(crate) fn inc_replay_covered_by_calls() {
    REPLAY_COVERED_BY_CALLS.with(|c| c.set(c.get() + 1));
}

/// Snapshot of all theory observability counters.
#[derive(Debug, Clone, Default)]
pub(crate) struct TheoryObservabilityStats {
    pub(crate) no_rounds: u64,
    pub(crate) unknown_returns: u64,
    pub(crate) diseq_propagations: u64,
    pub(crate) conflicts_lia: u64,
    pub(crate) conflicts_lra: u64,
    pub(crate) conflicts_euf: u64,
    pub(crate) conflicts_arrays: u64,
    pub(crate) checks_lia: u64,
    pub(crate) checks_lra: u64,
    pub(crate) checks_euf: u64,
    pub(crate) checks_arrays: u64,
    pub(crate) props_lia: u64,
    pub(crate) props_lra: u64,
    pub(crate) props_euf: u64,
    pub(crate) partial_clauses: u64,
    pub(crate) replay_covered_by_calls: u64,
}

/// Read all counters and reset them to zero.
pub(crate) fn drain_stats() -> TheoryObservabilityStats {
    TheoryObservabilityStats {
        no_rounds: NO_ROUNDS.with(|c| c.replace(0)),
        unknown_returns: UNKNOWN_RETURNS.with(|c| c.replace(0)),
        diseq_propagations: DISEQ_PROPAGATIONS.with(|c| c.replace(0)),
        conflicts_lia: CONFLICTS_LIA.with(|c| c.replace(0)),
        conflicts_lra: CONFLICTS_LRA.with(|c| c.replace(0)),
        conflicts_euf: CONFLICTS_EUF.with(|c| c.replace(0)),
        conflicts_arrays: CONFLICTS_ARRAYS.with(|c| c.replace(0)),
        checks_lia: CHECKS_LIA.with(|c| c.replace(0)),
        checks_lra: CHECKS_LRA.with(|c| c.replace(0)),
        checks_euf: CHECKS_EUF.with(|c| c.replace(0)),
        checks_arrays: CHECKS_ARRAYS.with(|c| c.replace(0)),
        props_lia: PROPS_LIA.with(|c| c.replace(0)),
        props_lra: PROPS_LRA.with(|c| c.replace(0)),
        props_euf: PROPS_EUF.with(|c| c.replace(0)),
        partial_clauses: PARTIAL_CLAUSES.with(|c| c.replace(0)),
        replay_covered_by_calls: REPLAY_COVERED_BY_CALLS.with(|c| c.replace(0)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_drain_resets_counters() {
        inc_no_rounds(5);
        inc_unknown_returns();
        inc_diseq_propagations(3);
        inc_conflict_lia();
        inc_conflict_euf();
        inc_check_lia();
        inc_check_euf();
        inc_props_euf(7);
        inc_partial_clauses();
        inc_partial_clauses();

        let stats = drain_stats();
        assert_eq!(stats.no_rounds, 5);
        assert_eq!(stats.unknown_returns, 1);
        assert_eq!(stats.diseq_propagations, 3);
        assert_eq!(stats.conflicts_lia, 1);
        assert_eq!(stats.conflicts_euf, 1);
        assert_eq!(stats.conflicts_lra, 0);
        assert_eq!(stats.conflicts_arrays, 0);
        assert_eq!(stats.checks_lia, 1);
        assert_eq!(stats.checks_euf, 1);
        assert_eq!(stats.checks_lra, 0);
        assert_eq!(stats.checks_arrays, 0);
        assert_eq!(stats.props_euf, 7);
        assert_eq!(stats.props_lia, 0);
        assert_eq!(stats.props_lra, 0);
        assert_eq!(stats.partial_clauses, 2);

        // After drain, counters should be zero
        let stats2 = drain_stats();
        assert_eq!(stats2.no_rounds, 0);
        assert_eq!(stats2.unknown_returns, 0);
        assert_eq!(stats2.checks_lia, 0);
        assert_eq!(stats2.props_euf, 0);
        assert_eq!(stats2.partial_clauses, 0);
    }

    #[test]
    fn test_inc_accumulates() {
        // Drain any leftover from other tests
        let _ = drain_stats();

        inc_no_rounds(2);
        inc_no_rounds(3);
        inc_conflict_lra();
        inc_conflict_lra();
        inc_conflict_arrays();
        inc_check_lra();
        inc_check_lra();
        inc_check_lra();
        inc_check_arrays();
        inc_props_lia(4);
        inc_props_lia(6);
        inc_props_lra(2);

        let stats = drain_stats();
        assert_eq!(stats.no_rounds, 5);
        assert_eq!(stats.conflicts_lra, 2);
        assert_eq!(stats.conflicts_arrays, 1);
        assert_eq!(stats.checks_lra, 3);
        assert_eq!(stats.checks_arrays, 1);
        assert_eq!(stats.props_lia, 10);
        assert_eq!(stats.props_lra, 2);
    }
}
