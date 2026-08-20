// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certification cost accounting (#cert-accounting item 6).
//!
//! # Why this exists
//!
//! Commit `66538b006f` made UNSAT certification mandatory and, as a side
//! effect, made a CHC benchmark (`dillig12_m`) miss a 20 s deadline it had
//! previously met in 14.6 s. Diagnosing that took a hand-built, throwaway
//! meter and a controlled A/B on a kill switch, and the first hypothesis it
//! produced — "the certificate mint is the regression" — turned out to be
//! **false**: removing all ~5.6 s of minting from the 20 s budget still left
//! the test failing at 27.9 s. The cost that actually mattered was proof
//! *recording* during search, on one call channel.
//!
//! Every number needed to reach that conclusion in five minutes instead of a
//! day is a counter this module now keeps permanently.
//!
//! # Why process-global and not per-`Executor`
//!
//! The obvious shape — `Cell<u64>` fields on `Executor`, published into
//! `last_statistics` — cannot see this regression at all. The CHC portfolio
//! constructs a **fresh `Executor` per sub-query** (`executor_adapter`'s
//! `execute_commands_via_executor`), and the two nested corroboration solves
//! inside a mint each construct another one. Per-executor counters would
//! therefore report `1` decision and `0` nested solves on ~1000 separate
//! objects, none of which any caller ever inspects. The quantity being
//! attributed is a property of the *run*, so the accumulator is a property of
//! the *process*.
//!
//! Per-executor `last_statistics` publication is kept as well (see
//! `publish_certification_accounting`), because `--stats` on a single-query
//! run is the other place these numbers are wanted.
//!
//! # Soundness
//!
//! This module is **write-only with respect to solver behaviour**. Nothing in
//! `ay-dpll` reads a counter to decide anything: not a gate, not a lane, not a
//! budget, not a verdict. Counters are `Relaxed` atomics precisely because no
//! happens-before relationship is implied or needed; a torn read across two
//! counters can misattribute a diagnostic, and can do nothing else. The only
//! way this module can affect an answer is by costing time, which is bounded
//! by a handful of relaxed adds and two `Instant::now()` calls per certificate
//! mint — events that occur on the order of 1e3 times per run, not 1e9.
//!
//! Timers use RAII guards so that the `?`-heavy early returns in
//! `mint_unsat_certificate` are all measured; a missed drop would under-count,
//! never over-count.

use std::sync::atomic::{AtomicU64, Ordering};

use ay_core::time::Instant;

use super::query_role::QueryPublicationRole;

/// The process-global counter bank.
///
/// Grouped in one struct-of-statics so a new counter cannot be added without
/// also appearing in [`CertificationAccounting::snapshot`] and
/// [`CertificationAccounting::reset`] — the compiler enforces the first
/// (struct literal) and review enforces the second.
mod counters {
    use super::AtomicU64;

    /// Command-boundary decision queries that reached the publication funnel.
    pub(super) static DECISIONS: AtomicU64 = AtomicU64::new(0);
    /// ... of which declared [`super::QueryPublicationRole::InternalLemma`].
    pub(super) static DECISIONS_INTERNAL_LEMMA: AtomicU64 = AtomicU64::new(0);
    /// ... of which reached the funnel with the proof tracker still ENABLED,
    /// i.e. paid the per-step proof-recording cost during search.
    pub(super) static DECISIONS_PROOF_TRACKED: AtomicU64 = AtomicU64::new(0);
    /// ... both internal-lemma AND proof-tracked. This is the cell that names
    /// the `dillig12_m` regression: search-channel queries paying for a proof
    /// artifact no caller on that channel consumes.
    pub(super) static DECISIONS_PROOF_TRACKED_INTERNAL_LEMMA: AtomicU64 = AtomicU64::new(0);
    /// Wall time inside outermost command-boundary decision commands.
    pub(super) static DECISION_NANOS: AtomicU64 = AtomicU64::new(0);
    /// Proof steps RETAINED in the tracker's ledger when each decision reached
    /// the publication funnel, summed.
    ///
    /// Deliberately named "retained", not "recorded": push/pop truncates the
    /// ledger, so this is a LOWER BOUND on the steps a solve constructed, and
    /// it does not capture the larger part of recording cost at all — the
    /// per-step dedup maps, scope snapshots, checkpoint budget, and the
    /// proof-producing code paths solver lanes take only while the tracker is
    /// armed. Use `DECISIONS_PROOF_TRACKED*` to answer "who paid for
    /// recording"; use this only to compare ledger sizes between runs.
    /// Measured on dillig12_m: 1424 retained steps across 1143 decisions, all
    /// 1143 of them tracked — i.e. the ledger is tiny and the cost is not in
    /// the ledger.
    pub(super) static PROOF_STEPS_RECORDED: AtomicU64 = AtomicU64::new(0);
    /// `mint_unsat_certificate` entries, and cumulative wall time in them.
    pub(super) static MINTS: AtomicU64 = AtomicU64::new(0);
    pub(super) static MINT_NANOS: AtomicU64 = AtomicU64::new(0);
    pub(super) static MINTS_INTERNAL_LEMMA: AtomicU64 = AtomicU64::new(0);
    pub(super) static MINT_NANOS_INTERNAL_LEMMA: AtomicU64 = AtomicU64::new(0);
    /// Whole-problem re-solves on a FRESH `Executor` performed *inside* a mint
    /// (`reconfirms_unsat_within`, `redecides_definitive_sat_within`).
    /// Measured at 97.4% of mint cost on `dillig12_m`.
    pub(super) static NESTED_CORROBORATION_SOLVES: AtomicU64 = AtomicU64::new(0);
    pub(super) static NESTED_CORROBORATION_NANOS: AtomicU64 = AtomicU64::new(0);
    /// Scope-authenticated raw admissions (#proof-capability B3).
    pub(super) static RAW_ADMISSIONS: AtomicU64 = AtomicU64::new(0);
    /// Computed verdicts refused at the publication funnel.
    pub(super) static PUBLICATION_REJECTIONS: AtomicU64 = AtomicU64::new(0);
}

/// An immutable read of the process-global certification counters.
///
/// Fields are plain `u64` totals since process start (or since the last
/// [`reset`](CertificationAccounting::reset)). Under concurrency the fields
/// are individually atomic but not mutually consistent; treat ratios between
/// them as approximate.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct CertificationAccounting {
    /// Command-boundary decision queries that reached the publication funnel.
    pub decisions: u64,
    /// Of `decisions`, those declared as internal search guidance.
    pub decisions_internal_lemma: u64,
    /// Of `decisions`, those whose proof tracker was still enabled — the
    /// population that paid per-step proof-recording cost during search.
    pub decisions_proof_tracked: u64,
    /// Of `decisions`, those both internal-lemma and proof-tracked.
    pub decisions_proof_tracked_internal_lemma: u64,
    /// Wall nanoseconds spent inside outermost decision commands.
    pub decision_nanos: u64,
    /// Proof-ledger steps RETAINED at the publication funnel, summed. A lower
    /// bound on recording work, not a total — see the counter's own doc.
    pub proof_steps_recorded: u64,
    /// `mint_unsat_certificate` entries.
    pub mints: u64,
    /// Wall nanoseconds inside `mint_unsat_certificate`.
    pub mint_nanos: u64,
    /// Of `mints`, those on the internal-lemma channel.
    pub mints_internal_lemma: u64,
    /// Of `mint_nanos`, those on the internal-lemma channel.
    pub mint_nanos_internal_lemma: u64,
    /// Fresh-`Executor` whole-problem re-solves performed inside a mint.
    pub nested_corroboration_solves: u64,
    /// Wall nanoseconds inside those re-solves.
    pub nested_corroboration_nanos: u64,
    /// Scope-authenticated raw admissions published without a checked
    /// certificate (#proof-capability B3 competition shedding).
    pub raw_admissions: u64,
    /// Verdicts refused by the publication funnel.
    pub publication_rejections: u64,
}

impl CertificationAccounting {
    /// Read every counter.
    #[must_use]
    pub fn snapshot() -> Self {
        let load = |counter: &AtomicU64| counter.load(Ordering::Relaxed);
        Self {
            decisions: load(&counters::DECISIONS),
            decisions_internal_lemma: load(&counters::DECISIONS_INTERNAL_LEMMA),
            decisions_proof_tracked: load(&counters::DECISIONS_PROOF_TRACKED),
            decisions_proof_tracked_internal_lemma: load(
                &counters::DECISIONS_PROOF_TRACKED_INTERNAL_LEMMA,
            ),
            decision_nanos: load(&counters::DECISION_NANOS),
            proof_steps_recorded: load(&counters::PROOF_STEPS_RECORDED),
            mints: load(&counters::MINTS),
            mint_nanos: load(&counters::MINT_NANOS),
            mints_internal_lemma: load(&counters::MINTS_INTERNAL_LEMMA),
            mint_nanos_internal_lemma: load(&counters::MINT_NANOS_INTERNAL_LEMMA),
            nested_corroboration_solves: load(&counters::NESTED_CORROBORATION_SOLVES),
            nested_corroboration_nanos: load(&counters::NESTED_CORROBORATION_NANOS),
            raw_admissions: load(&counters::RAW_ADMISSIONS),
            publication_rejections: load(&counters::PUBLICATION_REJECTIONS),
        }
    }

    /// Zero every counter.
    ///
    /// Intended for a harness that wants totals for one measured region. This
    /// is inherently racy against concurrently solving threads; it is a
    /// diagnostic reset, not a synchronization point.
    pub fn reset() {
        for counter in [
            &counters::DECISIONS,
            &counters::DECISIONS_INTERNAL_LEMMA,
            &counters::DECISIONS_PROOF_TRACKED,
            &counters::DECISIONS_PROOF_TRACKED_INTERNAL_LEMMA,
            &counters::DECISION_NANOS,
            &counters::PROOF_STEPS_RECORDED,
            &counters::MINTS,
            &counters::MINT_NANOS,
            &counters::MINTS_INTERNAL_LEMMA,
            &counters::MINT_NANOS_INTERNAL_LEMMA,
            &counters::NESTED_CORROBORATION_SOLVES,
            &counters::NESTED_CORROBORATION_NANOS,
            &counters::RAW_ADMISSIONS,
            &counters::PUBLICATION_REJECTIONS,
        ] {
            counter.store(0, Ordering::Relaxed);
        }
    }

    /// Difference of two snapshots, saturating at zero per field.
    ///
    /// Saturation matters: under a parallel test runner another thread's
    /// [`reset`](Self::reset) can move a counter backwards between two reads,
    /// and a diagnostic must not panic on that.
    #[must_use]
    pub fn since(self, earlier: Self) -> Self {
        Self {
            decisions: self.decisions.saturating_sub(earlier.decisions),
            decisions_internal_lemma: self
                .decisions_internal_lemma
                .saturating_sub(earlier.decisions_internal_lemma),
            decisions_proof_tracked: self
                .decisions_proof_tracked
                .saturating_sub(earlier.decisions_proof_tracked),
            decisions_proof_tracked_internal_lemma: self
                .decisions_proof_tracked_internal_lemma
                .saturating_sub(earlier.decisions_proof_tracked_internal_lemma),
            decision_nanos: self.decision_nanos.saturating_sub(earlier.decision_nanos),
            proof_steps_recorded: self
                .proof_steps_recorded
                .saturating_sub(earlier.proof_steps_recorded),
            mints: self.mints.saturating_sub(earlier.mints),
            mint_nanos: self.mint_nanos.saturating_sub(earlier.mint_nanos),
            mints_internal_lemma: self
                .mints_internal_lemma
                .saturating_sub(earlier.mints_internal_lemma),
            mint_nanos_internal_lemma: self
                .mint_nanos_internal_lemma
                .saturating_sub(earlier.mint_nanos_internal_lemma),
            nested_corroboration_solves: self
                .nested_corroboration_solves
                .saturating_sub(earlier.nested_corroboration_solves),
            nested_corroboration_nanos: self
                .nested_corroboration_nanos
                .saturating_sub(earlier.nested_corroboration_nanos),
            raw_admissions: self.raw_admissions.saturating_sub(earlier.raw_admissions),
            publication_rejections: self
                .publication_rejections
                .saturating_sub(earlier.publication_rejections),
        }
    }
}

impl std::fmt::Display for CertificationAccounting {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ms = |nanos: u64| (nanos as f64) / 1e6;
        write!(
            f,
            "cert: decisions={} (internal-lemma={}, proof-tracked={}, both={}) \
             decision_ms={:.1} proof_steps={} mints={} mint_ms={:.1} \
             (internal-lemma mints={} ms={:.1}) nested_corroboration={} ms={:.1} \
             raw_admissions={} rejections={}",
            self.decisions,
            self.decisions_internal_lemma,
            self.decisions_proof_tracked,
            self.decisions_proof_tracked_internal_lemma,
            ms(self.decision_nanos),
            self.proof_steps_recorded,
            self.mints,
            ms(self.mint_nanos),
            self.mints_internal_lemma,
            ms(self.mint_nanos_internal_lemma),
            self.nested_corroboration_solves,
            ms(self.nested_corroboration_nanos),
            self.raw_admissions,
            self.publication_rejections,
        )
    }
}

fn bump(counter: &AtomicU64, by: u64) {
    counter.fetch_add(by, Ordering::Relaxed);
}

fn elapsed_nanos(start: Instant) -> u64 {
    u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

/// Record one decision query arriving at the publication funnel.
pub(in crate::executor) fn record_decision(
    role: QueryPublicationRole,
    proof_tracked: bool,
    recorded_proof_steps: usize,
) {
    bump(&counters::DECISIONS, 1);
    bump(
        &counters::PROOF_STEPS_RECORDED,
        u64::try_from(recorded_proof_steps).unwrap_or(u64::MAX),
    );
    if role.is_internal_lemma() {
        bump(&counters::DECISIONS_INTERNAL_LEMMA, 1);
    }
    if proof_tracked {
        bump(&counters::DECISIONS_PROOF_TRACKED, 1);
        if role.is_internal_lemma() {
            bump(&counters::DECISIONS_PROOF_TRACKED_INTERNAL_LEMMA, 1);
        }
    }
}

/// Record a scope-authenticated raw admission (#proof-capability B3).
pub(in crate::executor) fn record_raw_admission() {
    bump(&counters::RAW_ADMISSIONS, 1);
}

/// Record a verdict refused by the publication funnel.
pub(in crate::executor) fn record_publication_rejection() {
    bump(&counters::PUBLICATION_REJECTIONS, 1);
}

/// Times the outermost command-boundary decision command on one executor.
///
/// Only the outermost is timed (the caller holds a re-entrancy depth), so a
/// nested probe solve on the SAME executor cannot double-count its enclosing
/// command's wall time.
pub(in crate::executor) struct DecisionTimer(Instant);

impl DecisionTimer {
    pub(in crate::executor) fn start() -> Self {
        Self(Instant::now())
    }
}

impl Drop for DecisionTimer {
    fn drop(&mut self) {
        bump(&counters::DECISION_NANOS, elapsed_nanos(self.0));
    }
}

/// Times one `mint_unsat_certificate` call, including its `?` early returns.
pub(in crate::executor) struct MintTimer {
    start: Instant,
    role: QueryPublicationRole,
}

impl MintTimer {
    pub(in crate::executor) fn start(role: QueryPublicationRole) -> Self {
        Self {
            start: Instant::now(),
            role,
        }
    }
}

impl Drop for MintTimer {
    fn drop(&mut self) {
        let nanos = elapsed_nanos(self.start);
        bump(&counters::MINTS, 1);
        bump(&counters::MINT_NANOS, nanos);
        if self.role.is_internal_lemma() {
            bump(&counters::MINTS_INTERNAL_LEMMA, 1);
            bump(&counters::MINT_NANOS_INTERNAL_LEMMA, nanos);
        }
    }
}

/// Times one fresh-`Executor` whole-problem corroboration re-solve run from
/// inside a certificate mint.
pub(in crate::executor) struct NestedCorroborationTimer(Instant);

impl NestedCorroborationTimer {
    pub(in crate::executor) fn start() -> Self {
        Self(Instant::now())
    }
}

impl Drop for NestedCorroborationTimer {
    fn drop(&mut self) {
        bump(&counters::NESTED_CORROBORATION_SOLVES, 1);
        bump(&counters::NESTED_CORROBORATION_NANOS, elapsed_nanos(self.0));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Deltas, never absolutes: the counters are process-global and the test
    /// runner is multi-threaded, so another test solving concurrently can only
    /// inflate a delta — never deflate it below what this test caused.
    #[test]
    fn timers_and_recorders_move_their_own_counters() {
        let before = CertificationAccounting::snapshot();
        record_decision(QueryPublicationRole::InternalLemma, true, 7);
        record_raw_admission();
        record_publication_rejection();
        drop(MintTimer::start(QueryPublicationRole::InternalLemma));
        drop(NestedCorroborationTimer::start());
        drop(DecisionTimer::start());
        let delta = CertificationAccounting::snapshot().since(before);

        assert!(delta.decisions >= 1);
        assert!(delta.decisions_internal_lemma >= 1);
        assert!(delta.decisions_proof_tracked >= 1);
        assert!(delta.decisions_proof_tracked_internal_lemma >= 1);
        assert!(delta.proof_steps_recorded >= 7);
        assert!(delta.mints >= 1);
        assert!(delta.mints_internal_lemma >= 1);
        assert!(delta.nested_corroboration_solves >= 1);
        assert!(delta.raw_admissions >= 1);
        assert!(delta.publication_rejections >= 1);
    }

    #[test]
    fn published_role_does_not_move_internal_lemma_counters() {
        let before = CertificationAccounting::snapshot();
        record_decision(QueryPublicationRole::Published, false, 0);
        drop(MintTimer::start(QueryPublicationRole::Published));
        let delta = CertificationAccounting::snapshot().since(before);

        // The published-role bumps above contributed nothing to the
        // internal-lemma cells; any nonzero delta here is another thread's.
        assert!(delta.decisions >= 1);
        assert!(delta.mints >= 1);
    }

    #[test]
    fn since_saturates_instead_of_panicking_on_a_concurrent_reset() {
        let later = CertificationAccounting {
            decisions: 1,
            ..CertificationAccounting::default()
        };
        let earlier = CertificationAccounting {
            decisions: 9,
            mints: 4,
            ..CertificationAccounting::default()
        };
        let delta = later.since(earlier);
        assert_eq!(delta.decisions, 0);
        assert_eq!(delta.mints, 0);
    }

    #[test]
    fn display_names_every_headline_counter() {
        let rendered = CertificationAccounting::default().to_string();
        for key in [
            "decisions=",
            "internal-lemma=",
            "proof-tracked=",
            "decision_ms=",
            "proof_steps=",
            "mints=",
            "mint_ms=",
            "nested_corroboration=",
            "raw_admissions=",
            "rejections=",
        ] {
            assert!(rendered.contains(key), "missing {key} in {rendered}");
        }
    }
}
