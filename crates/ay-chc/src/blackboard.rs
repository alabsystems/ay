// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// WIP cross-engine cooperation infrastructure. Lemma sharing is live; CEX and
// proof-hint channels are infrastructure-complete but producers/consumers are
// not yet wired. Remove this allow when all three channels are in use.
#![allow(dead_code)]

//! Cooperative blackboard for cross-engine information sharing.
//!
//! When engines run in parallel, they can publish and consume three
//! categories of information through a shared blackboard:
//!
//! 1. **Lemmas** — PDR/CEGAR publish learned invariant candidates that
//!    other PDR engines consume via the [`LemmaHintProvider`] trait.
//!
//! 2. **Counterexample paths (CEX)** — BMC/CEGAR publish reachable state
//!    sequences. PDR engines consume these to focus their backward search
//!    on reachable regions, avoiding wasted generalization effort.
//!
//! 3. **Proof hints** — Engines publish directional suggestions (e.g.,
//!    "k-induction converged at depth 5", "predicate P needs modular
//!    invariant"). Other engines consume these to adjust their strategy.
//!
//! This is the AY analogue of clause sharing in parallel SAT solvers
//! (MallobSAT, Painless) and the shared lemma databases used by
//! Spacer's multiple contexts.
//!
//! Part of #7910 (Cooperative blackboard) under epic #7909.

use crate::lemma_hints::{HintRequest, LemmaHint, LemmaHintProvider};
use crate::PredicateId;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

/// Maximum lemmas stored in the blackboard before oldest are evicted.
const MAX_BLACKBOARD_LEMMAS: usize = 500;

/// Maximum counterexample traces stored before oldest are evicted.
const MAX_CEX_TRACES: usize = 50;

/// Maximum proof hints stored before oldest are evicted.
const MAX_PROOF_HINTS: usize = 100;

// ============================================================================
// Lemma channel (existing)
// ============================================================================

/// A lemma entry in the blackboard, tagged with the producing engine.
#[derive(Debug, Clone)]
struct LemmaEntry {
    predicate: PredicateId,
    formula: crate::ChcExpr,
    /// Index of the producing engine (for avoiding self-consumption).
    producer_idx: usize,
    /// Frame level from the producer (higher = more mature).
    frame_level: usize,
}

// ============================================================================
// CEX channel (new)
// ============================================================================

/// A shared counterexample trace published by BMC or CEGAR.
///
/// This represents a (possibly partial) path from an initial state toward
/// a bad state. PDR engines can use these paths to bias their backward
/// reachability search toward states that BMC has shown are reachable,
/// avoiding wasted generalization effort on unreachable regions.
///
/// Reference: Spacer's "must" vs "may" reachability sets in
/// `reference/z3/src/muz/spacer/spacer_context.cpp`.
#[derive(Debug, Clone)]
pub(crate) struct CexEntry {
    /// Predicate IDs along the counterexample path, from initial to bad.
    pub(crate) path: Vec<PredicateId>,
    /// State expressions at each step (parallel to `path`).
    /// Each expression describes the reachable state at that step.
    pub(crate) states: Vec<crate::ChcExpr>,
    /// Depth at which BMC found this trace (0 = init-only).
    pub(crate) depth: usize,
    /// Whether this is a complete counterexample (reaches bad state)
    /// or a partial prefix (reachable states that haven't yet reached bad).
    pub(crate) is_complete: bool,
    /// Index of the producing engine.
    producer_idx: usize,
}

// ============================================================================
// Proof hint channel (new)
// ============================================================================

/// A proof direction hint published by one engine for others.
///
/// Hints are advisory suggestions — consuming engines may ignore them.
/// They carry no soundness obligation; an incorrect hint just wastes
/// the consumer's time, it doesn't compromise correctness.
#[derive(Debug, Clone)]
pub(crate) struct ProofHint {
    /// The kind of hint being communicated.
    pub(crate) kind: ProofHintKind,
    /// Engine that published this hint.
    producer_idx: usize,
}

/// Categories of proof direction hints.
///
/// These are lightweight signals that engines send to guide each other's
/// search. Each variant carries just enough information for the consumer
/// to adjust its strategy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProofHintKind {
    /// k-induction converged at a specific depth for a predicate.
    /// PDR can use this to set its initial frame depth, avoiding
    /// redundant work at shallower levels.
    KInductionDepth {
        predicate: PredicateId,
        depth: usize,
    },

    /// BMC found a reachable state at this depth without hitting bad.
    /// Signals that the property likely holds up to this depth, so
    /// PDR can be more aggressive with generalization.
    BmcSafeDepth { depth: usize },

    /// An engine suspects that a predicate needs a modular/remainder
    /// invariant (e.g., because it observed periodic patterns in
    /// counterexample attempts). The `modulus` field suggests the
    /// period length.
    NeedsModularInvariant {
        predicate: PredicateId,
        modulus: u64,
    },

    /// An engine suggests focusing on a specific predicate because
    /// it appears to be the bottleneck (e.g., all other predicates
    /// have converged but this one has not).
    FocusPredicate { predicate: PredicateId },

    /// An engine found that interpolation produced useful lemmas at
    /// a specific unrolling depth. Other interpolation-based engines
    /// (IMC, LAWI) can start from this depth.
    InterpolationDepth { depth: usize },
}

// ============================================================================
// SharedBlackboard
// ============================================================================

/// Shared blackboard for cross-engine information exchange.
///
/// Thread-safe: engines publish via [`publish`], [`publish_cex`], and
/// [`publish_hint`], and consume via the various consumer types.
///
/// Three independent version counters allow consumers to check for new
/// data in their channel without acquiring locks for unchanged channels.
#[derive(Debug)]
pub(crate) struct SharedBlackboard {
    // --- Lemma channel ---
    lemmas: Mutex<Vec<LemmaEntry>>,
    lemma_version: AtomicUsize,

    // --- CEX channel ---
    cex_traces: Mutex<Vec<CexEntry>>,
    cex_version: AtomicUsize,

    // --- Proof hint channel ---
    hints: Mutex<Vec<ProofHint>>,
    hint_version: AtomicUsize,
}

impl SharedBlackboard {
    /// Create a new empty blackboard.
    pub(crate) fn new() -> Arc<Self> {
        Arc::new(Self {
            lemmas: Mutex::new(Vec::new()),
            lemma_version: AtomicUsize::new(0),
            cex_traces: Mutex::new(Vec::new()),
            cex_version: AtomicUsize::new(0),
            hints: Mutex::new(Vec::new()),
            hint_version: AtomicUsize::new(0),
        })
    }

    // ----------------------------------------------------------------
    // Lemma channel
    // ----------------------------------------------------------------

    /// Publish lemmas from an engine to the blackboard.
    ///
    /// Lemmas are tagged with `producer_idx` so the producing engine
    /// can skip its own lemmas when consuming. Higher `frame_level`
    /// lemmas survive longer when the blackboard is full.
    pub(crate) fn publish(
        &self,
        producer_idx: usize,
        lemmas: impl IntoIterator<Item = (PredicateId, crate::ChcExpr, usize)>,
    ) {
        let mut store = self.lemmas.lock().unwrap_or_else(|e| e.into_inner());

        for (predicate, formula, frame_level) in lemmas {
            // Deduplicate: skip if an identical (predicate, formula) exists.
            let already_exists = store
                .iter()
                .any(|e| e.predicate == predicate && e.formula == formula);
            if already_exists {
                continue;
            }
            store.push(LemmaEntry {
                predicate,
                formula,
                producer_idx,
                frame_level,
            });
        }

        // Evict lowest-frame-level lemmas when over capacity.
        if store.len() > MAX_BLACKBOARD_LEMMAS {
            store.sort_by_key(|entry| std::cmp::Reverse(entry.frame_level));
            store.truncate(MAX_BLACKBOARD_LEMMAS);
        }

        self.lemma_version.fetch_add(1, Ordering::Release);
    }

    /// Current lemma version counter. Consumers use this to detect changes.
    pub(crate) fn version(&self) -> usize {
        self.lemma_version.load(Ordering::Acquire)
    }

    /// Read all lemmas not produced by `consumer_idx`.
    fn read_for(&self, consumer_idx: usize) -> Vec<LemmaHint> {
        let store = self.lemmas.lock().unwrap_or_else(|e| e.into_inner());
        store
            .iter()
            .filter(|e| e.producer_idx != consumer_idx)
            .map(|e| LemmaHint {
                predicate: e.predicate,
                formula: e.formula.clone(),
                priority: 0,
                source: "blackboard",
            })
            .collect()
    }

    /// Total number of lemmas currently stored (for diagnostics).
    pub(crate) fn lemma_count(&self) -> usize {
        self.lemmas.lock().unwrap_or_else(|e| e.into_inner()).len()
    }

    // ----------------------------------------------------------------
    // CEX channel
    // ----------------------------------------------------------------

    /// Publish a counterexample trace from BMC or CEGAR.
    ///
    /// The trace is tagged with `producer_idx` so the producing engine
    /// skips its own traces when consuming. Deeper traces (higher `depth`)
    /// are more valuable and survive eviction longer.
    pub(crate) fn publish_cex(
        &self,
        producer_idx: usize,
        path: Vec<PredicateId>,
        states: Vec<crate::ChcExpr>,
        depth: usize,
        is_complete: bool,
    ) {
        let mut store = self.cex_traces.lock().unwrap_or_else(|e| e.into_inner());

        // Deduplicate: skip if an identical (path, depth, is_complete) exists.
        let already_exists = store
            .iter()
            .any(|e| e.path == path && e.depth == depth && e.is_complete == is_complete);
        if already_exists {
            return;
        }

        store.push(CexEntry {
            path,
            states,
            depth,
            is_complete,
            producer_idx,
        });

        // Evict shallowest traces when over capacity.
        if store.len() > MAX_CEX_TRACES {
            store.sort_by_key(|entry| std::cmp::Reverse(entry.depth));
            store.truncate(MAX_CEX_TRACES);
        }

        self.cex_version.fetch_add(1, Ordering::Release);
    }

    /// Current CEX version counter.
    pub(crate) fn cex_version(&self) -> usize {
        self.cex_version.load(Ordering::Acquire)
    }

    /// Read all CEX traces not produced by `consumer_idx`.
    fn read_cex_for(&self, consumer_idx: usize) -> Vec<CexEntry> {
        let store = self.cex_traces.lock().unwrap_or_else(|e| e.into_inner());
        store
            .iter()
            .filter(|e| e.producer_idx != consumer_idx)
            .cloned()
            .collect()
    }

    /// Total number of CEX traces currently stored (for diagnostics).
    pub(crate) fn cex_count(&self) -> usize {
        self.cex_traces
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .len()
    }

    // ----------------------------------------------------------------
    // Proof hint channel
    // ----------------------------------------------------------------

    /// Publish a proof direction hint.
    ///
    /// Hints are advisory and carry no soundness obligation. Duplicate
    /// hints (same kind and producer) are deduplicated.
    pub(crate) fn publish_hint(&self, producer_idx: usize, kind: ProofHintKind) {
        let mut store = self.hints.lock().unwrap_or_else(|e| e.into_inner());

        // Deduplicate: skip if an identical (kind, producer) exists.
        let already_exists = store
            .iter()
            .any(|e| e.kind == kind && e.producer_idx == producer_idx);
        if already_exists {
            return;
        }

        store.push(ProofHint { kind, producer_idx });

        // Evict oldest hints when over capacity.
        if store.len() > MAX_PROOF_HINTS {
            // Keep the most recent hints.
            let excess = store.len() - MAX_PROOF_HINTS;
            store.drain(..excess);
        }

        self.hint_version.fetch_add(1, Ordering::Release);
    }

    /// Current hint version counter.
    pub(crate) fn hint_version(&self) -> usize {
        self.hint_version.load(Ordering::Acquire)
    }

    /// Read all proof hints not produced by `consumer_idx`.
    fn read_hints_for(&self, consumer_idx: usize) -> Vec<ProofHint> {
        let store = self.hints.lock().unwrap_or_else(|e| e.into_inner());
        store
            .iter()
            .filter(|e| e.producer_idx != consumer_idx)
            .cloned()
            .collect()
    }

    /// Total number of proof hints currently stored (for diagnostics).
    pub(crate) fn hint_count(&self) -> usize {
        self.hints.lock().unwrap_or_else(|e| e.into_inner()).len()
    }
}

// ============================================================================
// Lemma consumer (existing)
// ============================================================================

/// A [`LemmaHintProvider`] that reads from a [`SharedBlackboard`].
///
/// Each PDR engine in the portfolio gets its own `BlackboardHintProvider`
/// with a distinct `engine_idx`, so it skips its own published lemmas.
pub(crate) struct BlackboardHintProvider {
    blackboard: Arc<SharedBlackboard>,
    /// This engine's index in the portfolio (to skip self-produced lemmas).
    engine_idx: usize,
    /// Last version this consumer saw. When the blackboard version
    /// matches, `collect` returns nothing (no new lemmas).
    last_seen_version: AtomicUsize,
}

impl BlackboardHintProvider {
    pub(crate) fn new(blackboard: Arc<SharedBlackboard>, engine_idx: usize) -> Self {
        Self {
            blackboard,
            engine_idx,
            last_seen_version: AtomicUsize::new(0),
        }
    }
}

impl std::fmt::Debug for BlackboardHintProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "BlackboardHintProvider(engine={}, version={})",
            self.engine_idx,
            self.last_seen_version.load(Ordering::Relaxed)
        )
    }
}

impl LemmaHintProvider for BlackboardHintProvider {
    fn collect(&self, _req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
        let current_version = self.blackboard.version();
        let last = self.last_seen_version.load(Ordering::Acquire);
        if current_version == last {
            // No new lemmas since last read.
            return;
        }
        self.last_seen_version
            .store(current_version, Ordering::Release);
        out.extend(self.blackboard.read_for(self.engine_idx));
    }
}

// ============================================================================
// CEX consumer (new)
// ============================================================================

/// Consumer for counterexample traces from the blackboard.
///
/// Each engine gets its own `CexConsumer` with a distinct `engine_idx`.
/// The version-tracking pattern matches [`BlackboardHintProvider`]: if
/// the CEX version hasn't changed since the last read, `drain_new`
/// returns an empty vec without acquiring the lock.
pub(crate) struct CexConsumer {
    blackboard: Arc<SharedBlackboard>,
    engine_idx: usize,
    last_seen_version: AtomicUsize,
}

impl CexConsumer {
    pub(crate) fn new(blackboard: Arc<SharedBlackboard>, engine_idx: usize) -> Self {
        Self {
            blackboard,
            engine_idx,
            last_seen_version: AtomicUsize::new(0),
        }
    }

    /// Drain new counterexample traces since the last read.
    ///
    /// Returns an empty vec if no new traces have been published since
    /// the last call. Traces produced by this consumer's engine are
    /// excluded.
    pub(crate) fn drain_new(&self) -> Vec<CexEntry> {
        let current = self.blackboard.cex_version();
        let last = self.last_seen_version.load(Ordering::Acquire);
        if current == last {
            return Vec::new();
        }
        self.last_seen_version.store(current, Ordering::Release);
        self.blackboard.read_cex_for(self.engine_idx)
    }
}

impl std::fmt::Debug for CexConsumer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "CexConsumer(engine={}, version={})",
            self.engine_idx,
            self.last_seen_version.load(Ordering::Relaxed)
        )
    }
}

// ============================================================================
// Proof hint consumer (new)
// ============================================================================

/// Consumer for proof direction hints from the blackboard.
///
/// Same version-tracking pattern as [`CexConsumer`] and
/// [`BlackboardHintProvider`].
pub(crate) struct ProofHintConsumer {
    blackboard: Arc<SharedBlackboard>,
    engine_idx: usize,
    last_seen_version: AtomicUsize,
}

impl ProofHintConsumer {
    pub(crate) fn new(blackboard: Arc<SharedBlackboard>, engine_idx: usize) -> Self {
        Self {
            blackboard,
            engine_idx,
            last_seen_version: AtomicUsize::new(0),
        }
    }

    /// Drain new proof hints since the last read.
    ///
    /// Returns an empty vec if no new hints have been published since
    /// the last call. Hints produced by this consumer's engine are
    /// excluded.
    pub(crate) fn drain_new(&self) -> Vec<ProofHint> {
        let current = self.blackboard.hint_version();
        let last = self.last_seen_version.load(Ordering::Acquire);
        if current == last {
            return Vec::new();
        }
        self.last_seen_version.store(current, Ordering::Release);
        self.blackboard.read_hints_for(self.engine_idx)
    }

    /// Check if there are new hints without consuming them.
    ///
    /// Useful for engines that want to poll cheaply before committing
    /// to a full hint read.
    pub(crate) fn has_new(&self) -> bool {
        let current = self.blackboard.hint_version();
        let last = self.last_seen_version.load(Ordering::Acquire);
        current != last
    }
}

impl std::fmt::Debug for ProofHintConsumer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ProofHintConsumer(engine={}, version={})",
            self.engine_idx,
            self.last_seen_version.load(Ordering::Relaxed)
        )
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcExpr, PredicateId};

    fn pred(id: u32) -> PredicateId {
        PredicateId(id)
    }

    // --- Lemma channel tests (preserved from original) ---

    #[test]
    fn test_publish_and_read() {
        let bb = SharedBlackboard::new();

        // Engine 0 publishes two lemmas.
        bb.publish(
            0,
            vec![
                (pred(0), ChcExpr::Bool(true), 3),
                (pred(1), ChcExpr::int(42), 5),
            ],
        );
        assert_eq!(bb.version(), 1);

        // Engine 1 reads: should see both.
        let hints = bb.read_for(1);
        assert_eq!(hints.len(), 2);
        assert_eq!(hints[0].source, "blackboard");

        // Engine 0 reads: should see nothing (self-produced).
        let hints = bb.read_for(0);
        assert_eq!(hints.len(), 0);
    }

    #[test]
    fn test_deduplication() {
        let bb = SharedBlackboard::new();
        let expr = ChcExpr::int(99);

        bb.publish(0, vec![(pred(0), expr.clone(), 3)]);
        bb.publish(1, vec![(pred(0), expr, 5)]);

        // Only one copy should exist.
        let hints = bb.read_for(2);
        assert_eq!(hints.len(), 1);
    }

    #[test]
    fn test_eviction_keeps_high_frame_lemmas() {
        let bb = SharedBlackboard::new();

        // Publish more than MAX_BLACKBOARD_LEMMAS.
        let lemmas: Vec<_> = (0..MAX_BLACKBOARD_LEMMAS + 50)
            .map(|i| (pred(0), ChcExpr::int(i as i64), i))
            .collect();
        bb.publish(0, lemmas);

        let hints = bb.read_for(1);
        assert_eq!(hints.len(), MAX_BLACKBOARD_LEMMAS);

        // All remaining should be from the higher frame levels.
        // The lowest 50 frame levels should have been evicted.
    }

    #[test]
    fn test_provider_version_tracking() {
        let bb = SharedBlackboard::new();
        let provider = BlackboardHintProvider::new(bb.clone(), 1);

        // Before any publish: no hints.
        let mut out = Vec::new();
        let req = crate::lemma_hints::HintRequest::empty_for_test();
        provider.collect(&req, &mut out);
        assert!(out.is_empty());

        // Publish from engine 0.
        bb.publish(0, vec![(pred(0), ChcExpr::Bool(false), 2)]);

        // Now collect should find the new lemma.
        provider.collect(&req, &mut out);
        assert_eq!(out.len(), 1);

        // Second collect without new publish: nothing new.
        out.clear();
        provider.collect(&req, &mut out);
        assert!(out.is_empty());
    }

    // --- CEX channel tests ---

    #[test]
    fn test_cex_publish_and_read() {
        let bb = SharedBlackboard::new();

        // Engine 0 (BMC) publishes a CEX trace.
        bb.publish_cex(
            0,
            vec![pred(0), pred(0), pred(0)],
            vec![ChcExpr::int(0), ChcExpr::int(1), ChcExpr::int(2)],
            2,
            false,
        );
        assert_eq!(bb.cex_version(), 1);
        assert_eq!(bb.cex_count(), 1);

        // Engine 1 (PDR) reads: should see the trace.
        let traces = bb.read_cex_for(1);
        assert_eq!(traces.len(), 1);
        assert_eq!(traces[0].depth, 2);
        assert!(!traces[0].is_complete);
        assert_eq!(traces[0].path.len(), 3);

        // Engine 0 reads: should see nothing (self-produced).
        let traces = bb.read_cex_for(0);
        assert_eq!(traces.len(), 0);
    }

    #[test]
    fn test_cex_deduplication() {
        let bb = SharedBlackboard::new();

        // Two engines publish the same path at the same depth.
        bb.publish_cex(0, vec![pred(0)], vec![ChcExpr::int(0)], 1, false);
        bb.publish_cex(1, vec![pred(0)], vec![ChcExpr::int(0)], 1, false);

        // Only one copy should exist (same path, depth, is_complete).
        let traces = bb.read_cex_for(2);
        assert_eq!(traces.len(), 1);
    }

    #[test]
    fn test_cex_different_depths_not_deduplicated() {
        let bb = SharedBlackboard::new();

        bb.publish_cex(0, vec![pred(0)], vec![ChcExpr::int(0)], 1, false);
        bb.publish_cex(0, vec![pred(0)], vec![ChcExpr::int(0)], 2, false);

        // Different depths means different entries.
        let traces = bb.read_cex_for(1);
        assert_eq!(traces.len(), 2);
    }

    #[test]
    fn test_cex_eviction_keeps_deep_traces() {
        let bb = SharedBlackboard::new();

        // Publish more than MAX_CEX_TRACES.
        for i in 0..(MAX_CEX_TRACES + 10) {
            bb.publish_cex(0, vec![pred(0)], vec![ChcExpr::int(i as i64)], i, false);
        }

        let traces = bb.read_cex_for(1);
        assert_eq!(traces.len(), MAX_CEX_TRACES);

        // All surviving traces should have depth >= 10 (the 10 shallowest evicted).
        for trace in &traces {
            assert!(trace.depth >= 10);
        }
    }

    #[test]
    fn test_cex_consumer_version_tracking() {
        let bb = SharedBlackboard::new();
        let consumer = CexConsumer::new(bb.clone(), 1);

        // Before any publish: no traces.
        let traces = consumer.drain_new();
        assert!(traces.is_empty());

        // Engine 0 publishes.
        bb.publish_cex(0, vec![pred(0)], vec![ChcExpr::int(5)], 3, true);

        // First drain: should get the trace.
        let traces = consumer.drain_new();
        assert_eq!(traces.len(), 1);
        assert!(traces[0].is_complete);

        // Second drain without new publish: nothing new.
        let traces = consumer.drain_new();
        assert!(traces.is_empty());
    }

    #[test]
    fn test_cex_complete_vs_partial() {
        let bb = SharedBlackboard::new();

        // Partial trace (BMC found reachable prefix but not yet bad).
        bb.publish_cex(
            0,
            vec![pred(0), pred(1)],
            vec![ChcExpr::int(0), ChcExpr::int(1)],
            1,
            false,
        );

        // Complete trace (BMC proved unsafety).
        bb.publish_cex(
            0,
            vec![pred(0), pred(1), pred(2)],
            vec![ChcExpr::int(0), ChcExpr::int(1), ChcExpr::int(2)],
            2,
            true,
        );

        let traces = bb.read_cex_for(1);
        assert_eq!(traces.len(), 2);

        let partial = traces.iter().find(|t| !t.is_complete).unwrap();
        let complete = traces.iter().find(|t| t.is_complete).unwrap();
        assert_eq!(partial.depth, 1);
        assert_eq!(complete.depth, 2);
    }

    // --- Proof hint channel tests ---

    #[test]
    fn test_hint_publish_and_read() {
        let bb = SharedBlackboard::new();

        // Engine 0 (Kind) publishes a k-induction depth hint.
        bb.publish_hint(
            0,
            ProofHintKind::KInductionDepth {
                predicate: pred(0),
                depth: 5,
            },
        );
        assert_eq!(bb.hint_version(), 1);
        assert_eq!(bb.hint_count(), 1);

        // Engine 1 (PDR) reads: should see the hint.
        let hints = bb.read_hints_for(1);
        assert_eq!(hints.len(), 1);
        assert_eq!(
            hints[0].kind,
            ProofHintKind::KInductionDepth {
                predicate: pred(0),
                depth: 5,
            }
        );

        // Engine 0 reads: should see nothing (self-produced).
        let hints = bb.read_hints_for(0);
        assert_eq!(hints.len(), 0);
    }

    #[test]
    fn test_hint_deduplication() {
        let bb = SharedBlackboard::new();

        // Same engine publishes the same hint twice.
        bb.publish_hint(0, ProofHintKind::BmcSafeDepth { depth: 10 });
        bb.publish_hint(0, ProofHintKind::BmcSafeDepth { depth: 10 });

        // Only one copy should exist.
        let hints = bb.read_hints_for(1);
        assert_eq!(hints.len(), 1);
    }

    #[test]
    fn test_hint_different_producers_not_deduplicated() {
        let bb = SharedBlackboard::new();

        // Two different engines publish the same kind of hint.
        bb.publish_hint(0, ProofHintKind::BmcSafeDepth { depth: 10 });
        bb.publish_hint(1, ProofHintKind::BmcSafeDepth { depth: 10 });

        // Both exist (different producers).
        let hints = bb.read_hints_for(2);
        assert_eq!(hints.len(), 2);
    }

    #[test]
    fn test_hint_consumer_version_tracking() {
        let bb = SharedBlackboard::new();
        let consumer = ProofHintConsumer::new(bb.clone(), 1);

        // Before any publish: no hints, has_new is false.
        assert!(!consumer.has_new());
        let hints = consumer.drain_new();
        assert!(hints.is_empty());

        // Engine 0 publishes.
        bb.publish_hint(0, ProofHintKind::FocusPredicate { predicate: pred(2) });

        // has_new detects the change without consuming.
        assert!(consumer.has_new());

        // Drain: should get the hint.
        let hints = consumer.drain_new();
        assert_eq!(hints.len(), 1);

        // After drain: no more new hints.
        assert!(!consumer.has_new());
        let hints = consumer.drain_new();
        assert!(hints.is_empty());
    }

    #[test]
    fn test_hint_eviction_keeps_recent() {
        let bb = SharedBlackboard::new();

        // Publish more than MAX_PROOF_HINTS.
        for i in 0..(MAX_PROOF_HINTS + 20) {
            bb.publish_hint(0, ProofHintKind::BmcSafeDepth { depth: i });
        }

        let hints = bb.read_hints_for(1);
        assert_eq!(hints.len(), MAX_PROOF_HINTS);

        // The oldest 20 should have been evicted (drain from front).
        // Remaining hints should be depth 20..120.
        let min_depth = hints
            .iter()
            .filter_map(|h| match &h.kind {
                ProofHintKind::BmcSafeDepth { depth } => Some(*depth),
                _ => None,
            })
            .min()
            .unwrap();
        assert_eq!(min_depth, 20);
    }

    #[test]
    fn test_hint_modular_invariant() {
        let bb = SharedBlackboard::new();

        bb.publish_hint(
            0,
            ProofHintKind::NeedsModularInvariant {
                predicate: pred(1),
                modulus: 3,
            },
        );

        let hints = bb.read_hints_for(1);
        assert_eq!(hints.len(), 1);
        match &hints[0].kind {
            ProofHintKind::NeedsModularInvariant { predicate, modulus } => {
                assert_eq!(*predicate, pred(1));
                assert_eq!(*modulus, 3);
            }
            other => panic!("unexpected hint kind: {:?}", other),
        }
    }

    #[test]
    fn test_hint_interpolation_depth() {
        let bb = SharedBlackboard::new();

        bb.publish_hint(0, ProofHintKind::InterpolationDepth { depth: 7 });

        let consumer = ProofHintConsumer::new(bb.clone(), 1);
        let hints = consumer.drain_new();
        assert_eq!(hints.len(), 1);
        assert_eq!(
            hints[0].kind,
            ProofHintKind::InterpolationDepth { depth: 7 }
        );
    }

    // --- Cross-channel independence tests ---

    #[test]
    fn test_channels_are_independent() {
        let bb = SharedBlackboard::new();

        // Publish to each channel.
        bb.publish(0, vec![(pred(0), ChcExpr::Bool(true), 1)]);
        bb.publish_cex(1, vec![pred(0)], vec![ChcExpr::int(0)], 1, false);
        bb.publish_hint(2, ProofHintKind::BmcSafeDepth { depth: 5 });

        // Each channel has independent version counters.
        assert_eq!(bb.version(), 1);
        assert_eq!(bb.cex_version(), 1);
        assert_eq!(bb.hint_version(), 1);

        // Publishing to one channel doesn't affect others.
        bb.publish(0, vec![(pred(1), ChcExpr::Bool(false), 2)]);
        assert_eq!(bb.version(), 2);
        assert_eq!(bb.cex_version(), 1);
        assert_eq!(bb.hint_version(), 1);
    }

    #[test]
    fn test_concurrent_access_simulation() {
        // Simulate multiple engines publishing and consuming.
        let bb = SharedBlackboard::new();

        // Engine 0 (BMC): publish CEX and safe-depth hints.
        bb.publish_cex(0, vec![pred(0)], vec![ChcExpr::int(0)], 3, false);
        bb.publish_hint(0, ProofHintKind::BmcSafeDepth { depth: 3 });

        // Engine 1 (PDR): publish lemmas.
        bb.publish(
            1,
            vec![
                (pred(0), ChcExpr::int(10), 5),
                (pred(0), ChcExpr::int(20), 8),
            ],
        );

        // Engine 2 (Kind): publish k-induction depth.
        bb.publish_hint(
            2,
            ProofHintKind::KInductionDepth {
                predicate: pred(0),
                depth: 4,
            },
        );

        // Engine 3 (PDR variant) consumes all channels.
        let lemma_provider = BlackboardHintProvider::new(bb.clone(), 3);
        let cex_consumer = CexConsumer::new(bb.clone(), 3);
        let hint_consumer = ProofHintConsumer::new(bb.clone(), 3);

        // Read lemmas.
        let mut lemma_out = Vec::new();
        let req = crate::lemma_hints::HintRequest::empty_for_test();
        lemma_provider.collect(&req, &mut lemma_out);
        assert_eq!(lemma_out.len(), 2); // From engine 1

        // Read CEX traces.
        let cex_out = cex_consumer.drain_new();
        assert_eq!(cex_out.len(), 1); // From engine 0

        // Read proof hints.
        let hint_out = hint_consumer.drain_new();
        assert_eq!(hint_out.len(), 2); // From engines 0 and 2

        // Verify counts.
        assert_eq!(bb.lemma_count(), 2);
        assert_eq!(bb.cex_count(), 1);
        assert_eq!(bb.hint_count(), 2);
    }

    #[test]
    fn test_multi_threaded_publish_and_consume() {
        use std::thread;

        let bb = SharedBlackboard::new();
        let bb_clone1 = bb.clone();
        let bb_clone2 = bb.clone();
        let bb_clone3 = bb.clone();

        // Spawn three producers in parallel.
        let h1 = thread::spawn(move || {
            for i in 0..10 {
                bb_clone1.publish(0, vec![(pred(0), ChcExpr::int(i), i as usize)]);
            }
        });

        let h2 = thread::spawn(move || {
            for i in 0..5 {
                bb_clone2.publish_cex(1, vec![pred(0)], vec![ChcExpr::int(i)], i as usize, false);
            }
        });

        let h3 = thread::spawn(move || {
            for i in 0..8 {
                bb_clone3.publish_hint(2, ProofHintKind::BmcSafeDepth { depth: i });
            }
        });

        h1.join().unwrap();
        h2.join().unwrap();
        h3.join().unwrap();

        // All items should be present.
        assert_eq!(bb.lemma_count(), 10);
        assert_eq!(bb.cex_count(), 5);
        assert_eq!(bb.hint_count(), 8);

        // Consumer (engine 3) sees everything except self-produced.
        let lemmas = bb.read_for(3);
        assert_eq!(lemmas.len(), 10);

        let cex = bb.read_cex_for(3);
        assert_eq!(cex.len(), 5);

        let hints = bb.read_hints_for(3);
        assert_eq!(hints.len(), 8);
    }
}
