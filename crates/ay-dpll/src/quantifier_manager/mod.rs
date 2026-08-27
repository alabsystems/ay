// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier Manager for persisting quantifier instantiation state across solver rounds.
//!
//! This module provides a unified interface for managing quantifier instantiation,
//! including generation tracking across E-matching rounds and deferred instantiations.
//!
//! # Architecture
//!
//! The `QuantifierManager` corresponds to Z3's `qi_queue` + `quantifier_manager`.
//! It persists state that must survive across `check_sat` calls:
//!
//! - `GenerationTracker`: tracks term generations to avoid redundant instantiations
//! - `deferred`: instantiations that exceeded the eager threshold but may be needed later
//!
//! # References
//!
//! - Z3: `reference/z3/src/smt/qi_queue.cpp`
//! - Design: the development design notes

use std::collections::VecDeque;

use crate::ematching::{
    perform_ematching_with_generations, DeferredInstantiation, DemandGate, DemandStats,
    EMatchingConfig, EMatchingResult, GenerationTracker, ParkedInstance, PersistentMatchState,
};
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{TermId, TermStore};
use ay_euf::EufModel;

/// Manages quantifier instantiation state across solver rounds.
///
/// This struct persists the generation tracker and deferred instantiations
/// that would otherwise be lost between E-matching calls.
///
/// # Phase A (#573)
///
/// Initial implementation: persist GenerationTracker across rounds so that:
/// - Generation tracking is not reset each call
/// - We can observe generation increments across rounds
/// - Foundation for later phases (B-E)
#[derive(Debug)]
pub(crate) struct QuantifierManager {
    /// Persisted generation tracker across rounds.
    ///
    /// Without persistence, each `perform_ematching()` call starts fresh,
    /// making generation-based cost filtering ineffective.
    generation_tracker: GenerationTracker,

    /// Deferred instantiations from previous rounds.
    ///
    /// Instantiations with cost > eager_threshold but <= lazy_threshold
    /// are collected here for later processing.
    ///
    /// Public to allow promote-unsat processing in executor (Phase D, #557).
    pub deferred: VecDeque<DeferredInstantiation>,

    /// Configuration for E-matching.
    config: EMatchingConfig,

    /// Round counter for debugging/profiling.
    round: usize,

    /// Saved states for push/pop incremental mode (#2844).
    /// Each entry stores the generation tracker and deferred queue at that scope level.
    scope_stack: Vec<QuantifierManagerSnapshot>,

    /// Persistent, incrementally-maintained E-matching state (index + assertion
    /// equality classes + cross-round instantiation memo). Replaces the per-round
    /// full rebuild of `TermIndex`/`EqualityClasses`/`seen` to cut the per-round
    /// O(rounds * terms) cost. See `ematching::PersistentMatchState` for the
    /// soundness invariants (LI-1..LI-10).
    match_state: PersistentMatchState,

    /// M0' demand-campaign instrumentation: pure-observation counters accumulated
    /// across this solve's E-matching rounds (per-family generation histograms +
    /// asserted/parked/blocked/budget-break tallies read off the cost gate). Reset
    /// per solve at [`Self::begin_epoch`]; surfaced under `quantifier.demand.*`.
    /// NEVER consulted by any solver decision — deleting it changes no verdict.
    demand_stats: DemandStats,

    /// M2+M3 demand lane (SHADOW-ONLY). Inert unless armed by
    /// [`Self::demand_arm`] (only the debug-gated shadow arm arms it). When armed,
    /// the E-matching cost gate PARKS over-frontier instances of frontier-gated
    /// families here (LAW #7) and the round driver flushes them on demand as the
    /// frontier bumps (LAW #1) / fences them before any conclusion (LAW #2). When
    /// NOT armed, `demand.active == false`, `run_ematching_round` passes `None` to
    /// the E-matcher and every field is untouched — production is byte-identical.
    demand: DemandLaneState,

    /// Relevance-ranked admission carry queue and observation counters.
    relevance: RelevanceState,
}

/// M2+M3 demand-lane state (SHADOW-ONLY). Persists the generation frontier `F`,
/// the parked-instance queue, the frontier-gated family set, and the DT
/// resume-depth across the E-matching rounds of a single solve.
#[derive(Clone, Debug, Default)]
pub(crate) struct DemandLaneState {
    /// Armed only by the debug-gated shadow arm. `false` ⇒ fully inert.
    pub active: bool,
    /// Generation frontier `F` (>= 1). Instances of a gated family at generation
    /// `<= F` are asserted; those `> F` are parked. Starts at 1, bumps on demand.
    pub frontier: u32,
    /// Raw ids (`TermId.0`) of the frontier-gated foralls (M1
    /// `SelfChainingDefinitional` / `BridgeCycle`).
    pub gated: HashSet<u32>,
    /// Parked over-frontier instances (LAW #7), retained with their generation.
    pub parked: VecDeque<ParkedInstance>,
    /// Persisted DT iterative-deepening resume depth (LAW #5): the demand arm
    /// resumes DT deepening from here instead of restarting at the warm-start
    /// depth each demand round.
    pub dt_resume_depth: usize,
    /// Count of frontier bumps + under-frontier flushes performed (LAW #1).
    pub flushes: u64,
    /// Count of fence drains performed (LAW #2).
    pub fence_drains: u64,
    /// Total instances parked over the solve (surfaced under
    /// `quantifier.demand.frontier_parked`).
    pub total_parked: u64,
    /// Total parked instances asserted by a flush/fence.
    pub total_flushed: u64,
    /// M4 (A0 no-drop conservation oracle): total gated-family bindings that
    /// reached the cost gate over the solve.
    pub total_gated_bindings: u64,
    /// M4 (A0 no-drop conservation oracle): total gated-family bindings that were
    /// NOT parked (generation `<= F`, passed to the normal path). The invariant
    /// `total_gated_bindings == total_parked + total_gated_passed` holds across the
    /// whole solve (no gated binding is silently dropped).
    pub total_gated_passed: u64,
    /// M4 (LAW #2 hardening): count of fence grant-only-flush seen-frame resets
    /// performed (a fresh seen frame so a parked binding re-encountered post-fence
    /// re-asserts).
    pub fence_seen_resets: u64,
}

/// Snapshot of QuantifierManager state saved on push (#2844).
#[derive(Clone, Debug)]
struct QuantifierManagerSnapshot {
    generation_tracker: GenerationTracker,
    deferred_len: usize,
    round: usize,
    /// High-water mark of the persistent seen memo's insertion log. On pop, the
    /// memo is drained back to this length and the drained keys removed from the
    /// seen set (LI-3), mirroring `deferred.truncate(deferred_len)`. This is the
    /// false-result-critical field: a (quant,binding) produced only inside the
    /// popped scope MUST be forgotten so a sibling/parent re-derives it.
    seen_order_len: usize,
    /// High-water mark of the incremental-matching epoch instantiated-set's
    /// insertion log. On pop, that set is drained back to this length so a
    /// quantifier marked instantiated only inside the popped scope is forgotten
    /// (mirrors `seen_order_len`; LI-INC-3 scope-pop guard). Belongs to no live
    /// epoch after a cross-epoch pop, so truncating it back is always safe.
    instantiated_order_len: usize,
    /// Snapshot of the persisted assertion-only equality classes (LI-7/LI-8) so
    /// an inner scope's unions do not leak into a sibling/parent on pop.
    assertion_eqclasses: crate::ematching::EqualityClasses,
    /// Snapshot of the folded equality-atom TermId set, restored alongside the
    /// eqclasses so re-entering a sibling scope re-folds correctly.
    folded_eq_atoms: ay_core::kani_compat::DetHashSet<u32>,
}

impl Default for QuantifierManager {
    fn default() -> Self {
        Self::new()
    }
}

impl QuantifierManager {
    /// Create a new quantifier manager with default configuration.
    pub(crate) fn new() -> Self {
        Self::with_config(EMatchingConfig::default())
    }

    /// Create a quantifier manager with custom configuration.
    pub(crate) fn with_config(config: EMatchingConfig) -> Self {
        Self {
            generation_tracker: GenerationTracker::new(),
            deferred: VecDeque::new(),
            config,
            round: 0,
            scope_stack: Vec::new(),
            match_state: PersistentMatchState::new(),
            demand_stats: DemandStats::default(),
            demand: DemandLaneState::default(),
            relevance: RelevanceState::default(),
        }
    }

    /// Begin a new `process_quantifiers` epoch (LI-4). Drains the persistent
    /// instantiation memo back to the current scope baseline so that any
    /// (quantifier, binding) produced in a PRIOR check-sat — whose instance
    /// `restore_assertions` has since retracted — is re-instantiable in this
    /// check-sat. Called at the TOP of `run_ematching_rounds`, before the round
    /// loop. The index and assertion eqclasses are monotone-safe and are NOT
    /// reset here.
    ///
    /// The baseline is the deepest live scope snapshot's `seen_order_len` (so an
    /// epoch starting inside a pushed scope never forgets that scope's parents),
    /// or 0 at base scope.
    pub(crate) fn begin_epoch(&mut self) {
        let baseline = self
            .scope_stack
            .last()
            .map_or(0, |snap| snap.seen_order_len);
        self.match_state.begin_epoch(baseline);
        // M0': reset the demand-instrumentation accumulator per solve. `begin_epoch`
        // is called ONCE per `process_quantifiers` (top of `run_ematching_rounds`),
        // so the surfaced `quantifier.demand.*` counters describe exactly the
        // current check-sat's E-matching activity — matching the per-solve
        // convention of `ematching_rounds_completed`. Pure observation; a reset
        // here can never change a verdict.
        self.demand_stats = DemandStats::default();
        // M2+M3: reset the demand lane to inert per solve. The executor's shadow
        // arm RE-ARMS it (via `demand_arm`) immediately after this call when the
        // shadow flag is set; a non-shadow solve leaves it inert (byte-identical).
        self.demand = DemandLaneState::default();
        self.relevance_begin_epoch();
    }

    /// Begin a fresh round group WITHIN the current epoch. Resets only the index
    /// and assertion eqclasses (the seen memo persists across the whole
    /// `process_quantifiers`). Called by the single-round post-CEGQI and
    /// interleaved-refinement passes, whose slices are freshly re-cloned from
    /// `ctx.assertions` and may not extend the main loop's slice.
    pub(crate) fn begin_round_group(&mut self) {
        self.match_state.begin_round_group();
    }

    /// Run one round of E-matching with the persisted generation tracker.
    ///
    /// Returns the E-matching result with instantiations and updated state.
    ///
    /// # Phase A behavior
    ///
    /// This phase simply persists the tracker across calls. Later phases will:
    /// - B: Process deferred instantiations
    /// - C: Skip satisfied instantiations
    /// - D: Promote conflict-inducing instantiations
    ///
    /// `should_stop` is polled inside the E-matching binding loop so an
    /// executor wall-clock deadline or interrupt can break a long round before
    /// it materializes its full instantiation budget. On stop the round reports
    /// `reached_limit = true`, which callers route to `Unknown` (never `Sat`).
    pub(crate) fn run_ematching_round(
        &mut self,
        terms: &mut TermStore,
        assertions: &[TermId],
        euf_model: Option<&EufModel>,
        should_stop: &dyn Fn() -> bool,
    ) -> EMatchingResult {
        self.round += 1;

        // M2+M3 demand lane (SHADOW-ONLY): build the per-round frontier gate ONLY
        // when the lane is armed. On every production path `self.demand.active` is
        // false and `gate` stays `None`, so the E-matcher is called exactly as
        // before — byte-identical.
        let mut parked_this_round: Vec<ParkedInstance> = Vec::new();
        let mut gate = if self.demand.active {
            Some(DemandGate {
                frontier: self.demand.frontier,
                gated: &self.demand.gated,
                parked: &mut parked_this_round,
                frontier_parked: 0,
                max_gated_gen: 0,
                gated_bindings: 0,
                gated_passed: 0,
            })
        } else {
            None
        };

        // Perform E-matching with our persisted tracker.
        // Pass EUF model from a previous solve for congruence-aware matching (#3325 B1b).
        // The persistent match state is incrementally updated (index/eqclasses/seen
        // memo) instead of rebuilt per round.
        let result = perform_ematching_with_generations(
            terms,
            assertions,
            &self.config,
            // Clone the tracker so we can update it after
            self.generation_tracker.clone(),
            euf_model,
            should_stop,
            &mut self.match_state,
            gate.as_mut(),
        );

        // Demand lane: move this round's parked instances into the persistent
        // queue and tally them. `gate` borrowed `self.demand.gated`, so it must be
        // dropped before we mutate `self.demand`.
        let frontier_parked = gate.as_ref().map_or(0, |g| g.frontier_parked);
        let max_gated_gen = gate.as_ref().map_or(0, |g| g.max_gated_gen);
        let gated_bindings = gate.as_ref().map_or(0, |g| g.gated_bindings);
        let gated_passed = gate.as_ref().map_or(0, |g| g.gated_passed);
        let _ = gate;
        if self.demand.active {
            // M4 (A0 no-drop conservation oracle): every gated-family binding the
            // gate saw this round is EITHER parked (LAW #7) OR passed to the normal
            // path — never silently dropped. This is the debug-assert half of the
            // "no relevant instance dropped" oracle (the corpus test is the other
            // half). SHADOW-ONLY (only runs when the lane is armed).
            debug_assert_eq!(
                gated_bindings,
                frontier_parked + gated_passed,
                "M4 A0 conservation: a gated binding was neither parked nor passed \
                 (silent drop) — parked={frontier_parked} passed={gated_passed} \
                 total={gated_bindings}"
            );
            self.demand.total_parked += frontier_parked;
            self.demand.total_gated_bindings += gated_bindings;
            self.demand.total_gated_passed += gated_passed;
            for p in parked_this_round.drain(..) {
                self.demand.parked.push_back(p);
            }
            if ay_core::misc_cli_flags().demand_debug {
                eprintln!(
                    "c demand-round F={} gated_bindings={gated_bindings} gated_passed={gated_passed} max_gated_gen={max_gated_gen} parked_this_round={frontier_parked}",
                    self.demand.frontier,
                );
            }
        }

        // Persist the updated tracker for next round
        self.generation_tracker = result.generation_tracker.clone();

        // M0': fold this round's demand-instrumentation delta into the per-solve
        // accumulator. Pure observation — the merged counters are never read back
        // into any instantiation/verdict decision.
        self.demand_stats.merge(&result.demand);

        // Collect deferred instantiations (Phase B will process these)
        for def in &result.deferred {
            self.deferred.push_back(def.clone());
        }

        result
    }

    // ---- M2+M3 demand lane (SHADOW-ONLY) --------------------------------------

    /// Arm the demand lane for THIS solve with the frontier-gated family set
    /// (`gated` = raw ids of the M1 self-chaining / bridge-cycle foralls). Sets
    /// `F = 1` and clears the parked queue. Called by the executor's shadow arm
    /// AFTER `begin_epoch` (which resets the lane to inert), so a non-shadow solve
    /// never arms it. `dt_resume_depth` starts at the warm-start depth.
    pub(crate) fn demand_arm(&mut self, gated: HashSet<u32>, warm_start_depth: usize) {
        self.demand.active = true;
        self.demand.frontier = 1;
        self.demand.gated = gated;
        self.demand.parked.clear();
        self.demand.dt_resume_depth = warm_start_depth;
    }

    /// Whether the demand lane is armed for this solve.
    pub(crate) fn demand_active(&self) -> bool {
        self.demand.active
    }

    /// Current generation frontier `F`.
    pub(crate) fn demand_frontier(&self) -> u32 {
        self.demand.frontier
    }

    /// Whether any instances are parked (over-frontier, awaiting flush).
    pub(crate) fn demand_has_parked(&self) -> bool {
        !self.demand.parked.is_empty()
    }

    /// Persisted DT iterative-deepening resume depth (LAW #5).
    pub(crate) fn demand_dt_resume_depth(&self) -> usize {
        self.demand.dt_resume_depth
    }

    /// Record the DT deepening depth reached this demand round so the NEXT round
    /// resumes there instead of restarting at the warm-start depth (LAW #5). Never
    /// decreases the persisted depth.
    pub(crate) fn demand_set_dt_resume_depth(&mut self, depth: usize) {
        if depth > self.demand.dt_resume_depth {
            self.demand.dt_resume_depth = depth;
        }
    }

    /// LAW #1 — UNCONDITIONAL under-frontier flush. Bump `F` by one, then drain
    /// EVERY parked instance whose generation `<= F` (never suppressed by any
    /// model filter — a model may only ORDER, never drop, per the
    /// parking-fixpoint trap), instantiate + generation-tag each, and return the
    /// ground instance TermIds for the caller to assert. Instances still over the
    /// new frontier stay parked.
    pub(crate) fn demand_flush_under_frontier(&mut self, terms: &mut TermStore) -> Vec<TermId> {
        self.demand.frontier = self.demand.frontier.saturating_add(1);
        self.demand.flushes += 1;
        let f = self.demand.frontier;
        let mut out = Vec::new();
        let mut remaining: VecDeque<ParkedInstance> = VecDeque::new();
        while let Some(p) = self.demand.parked.pop_front() {
            if p.generation <= f {
                if let Some(inst) = p.instantiate_and_tag(terms, &mut self.generation_tracker) {
                    out.push(inst);
                    self.demand.total_flushed += 1;
                }
            } else {
                remaining.push_back(p);
            }
        }
        self.demand.parked = remaining;
        out
    }

    /// LAW #2 — FENCE drain (M4-hardened: direct parked-queue drain). Before any
    /// Sat/Unknown conclusion with parked instances remaining, drain the ENTIRE
    /// parked queue directly (regardless of frontier — bypassing model-admission
    /// ORDERING), instantiate + generation-tag each, and return the ground instance
    /// TermIds for the caller to assert.
    ///
    /// M4 (direct parked-queue drain, three disciplines):
    ///  1. BYPASS MODEL-ADMISSION ORDERING: the whole queue is drained
    ///     unconditionally — no model filter may reorder or withhold (the
    ///     parking-fixpoint trap: individually-model-consistent bridge instances
    ///     whose JOINT contradiction is the refutation).
    ///  2. BYPASS THE E-MATCHING SEEN-MEMO: the instances were already produced at
    ///     park time, so they are re-asserted VERBATIM (not re-derived through the
    ///     matcher / seen gate).
    ///  3. FRESH SEEN FRAME: after draining, the E-matching seen frame is reset to
    ///     the epoch baseline (via [`Self::demand_reset_seen_frame`]) so a parked
    ///     binding RE-ENCOUNTERED post-fence (by a subsequent interleave round) is
    ///     NOT suppressed by the memo — it re-asserts. Sound: resetting the seen
    ///     memo can only cause RE-derivation (more instances), never fewer, so it
    ///     can never manufacture a false UNSAT, and a still-parked/deferred state
    ///     keeps `has_deferred` true (no false SAT).
    ///
    /// The direct drain uses NO E-matching budget (`EMatchingConfig`) — it is a
    /// verbatim re-assert, so the per-quantifier / max-total caps that gate the
    /// matcher do not apply; the fence is a FRESH, unbudgeted grant of every parked
    /// instance.
    pub(crate) fn demand_fence_drain(&mut self, terms: &mut TermStore) -> Vec<TermId> {
        if self.demand.parked.is_empty() {
            return Vec::new();
        }
        self.demand.fence_drains += 1;
        let mut out = Vec::new();
        while let Some(p) = self.demand.parked.pop_front() {
            if let Some(inst) = p.instantiate_and_tag(terms, &mut self.generation_tracker) {
                out.push(inst);
                self.demand.total_flushed += 1;
            }
        }
        // M4 (discipline #3): fresh seen frame so a re-encountered parked binding
        // re-asserts post-fence rather than being memo-suppressed.
        self.demand_reset_seen_frame();
        out
    }

    /// M4 (LAW #2 discipline #3): reset the E-matching seen frame to the epoch
    /// baseline, giving a FRESH seen frame within the solve. A (quantifier, binding)
    /// seen this epoch is forgotten, so a post-fence interleave round re-derives —
    /// and re-asserts — it instead of skipping it as a duplicate. SHADOW-ONLY: only
    /// called from the fence drain, which only runs when the lane is armed; a
    /// non-empty parked queue is a shadow-arm-only state.
    pub(crate) fn demand_reset_seen_frame(&mut self) {
        self.demand.fence_seen_resets += 1;
        self.match_state.reset_seen_frame();
    }

    /// LAW #4 (DT-emitter charge-AND-tag, SHADOW-ONLY): tag every term the DT
    /// selector emitter minted in `[from, to)` that is still generation-0 with
    /// `gen`, so a subsequent interleave E-matching round cannot re-enter the
    /// frontier gate with a LAUNDERED gen-0 DT-minted selector term (the DT
    /// emitter's gen-0 laundering hole, the campaign's second minter). No-op unless
    /// the lane is armed — production DT solving is unaffected. Returns the count of
    /// terms newly tagged (0 when inert).
    pub(crate) fn demand_tag_dt_minted(
        &mut self,
        from: usize,
        to: usize,
        generation: u32,
    ) -> usize {
        if !self.demand.active || generation == 0 {
            return 0;
        }
        let mut tagged = 0;
        for idx in from..to {
            debug_assert!(u32::try_from(idx).is_ok(), "term id overflow");
            let t = TermId::new(idx as u32);
            if self.generation_tracker.get(t) == 0 {
                self.generation_tracker.set(t, generation);
                tagged += 1;
            }
        }
        tagged
    }

    /// Surface the demand-lane counters under `quantifier.demand.*` (pure output).
    pub(crate) fn demand_write_statistics(&self, stats: &mut crate::Statistics) {
        if !self.demand.active {
            return;
        }
        stats.set_int(
            "quantifier.demand.frontier",
            u64::from(self.demand.frontier),
        );
        stats.set_int(
            "quantifier.demand.frontier_parked",
            self.demand.total_parked,
        );
        stats.set_int("quantifier.demand.flushed", self.demand.total_flushed);
        stats.set_int("quantifier.demand.flushes", self.demand.flushes);
        stats.set_int("quantifier.demand.fence_drains", self.demand.fence_drains);
        stats.set_int(
            "quantifier.demand.parked_remaining",
            self.demand.parked.len() as u64,
        );
        stats.set_int(
            "quantifier.demand.gated_families",
            self.demand.gated.len() as u64,
        );
        stats.set_int(
            "quantifier.demand.dt_resume_depth",
            self.demand.dt_resume_depth as u64,
        );
        // M4 (A0 no-drop conservation oracle): the gated-binding partition + the
        // fence seen-frame reset count. `gated_bindings == frontier_parked +
        // gated_passed` is the no-silent-drop invariant.
        stats.set_int(
            "quantifier.demand.gated_bindings",
            self.demand.total_gated_bindings,
        );
        stats.set_int(
            "quantifier.demand.gated_passed",
            self.demand.total_gated_passed,
        );
        stats.set_int(
            "quantifier.demand.fence_seen_resets",
            self.demand.fence_seen_resets,
        );
    }

    /// Clone this solve's accumulated M0' demand-instrumentation counters so the
    /// executor can surface them into `Statistics` under `quantifier.demand.*`
    /// (the borrow of `self` ends when the clone is returned, freeing the
    /// executor's `last_statistics` for a mutable borrow). Pure observation.
    pub(crate) fn demand_stats_clone(&self) -> DemandStats {
        self.demand_stats.clone()
    }
}

impl crate::incremental_state::IncrementalSubsystem for QuantifierManager {
    /// Save current state for incremental push (#2844).
    ///
    /// Captures the generation tracker, deferred queue length, and round counter
    /// so they can be restored on pop. This prevents state from inner scopes
    /// leaking into outer scopes after pop.
    fn push(&mut self) {
        self.relevance_clear_carried_at_scope_boundary();
        let (assertion_eqclasses, folded_eq_atoms) = self.match_state.snapshot_eqclasses();
        self.scope_stack.push(QuantifierManagerSnapshot {
            generation_tracker: self.generation_tracker.clone(),
            deferred_len: self.deferred.len(),
            round: self.round,
            // LI-3: record the seen-memo high-water mark so pop forgets exactly
            // the (quant,binding) keys produced inside this scope.
            seen_order_len: self.match_state.seen_order_len(),
            // LI-INC-3: record the incremental-matching instantiated-set mark so pop
            // forgets exactly the quantifiers marked instantiated inside this scope.
            instantiated_order_len: self.match_state.instantiated_order_len(),
            assertion_eqclasses,
            folded_eq_atoms,
        });
    }

    /// Restore state from before the matching push (#2844).
    ///
    /// Discards generation tracker entries and deferred instantiations
    /// accumulated in the popped scope. Returns false on underflow.
    fn pop(&mut self) -> bool {
        if let Some(snapshot) = self.scope_stack.pop() {
            self.relevance_clear_carried_at_scope_boundary();
            self.generation_tracker = snapshot.generation_tracker;
            self.deferred.truncate(snapshot.deferred_len);
            self.round = snapshot.round;
            // LI-3 (the false-result-critical step): drain the seen memo back to
            // the high-water mark recorded at push, so a (quant,binding) produced
            // only inside the popped scope is forgotten and a sibling/parent scope
            // re-derives it. Mirrors `deferred.truncate(deferred_len)` above. A
            // stale seen across pop is the ONLY false-UNSAT/false-SAT vector.
            self.match_state.truncate_seen_to(snapshot.seen_order_len);
            // LI-INC-3: drain the incremental-matching epoch instantiated-set back
            // to its push-time mark, mirroring the seen-memo truncation, so a
            // quantifier marked instantiated only inside the popped scope cannot
            // leak its "already instantiated" status into a sibling/parent epoch.
            // (The new-candidate watermark self-heals on pop via the eqclass
            // fingerprint, which changes when `restore_eqclasses` runs below.)
            self.match_state
                .truncate_instantiated_to(snapshot.instantiated_order_len);
            // LI-INC-2 scope-pop guard: invalidate the new-candidate watermark. A
            // pop can retract ground candidates; the eqclass-fingerprint guard does
            // NOT catch this when the partition is unchanged (e.g. empty), so the
            // watermark must be cleared unconditionally here so re-added candidates
            // are re-matched (the only stale-memo-across-pop vector).
            self.match_state.invalidate_match_watermark_on_pop();
            // LI-7/LI-8: restore the assertion-only eqclasses + folded-atom set so
            // an inner scope's unions do not leak into a sibling/parent. The index
            // is monotone-safe and intentionally NOT restored.
            self.match_state
                .restore_eqclasses(snapshot.assertion_eqclasses, snapshot.folded_eq_atoms);
            true
        } else {
            false
        }
    }

    /// Reset all state (for `(reset)` command).
    fn reset(&mut self) {
        self.generation_tracker = GenerationTracker::new();
        self.deferred.clear();
        self.round = 0;
        self.scope_stack.clear();
        // F6: clear ALL persistent match state so a `(reset)` cannot leave stale
        // TermIds that would alias different terms after the store is also reset.
        self.match_state.clear();
        // M0': clear the pure-observation demand counters too (tidy; a stale value
        // here can never affect a verdict).
        self.demand_stats = DemandStats::default();
        self.demand = DemandLaneState::default();
        self.relevance_reset();
    }
}

#[cfg(test)]
impl QuantifierManager {
    pub(crate) fn deferred_count(&self) -> usize {
        self.deferred.len()
    }

    pub(crate) fn round(&self) -> usize {
        self.round
    }

    pub(crate) fn generation_tracker(&self) -> &GenerationTracker {
        &self.generation_tracker
    }

    pub(crate) fn clear(&mut self) {
        self.generation_tracker = GenerationTracker::new();
        self.deferred.clear();
        self.round = 0;
        self.scope_stack.clear();
        self.match_state.clear();
        self.demand_stats = DemandStats::default();
        self.demand = DemandLaneState::default();
        self.relevance_reset();
    }

    /// Number of (quantifier, binding) keys in the persistent instantiation memo.
    pub(crate) fn seen_len(&self) -> usize {
        self.match_state.seen_len()
    }

    /// Length of the persistent instantiation memo's insertion log (must equal
    /// `seen_len()`).
    pub(crate) fn seen_order_len(&self) -> usize {
        self.match_state.seen_order_len()
    }

    // ---- M4 demand-lane unit-test helpers (SHADOW-ONLY paths) ----

    /// Inject a parked instance directly (simulating the E-matching cost gate's
    /// LAW #7 park), for the fence/discipline unit tests.
    pub(crate) fn demand_park_for_test(
        &mut self,
        quantifier: TermId,
        binding: Vec<TermId>,
        var_names: Vec<String>,
        generation: u32,
        head: String,
    ) {
        self.demand.parked.push_back(ParkedInstance {
            quantifier,
            binding,
            var_names,
            generation,
            head,
        });
        self.demand.total_parked += 1;
    }

    /// Insert a `(quantifier, binding)` into the E-matching seen memo (simulating
    /// the seen-insert the park path performs), for the fence re-assert test.
    /// Returns whether it was newly inserted.
    pub(crate) fn demand_seen_insert_for_test(
        &mut self,
        quantifier: TermId,
        binding: Vec<TermId>,
    ) -> bool {
        self.match_state.seen_insert((quantifier, binding))
    }

    /// Number of instances still parked (over the frontier, not yet flushed).
    pub(crate) fn demand_parked_len(&self) -> usize {
        self.demand.parked.len()
    }
}

mod relevance;
#[cfg(test)]
mod tests;
use relevance::RelevanceState;
