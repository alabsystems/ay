// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver state layout: hot/cold field separation for BCP cache locality (#5090).
//!
//! Field order is significant: `#[repr(C)]` locks the memory layout so
//! BCP-hot fields occupy the first cache lines of the struct. Hot fields
//! are grouped first, warm fields next, cold fields last.
//! See `cold.rs` for the full field classification.

use super::*;

/// The CDCL SAT solver.
///
/// `#[repr(C)]` ensures deterministic field layout for cache locality (#5090).
/// BCP-hot fields are first so they occupy the initial cache lines.
#[repr(C)]
pub struct Solver {
    // ══════════════════════════════════════════════════════════════════════
    // HOT: BCP inner loop (accessed every propagation)
    // ══════════════════════════════════════════════════════════════════════
    /// Literal values indexed by literal index (CaDiCaL-style).
    /// `vals[lit.index()]` is 1 (true), -1 (false), or 0 (unassigned).
    /// Sole source of truth for assignment state (#3758 Phase 3).
    pub(super) vals: Vec<i8>,
    /// Watched literal lists
    pub(super) watches: WatchedLists,
    /// Unified inline clause arena (CaDiCaL-style, #3904).
    /// Contiguous header+literal storage for single-cache-line BCP.
    pub(super) arena: ClauseArena,
    /// Trail (sequence of assigned literals)
    pub(super) trail: Vec<Literal>,
    /// Trail limit for each decision level (index into trail)
    pub(super) trail_lim: Vec<usize>,
    /// Propagation queue head (index into trail)
    pub(super) qhead: usize,
    /// Current decision level
    pub(super) decision_level: u32,
    /// Per-variable AoS data: level + trail_pos + reason packed in 16 bytes.
    /// CaDiCaL-style: 4 variables per cache line for conflict analysis locality.
    /// Replaces separate `level`, `reason`, `trail_pos` arrays (#5090).
    pub(super) var_data: Vec<VarData>,
    /// Phase saving: last polarity of each variable.
    /// Encoding: 1 = positive, -1 = negative, 0 = unset.
    /// Kissat-style i8 avoids Option matching overhead in the hot path.
    /// Placed in HOT section (#8044): written on every propagation
    /// (`enqueue` saves phase), read on every decision (`pick_phase`).
    pub(super) phase: Vec<i8>,
    /// Whether chronological backtracking is enabled.
    /// Moved to HOT section (#9160): checked on every propagation in
    /// `enqueue_bcp` and `enqueue_bcp_binary` to compute assignment level.
    /// Previously in WARM section, costing an extra cache-line load per
    /// propagation on large formulas where the hot section spans >1 line.
    pub(super) chrono_enabled: bool,
    /// Whether ghost literal guards are needed in conflict analysis (#8466, #8489).
    /// Ghost literals are unassigned variables with stale var_data.level values.
    ///
    /// Two sources of ghost literals:
    /// 1. **Chronological backtracking**: chrono-BT only fires when
    ///    decision_level - jump_level > CHRONO_LEVEL_LIMIT, requiring
    ///    num_vars > CHRONO_LEVEL_LIMIT.
    /// 2. **Incremental mode (push/pop)**: after pop(), variables from the
    ///    popped scope retain stale var_data entries. Between solves,
    ///    reset_search_state() unassigns non-level-0 variables, creating
    ///    ghost literals in clauses that reference those variables (#8489).
    ///
    /// The guard is enabled when EITHER condition can produce ghosts:
    /// `num_vars > CHRONO_LEVEL_LIMIT || has_ever_scoped`.
    pub(super) ghost_guard_needed: bool,
    /// LSCB lambda vector (#8442): per-variable MLI (Missed Lower Implication)
    /// clause reference. When BCP discovers that an already-satisfied literal
    /// could be reimplied at a lower level by a clause, that clause is stored
    /// here. Used during backtracking for lazy reimplication and during
    /// conflict analysis as a preferred (lower-level) reason.
    /// Reference: Coutelier, Fleury, Kovacs "Lazy Reimplication in
    /// Chronological Backtracking" (SAT 2024, arXiv:2501.07457).
    /// Placed in WARM section: accessed during BCP replacement scan (not the
    /// hottest blocker fast path) and during backtracking/conflict analysis.
    pub(super) lambda: Vec<Option<ClauseRef>>,
    /// When true, enqueue() skips phase saving. Set during vivification
    /// and lucky phase probing where decisions are artificial.
    /// CaDiCaL: `searching_lucky_phases` (internal.hpp).
    /// Placed in HOT section (#8044): checked on every propagation.
    pub(super) suppress_phase_saving: bool,
    /// Reusable SoA buffer for deferred watchers during propagation
    pub(super) deferred_watch_list: WatchList,
    /// Deferred replacement watches: (target_literal, watcher) pairs collected
    /// during BCP when a long clause finds an unassigned replacement literal.
    /// Instead of immediately adding the new watch to the replacement literal's
    /// watch list (which pollutes the cache during the hot BCP scan), entries
    /// are buffered here and flushed after the current literal's watch list
    /// processing completes. Kissat proplit.h pattern (#8041).
    pub(super) deferred_replacement_watches: Vec<(Literal, Watcher)>,
    /// Number of variables
    pub(super) num_vars: usize,
    /// Number of user-visible variables (excludes internal scope selectors)
    pub(super) user_num_vars: usize,
    /// Whether an empty clause has been added (formula is UNSAT)
    pub(super) has_empty_clause: bool,
    /// Statistics: number of propagations
    pub(super) num_propagations: u64,
    pub(super) no_conflict_until: usize,
    /// Search ticks per mode [0=focused, 1=stable]. Counts cache-line work in BCP.
    /// CaDiCaL restart.cpp:27, propagate.cpp:473.
    pub(super) search_ticks: [u64; 2],
    /// Whether we're in stable mode (infrequent restarts) vs focused mode (frequent restarts)
    pub(super) stable_mode: bool,
    /// Heuristic currently driving branch-variable selection.
    pub(super) active_branch_heuristic: BranchHeuristic,
    /// Whether we're currently in probing mode (level 1 propagation)
    pub(super) probing_mode: bool,
    /// Cached identity for the most recent propagation conflict.
    /// LRAT hint collection consults this instead of scanning the whole arena
    /// when the immediate `ClauseRef -> clause_id` mapping is unavailable.
    /// The ref gates the cache so stale IDs are never reused across conflicts.
    pub(super) last_conflict_clause_ref: Option<ClauseRef>,
    pub(super) last_conflict_clause_id: u64,
    // ══════════════════════════════════════════════════════════════════════
    // WARM: per-conflict / per-decision
    // ══════════════════════════════════════════════════════════════════════
    /// Total number of conflicts (for clause deletion scheduling)
    pub(super) num_conflicts: u64,
    /// Number of conflicts since last restart
    pub(super) conflicts_since_restart: u64,
    /// Statistics: number of decisions
    pub(super) num_decisions: u64,
    /// Variable selection heuristic
    pub(super) vsids: VSIDS,
    /// Conflict analyzer
    pub(super) conflict: ConflictAnalyzer,
    /// Target phases: phases at longest conflict-free trail (for stable mode).
    /// Encoding: 1 = positive, -1 = negative, 0 = unset.
    pub(super) target_phase: Vec<i8>,
    /// Best phases: best assignment seen (for rephasing).
    /// Encoding: 1 = positive, -1 = negative, 0 = unset.
    pub(super) best_phase: Vec<i8>,
    /// Trail length when target phases were saved
    pub(super) target_trail_len: usize,
    /// Trail length when best phases were saved
    pub(super) best_trail_len: usize,
    /// When true, `should_reduce_db()` returns false. Set during backbone
    /// probing to prevent clause deletion from invalidating the DRAT proof
    /// chain for backbone units (#7929). Without this, `reduce_db` can
    /// delete learned clauses from the probe that the backbone unit's RUP
    /// derivation depends on.
    pub(super) suppress_reduce_db: bool,
    // suppress_otfs removed (#8439): OTFS no longer clears the pivot's
    // reason pointer, so it is safe during backbone probing. The root cause
    // of #8356 (trail exhaustion) was setting reason=NO_REASON after OTFS
    // strengthening — now the reason pointer is preserved.
    /// Proof mediator (optional, supports DRAT and LRAT outputs).
    pub(super) proof_manager: Option<ProofManager>,
    /// Snapshot of proof mode at solve entry, for debug stability assertions.
    #[cfg(debug_assertions)]
    pub(super) solve_proof_mode: Option<bool>,
    /// Whether to use trail reuse heuristic for chrono BT (CaDiCaL-style)
    pub(super) chrono_reuse_trail: bool,
    /// Pure telemetry counters (write-only from hot paths, read for stats display).
    pub(crate) stats: solver_stats::SolverStats,
    /// Number of original (non-learned) clauses
    pub(super) num_original_clauses: usize,
    /// Number of units derived at level 0 (for propfixed tracking)
    pub(super) fixed_count: i64,
    /// Proof clause ID for inprocessing-derived units that have no `ClauseRef` reason.
    /// Indexed by `var.index()`. 0 means no provenance. Set when `emit_add` returns
    /// a proof clause ID but the unit is enqueued with `reason=None` (#4611).
    pub(super) unit_proof_id: Vec<u64>,
    /// Signed literal proven by `unit_proof_id`; 0 means no signed provenance.
    pub(super) unit_proof_sign: Vec<i8>,
    /// Proof-manager IDs for queued theory units when they differ from the
    /// arena clause ID (notably hidden LRAT `TrustedTransform` additions).
    ///
    /// Entries survive the queue pop because unit installation happens in the
    /// subsequent conflict-analysis step. They are consumed when the unit is
    /// installed or discarded with stale queued work.
    pub(super) pending_theory_unit_proof_ids: Vec<(ClauseRef, u64)>,
    /// Clause-indexed reason markers (epoch-stamped, avoids per-pass bool allocations).
    pub(super) reason_clause_marks: Vec<u32>,
    /// Current epoch for `reason_clause_marks`.
    pub(super) reason_clause_epoch: u32,
    /// Set when reason marks need a full trail rebuild (#8100, #8569).
    ///
    /// BCP enqueue functions do NOT incrementally mark reasons (#8569):
    /// backtrack always invalidates marks before any consumer reads them,
    /// so BCP marks were wasted writes. This flag is set by backtrack and
    /// mass-invalidation events (arena GC, incremental clause deletion,
    /// inprocessing). Consumers call `ensure_reason_clause_marks_current()`
    /// which rebuilds marks from the trail in O(trail_len) when needed.
    pub(super) reason_marks_invalidated: bool,
    /// Persistent `(old bump order, variable index)` pair buffer for VMTF
    /// conflict bump sorting (reused across conflicts; CaDiCaL analyze.cpp:189).
    /// Caching the order avoids repeated `Vsids::bump_order` lookups during
    /// comparator calls; the sorted pairs are consumed directly by
    /// `batch_bump_queue_sorted` (instruction-shave #4).
    pub(super) bump_order_sort_buf: Vec<(u64, usize)>,
    /// Persistent seen buffer for backbone analysis (reused across per-conflict calls).
    /// Eliminates per-call vec![false; num_vars] allocation in backbone_analyze_binary.
    /// CaDiCaL backbone.cpp:202-254 uses a persistent marks array.
    pub(super) backbone_seen: Vec<bool>,
    /// Persistent seen buffer for vivify backward analysis (reused across calls).
    /// Eliminates per-call `vec![false; num_vars]` allocation in
    /// `vivify_analyze_conflict` and `vivify_analyze_implied_literal` (#8543).
    /// Uses sparse cleanup via `vivify_analyzed_to_clear`.
    pub(super) vivify_analyzed: Vec<bool>,
    /// Sparse cleanup list for `vivify_analyzed`: indices that were set to `true`.
    pub(super) vivify_analyzed_to_clear: Vec<usize>,
    // Glue recomputation (CaDiCaL-style, analyze.cpp:206-240)
    pub(super) glue_stamp: Vec<u32>,
    pub(super) glue_stamp_counter: u32,
    // Block-level clause shrinking (CaDiCaL-style, shrink.cpp)
    pub(super) shrink_stamp: Vec<u32>,
    pub(super) shrink_stamp_counter: u32,
    pub(super) shrink_enabled: bool,
    pub(super) reap: reap::Reap,
    // Workspace vectors for per-conflict shrink allocations (reused via take/return)
    pub(super) ws_shrink_entries: Vec<(u32, usize, usize)>,
    pub(super) ws_shrink_result: Vec<Literal>,
    pub(super) ws_shrink_block_lits: Vec<Literal>,
    pub(super) ws_shrink_chain: Vec<u64>,
    pub(crate) tiers: tier_state::TierState,
    pub(crate) min: minimization_state::MinimizationState,
    pub(crate) phase_init: phase_init_state::PhaseInitState,
    /// FIFO queue of theory conflicts and mandatory unit work detected by
    /// `add_theory_lemma` at decision level > 0. All-false watched clauses
    /// have no future watch event, while unit axioms must be installed at root
    /// before a later backtrack can erase them (#6262).
    ///
    /// This must be a queue, not a single slot: a theory callback may add a
    /// batch of simultaneously conflicting lemmas before the CDCL loop gets a
    /// chance to consume any of them. Overwriting an `Option` silently dropped
    /// every conflict except the last one and allowed search to continue on a
    /// conflict-laden trail. Each queued clause is revalidated when popped, so
    /// conflicts made stale by an earlier backtrack are still discarded.
    pub(super) pending_theory_conflicts: std::collections::VecDeque<ClauseRef>,
    /// Clauses marked pending-garbage (deferred HBR subsumption deletion).
    /// Incremented in probe_propagate, decremented in collect_level0_garbage.
    pub(super) pending_garbage_count: u32,
    /// True when watches have been disconnected for watch-free BVE
    /// (CaDiCaL fastelim.cpp:463 reset_watches pattern). While true,
    /// add_clause_watched skips watch attachment and BCP must not run.
    pub(super) watches_disconnected: bool,
    /// When true, `delete_clause_checked` skips the per-deletion O(num_vars)
    /// stale reason scan and instead pushes affected variable indices onto
    /// `stale_reasons`. Caller MUST call `clear_stale_reasons()` after the
    /// batch completes. This reduces bulk-deletion cost from
    /// O(deleted × num_vars) to O(stale_count).
    pub(super) defer_stale_reason_cleanup: bool,
    /// When true, `delete_clause_observed` buffers proof deletion emissions
    /// (both forward checker and proof manager) instead of emitting them
    /// immediately. Used during BVE to ensure all resolvent additions appear
    /// in the proof stream before any deletion, preventing cross-variable
    /// ordering violations where variable A's deletions remove clauses needed
    /// for variable B's resolvent RUP derivability (#8011).
    pub(super) defer_proof_deletions: bool,
    /// Buffered proof deletions: `(clause_literals, clause_id)` pairs collected
    /// during deferred mode. Flushed by `flush_deferred_proof_deletions()`
    /// after all BVE resolvents for the current round have been added.
    pub(super) deferred_proof_deletions: Vec<(Vec<Literal>, u64)>,
    /// Minimal trail rewind after inprocessing (#8095).
    ///
    /// Tracks the earliest trail position affected during an inprocessing round.
    /// When a new unit is derived (enqueued on the trail) or a reason clause is
    /// deleted, this is updated to the minimum of the current value and the
    /// affected trail position. After inprocessing, `rebuild_watches` uses this
    /// to set `qhead` instead of rewinding to 0, avoiding O(trail × avg_watches)
    /// re-propagation of unaffected assignments.
    ///
    /// `None` means no trail positions were affected during the current
    /// inprocessing round (no new units, no deleted reasons). In that case,
    /// `qhead` is left at the trail length (no re-propagation needed beyond
    /// what was already propagated).
    pub(super) earliest_affected_trail_pos: Option<usize>,
    /// Variable indices with potentially stale reason references, collected
    /// during deferred-mode clause deletion. Bounded by the number of clause
    /// deletions per inprocessing round (typically hundreds, vs 100K+ total
    /// variables). Cleared by `clear_stale_reasons()`.
    pub(super) stale_reasons: Vec<u32>,
    /// Whether hyper-binary resolution is enabled during probing
    pub(super) hbr_enabled: bool,
    /// Experimental, default-off LRAT proof path for failed-literal parent-chain units.
    pub(super) lrat_probe_parent_chain_enabled: bool,
    /// Experimental, default-off LRAT-safe probe cadence rescue when BVE/factor
    /// are due but proof-clamped.
    pub(super) lrat_proof_clamp_probe_rescue_enabled: bool,
    /// Experimental, default-off scheduler policy: count productive
    /// backbone/decompose pass yields as inprocessing round productivity.
    pub(super) inprocessing_yield_productivity_rescue_enabled: bool,
    /// Experimental, default-off scheduler policy: after a round is productive
    /// only because of yield rescue, push the shared backbone row out by a
    /// bounded cooldown to limit extra backbone work.
    pub(super) inprocessing_yield_rescue_backbone_cooldown_enabled: bool,
    /// Experimental, default-off scheduler policy: delay only bounded-CDCL
    /// backbone after zero-yield decompose rounds with expensive bounded work.
    pub(super) bounded_backbone_zero_decompose_backoff_enabled: bool,
    /// Reusable buffer for HBR clause literals (avoids allocation in hot loop)
    pub(super) hbr_lits: Vec<Literal>,
    /// Parent literal during probing, indexed by variable.
    pub(super) probe_parent: Vec<Option<Literal>>,
    /// Per-variable lifecycle state machine (CaDiCaL flags.hpp).
    /// Replaces the previous `eliminated: Vec<bool>` (#3906).
    pub(super) var_lifecycle: lifecycle::VarLifecycle,
    /// Shared mark array for inprocessing tautology/duplicate checks.
    pub(super) lit_marks: LitMarks,
    /// Per-variable subsume dirty bits (CaDiCaL flags.subsume).
    /// True = variable appeared in a clause added since last subsumption round.
    /// Used for incremental scheduling: only clauses with >= 2 dirty vars are candidates.
    pub(super) subsume_dirty: Vec<bool>,
    /// Per-variable dirty bit for occurrence-guided level-0 garbage collection (#8097).
    /// `l0_gc_dirty[var_index]` is true when the variable was newly fixed at level 0
    /// since the last GC pass. During GC, only clauses containing at least one dirty
    /// variable need scanning — clauses with no dirty variables are guaranteed unaffected.
    pub(super) l0_gc_dirty: Vec<bool>,
    /// Per-literal dirty bit for targeted watch-list flushing (#8101).
    /// When a long clause is deleted, its two watched literals are marked dirty.
    /// `flush_watches()` processes only dirty literals instead of sweeping all
    /// `num_vars * 2` lists, reducing cost from O(total_watches) to
    /// O(deleted_clauses * avg_dirty_list_len).
    pub(super) dirty_watches: Vec<bool>,
    /// Explicit list of dirty literal indices for O(dirty) iteration (#8101).
    /// Avoids scanning the entire `dirty_watches` bitmap. Entries may contain
    /// duplicates (de-duped via the `dirty_watches` bitmap during flush).
    pub(super) dirty_watch_list: Vec<u32>,
    /// Occurrence list for level-0 garbage collection (#8097).
    /// Lazily built from all active clauses on first GC call, then maintained
    /// incrementally. Set to `None` on compaction/reset.
    pub(super) gc_occ: Option<crate::occ_list::OccList>,
    /// Persistent scratch allocation for `gc_occ`. `collect_level0_garbage`
    /// rebuilds `gc_occ` from scratch every fixpoint pass but only ever calls
    /// `get()` on it (it is set to `None` before any clause mutation), so the
    /// occurrence vectors are dropped and reallocated on each incremental
    /// solve. On million-clause hard MaxSAT parts this per-solve rebuild was a
    /// dominant cost. This holds the freed occ-only allocation between passes
    /// and solves so `clear()` (which retains capacity) replaces the drop +
    /// realloc + regrow. Behavior is identical: a cleared list equals a fresh
    /// one. Set to `None` on compaction/reset alongside `gc_occ`.
    pub(super) gc_occ_scratch: Option<crate::occ_list::OccList>,
    /// Centralized inprocessing scheduling: one `TechniqueControl` per technique.
    /// Replaces the flat `next_*` + `*_enabled` fields (#3546).
    pub(super) inproc_ctrl: inproc_control::InprocessingControls,
    /// Pristine copy of `inproc_ctrl` taken just before proof-mode overrides
    /// were applied (#A2b). Restored by
    /// `degrade_proof_bookkeeping_after_exhaustion` so a synthesized-default
    /// run whose proof bookkeeping budget is exhausted regains full
    /// inprocessing power for the remainder of the search.
    pub(super) inproc_ctrl_pre_proof: Option<inproc_control::InprocessingControls>,
    /// Preprocessing quick mode: skip HTR, probing, conditioning, subsumption.
    /// CaDiCaL defaults to 0 full preprocessing rounds (internal.cpp:805).
    /// Quick path runs only: congruence, backbone, sweep, decompose, factor,
    /// fastelim. Heavy passes fire in the first inprocessing round (~2K conflicts).
    pub(super) preprocessing_quick_mode: bool,
    // Inprocessing engines (cold, separated for cache locality — #5090)
    /// All inprocessing engine instances, grouped into a sub-struct to keep
    /// them out of the Solver's hot BCP cache lines.
    pub(crate) inproc: inproc_engines::InprocessingEngines,
    // ══════════════════════════════════════════════════════════════════════
    // JIT: non-BCP JIT state (conflict processor)
    // BCP JIT compilation (CompiledFormula, per-variable propagation functions,
    // watch-JIT, PGO, deferred pairs, full-BCP) removed in #8517.
    // ══════════════════════════════════════════════════════════════════════
    /// JIT-compiled conflict analysis literal processor (#8277).
    #[cfg(feature = "jit")]
    pub(super) jit_conflict_processor: Option<ay_jit::conflict_jit::CompiledConflictProcessor>,
    /// Reusable output buffer for the JIT conflict processor (#8277).
    #[cfg(feature = "jit")]
    pub(super) jit_conflict_output: ay_jit::conflict_jit::ConflictProcessorOutput,
    // ══════════════════════════════════════════════════════════════════════
    // COLD: boxed restart/proof/incremental/tracing state
    // ══════════════════════════════════════════════════════════════════════
    /// Boxed cold tail containing restart, proof, incremental, and tracing state.
    pub(super) cold: Box<cold::ColdState>,
    /// Clause provenance tracker for UNSAT debugging (#8321).
    /// Opt-in via `AY_CLAUSE_PROVENANCE=1`. Zero-overhead when disabled.
    pub(crate) provenance: crate::clause_provenance::ProvenanceTracker,
    /// DIP-ERCL manager: tracks extension variables and DIP detection state (#8440).
    pub(crate) dip: dip::DipManager,
    /// Domain-restricted decision heuristic for IC3/PDR queries (#8430).
    ///
    /// When `Some(bitmap)`, decisions are restricted to variables where
    /// `bitmap[var_index]` is `true`. BCP still propagates all clauses
    /// (soundness requires full propagation), but decisions only pick
    /// from the domain. This avoids exploring irrelevant parts of the
    /// search space when IC3 queries concern a small cube (5-50 vars)
    /// within a large transition system (thousands of vars).
    ///
    /// GipSAT rIC3 design: domain restriction applies at decision level > 0.
    /// Level-0 propagation always uses the full clause set.
    pub(super) active_domain: Option<Vec<bool>>,
    /// Decision domain: the ORIGINAL (caller-provided) domain for decision
    /// heuristic filtering (#8661). When `active_domain` is expanded to
    /// include transitively connected non-domain variables (for BCP soundness),
    /// `decision_domain` preserves the original domain so that decisions are
    /// still restricted to the caller's intended variables. Used by
    /// `pick_domain_restricted_decision` when the bucket queue is inactive.
    pub(super) decision_domain: Option<Vec<bool>>,
    /// Whether the bucket-queue VSIDS is active for domain-restricted queries (#8476).
    ///
    /// When `true`, `pick_domain_restricted_decision` uses the O(1) amortized
    /// bucket queue instead of the O(log n) binary heap. Activated when
    /// `set_domain` is called with a small domain (<= 64 variables), and
    /// automatically disabled after `BUCKET_QUEUE_RESTART_THRESHOLD` restarts,
    /// at which point the solver rebuilds the heap for the remaining domain
    /// variables and continues with the standard EVSIDS/CHB selection.
    pub(super) bucket_queue_active: bool,
    /// Number of restarts since the last `set_domain` call (#8476).
    ///
    /// Used to trigger the bucket-queue-to-heap switch after
    /// `BUCKET_QUEUE_RESTART_THRESHOLD` restarts within a single domain.
    pub(super) domain_restarts: u32,
    /// Relevancy brancher enable flag (Increment 1, relevancy propagation).
    ///
    /// When `true`, decisions may be restricted to the CNF relevancy frontier
    /// (variables occurring unassigned in a currently-unsatisfied clause) while
    /// the search is WANDERING (the hybrid trip-wire in `solver/relevancy.rs`).
    /// Decisions-only: BCP and the model gate are untouched, so a wrong
    /// don't-care degrades to `unknown`, never wrong-SAT. Set by the QF_UFLIA
    /// split-loop lane via `set_relevancy_branching`; off by default. See
    /// the development design notes.
    pub(super) relevancy_branching: bool,
    /// Reusable scratch buffer for the relevancy frontier (`relevancy.rs`).
    /// `relevancy_buf[var_index]` is `true` when the variable is currently
    /// relevant. Kept on the solver to avoid per-decision allocation.
    pub(super) relevancy_buf: Vec<bool>,
    /// Count of decisions taken under relevancy restriction (observability).
    pub(super) relevancy_decisions: u64,
    /// Relevancy HARD mode (`relevancy.rs`): when `true` (and
    /// `relevancy_branching`), the frontier restriction engages on EVERY
    /// decision — no warm-up / wander-ratio trip-wire. Used by the UFLIA
    /// hybrid's lazy-arm fallback, where arm-level protection (the eager
    /// first attempt served the baseline-easy instances) makes the
    /// prototype-faithful hard restriction safe to run.
    pub(super) relevancy_hard: bool,
    /// Wander-abort for hybrid arm routing (`relevancy.rs`): when armed, the
    /// CDCL loops return Unknown once the search WANDERS past the thresholds
    /// (conflict/decision deltas from the armed baselines + decisions/conflicts
    /// ratio), so the DPLL(T) executor can re-route the check-sat to the lazy
    /// arm with relevancy. Soundness-neutral: aborting a solve early yields
    /// `unknown`, never a verdict.
    pub(super) wander_abort_armed: bool,
    /// Sticky executor-visible signal: an armed solve aborted on wander.
    /// Cleared when (re-)armed.
    pub(super) wander_abort_tripped: bool,
    /// Conflict counter snapshot taken at arm time (delta base).
    pub(super) wander_abort_base_conflicts: u64,
    /// Decision counter snapshot taken at arm time (delta base).
    pub(super) wander_abort_base_decisions: u64,
}

/// Discriminated reason kind for a variable (#8034).
///
/// Used by conflict analysis and minimization to handle binary literal
/// reasons inline without arena access.
pub(crate) enum ReasonKind {
    /// Decision variable (no reason).
    Decision,
    /// Clause reason: arena offset.
    Clause(ClauseRef),
    /// Binary literal reason: the OTHER (false) literal from the binary clause.
    /// Stored as a tagged literal in `VarData.reason` (Kissat fastassign.h:12-19).
    BinaryLiteral(Literal),
    /// Lazy theory reason (#8467): the reason clause has not been materialized.
    /// The u32 is an index into the solver's `lazy_theory_reasons` table.
    /// The extension must be called to materialize the full clause on demand.
    LazyTheory(u32),
}

impl Solver {
    /// Get the reason clause for a variable, or None if it's a decision variable,
    /// has a binary literal reason (#8034), or has a lazy theory reason (#8467).
    ///
    /// Binary literal and lazy theory reasons return `None` because they have
    /// no `ClauseRef`. Callers that need to distinguish all reason kinds should
    /// use `var_reason_kind()`.
    #[inline(always)]
    pub(crate) fn var_reason(&self, var_idx: usize) -> Option<ClauseRef> {
        let vd = &self.var_data[var_idx];
        let r = vd.reason;
        if r == NO_REASON || is_binary_literal_reason(r) || vd.is_lazy_theory_reason() {
            None
        } else {
            Some(ClauseRef(r))
        }
    }

    /// Get the discriminated reason kind for a variable (#8034, #8467).
    ///
    /// Returns `Decision` for unassigned or decision variables, `Clause` for
    /// clause reasons, `BinaryLiteral` for binary literal reasons, or
    /// `LazyTheory` for unmaterialized theory reasons.
    #[inline(always)]
    pub(crate) fn var_reason_kind(&self, var_idx: usize) -> ReasonKind {
        let vd = &self.var_data[var_idx];
        let r = vd.reason;
        if r == NO_REASON {
            ReasonKind::Decision
        } else if vd.is_lazy_theory_reason() {
            ReasonKind::LazyTheory(r)
        } else if is_binary_literal_reason(r) {
            ReasonKind::BinaryLiteral(Literal(binary_reason_lit(r)))
        } else {
            ReasonKind::Clause(ClauseRef(r))
        }
    }
}
