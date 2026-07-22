// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Generic Nelson-Oppen theory combiner.
//!
//! Replaces bespoke combined solver adapters with a single implementation
//! of the Nelson-Oppen fixpoint loop, parameterized by which sub-solvers
//! participate. Each theory is optional except EUF (always present).
//!
//! # Supported Combinations
//!
//! | LIA | LRA | Arrays | Replaces           | Logic     |
//! |-----|-----|--------|--------------------|-----------|
//! |     |     | yes    | ArrayEufSolver     | QF_AX     |
//! | yes |     |        | UfLiaSolver        | QF_UFLIA  |
//! |     | yes |        | UfLraSolver        | QF_UFLRA  |
//! | yes |     | yes    | AufLiaSolver       | QF_AUFLIA |
//! |     | yes | yes    | AufLraSolver       | QF_AUFLRA |

// Wave 1: TheoryCombiner now used in production dispatch (#6332).

use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_arrays::{ArrayPropagatedEqualityReplay, ArraySolver, ExactSelectModelEqKey};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::kani_compat::DetHashSet;
use ay_core::{
    DiscoveredEquality, Sort, TermData, TermId, TermStore, TheoryLit, TheoryResult, TheorySolver,
};
use ay_euf::EufSolver;
use ay_lia::LiaSolver;
use ay_lra::LraSolver;

use super::check_loops::defer_non_local_result;
use super::interface_bridge::InterfaceBridge;
use crate::term_helpers::{
    arg_involves_select_or_store, involves_array, involves_int_arithmetic,
    involves_real_arithmetic, is_select_or_store, is_select_real_equality, is_uf_int_equality,
    is_uf_real_equality,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct EufArrayNotifyReplayEdge {
    pub(crate) target: TermId,
    pub(crate) source: TermId,
    pub(crate) reason: Vec<TheoryLit>,
}

/// Endpoint adjacency + dedup index over a `Vec<EufArrayNotifyReplayEdge>`,
/// maintained incrementally across the prune/append batch loops so the
/// covered-by DFS visits O(deg) edges per node instead of re-scanning the
/// whole edge vector (#alia-notify-replay-index). Production stopped
/// calling the covered-by kernel when the export/import path moved to
/// exact-dup superset retention (#no-replay-quadratic M2); the kernel and
/// this index are kept test-only as the reference for covered-by semantics.
#[cfg(test)]
#[derive(Default)]
struct EufArrayNotifyEdgeIndex {
    by_endpoint: ay_core::kani_compat::DetHashMap<TermId, Vec<usize>>,
    dedup: DetHashSet<EufArrayNotifyReplayEdge>,
    /// Reusable DFS scratch (epoch-stamped so no per-candidate clearing):
    /// `eligible_*` are per-edge caches of the reason-subset test, `seen` is
    /// the visited-term set, `stack` the DFS worklist.
    epoch: u32,
    eligible_epoch: Vec<u32>,
    eligible_value: Vec<bool>,
    seen: ay_core::kani_compat::DetHashMap<TermId, u32>,
    stack: Vec<TermId>,
}

#[cfg(test)]
impl EufArrayNotifyEdgeIndex {
    fn build(edges: &[EufArrayNotifyReplayEdge]) -> Self {
        let mut index = Self::default();
        for (idx, edge) in edges.iter().enumerate() {
            index.push(idx, edge);
        }
        index
    }

    fn push(&mut self, idx: usize, edge: &EufArrayNotifyReplayEdge) {
        self.by_endpoint.entry(edge.target).or_default().push(idx);
        if edge.source != edge.target {
            self.by_endpoint.entry(edge.source).or_default().push(idx);
        }
        self.dedup.insert(edge.clone());
    }
}

impl EufArrayNotifyReplayEdge {
    pub(crate) fn new(target: TermId, source: TermId, mut reason: Vec<TheoryLit>) -> Self {
        reason.sort_by_key(|lit| (lit.term.0, lit.value));
        reason.dedup_by_key(|lit| (lit.term, lit.value));
        Self {
            target,
            source,
            reason,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CrossTheoryEqualityReplay {
    pub(crate) lhs: TermId,
    pub(crate) rhs: TermId,
    pub(crate) reason: Vec<TheoryLit>,
}

impl CrossTheoryEqualityReplay {
    pub(crate) fn new(lhs: TermId, rhs: TermId, mut reason: Vec<TheoryLit>) -> Self {
        let (lhs, rhs) = if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) };
        reason.sort_by_key(|lit| (lit.term.0, lit.value));
        reason.dedup_by_key(|lit| (lit.term, lit.value));
        Self { lhs, rhs, reason }
    }

    fn same_pair(&self, other: &Self) -> bool {
        self.lhs == other.lhs && self.rhs == other.rhs
    }
}

/// Reusable, epoch-stamped DFS scratch for
/// `cross_theory_equality_replay_covered_by_indexed`
/// (#qfuflia-replay-cover-scratch). Transplants the exact pattern the
/// `euf_array_notify` sibling index already uses (`EufArrayNotifyEdgeIndex`):
/// the covered-by BFS previously `Default::default()`-ed a fresh
/// `DetHashMap`/`DetHashSet`/`Vec` on EVERY call, and ~40% of the wall's
/// self-time was the resulting `reserve_rehash`. Here the buffers are cleared
/// (or epoch-invalidated), never reallocated:
///   - `eligible_*` cache the per-edge reason-subset test, indexed by replay
///     slot; a fresh `epoch` invalidates every stale entry with NO O(E) clear.
///   - `seen` marks visited terms by epoch (stale ⇒ != epoch ⇒ revisit).
///   - `stack` is the DFS worklist, `clear()`-ed per call (keeps capacity).
///
/// Semantics-identical to the former per-call allocation: same reachability
/// BFS, same lazy `cross_theory_replay_reason_subset` eligibility, same
/// boolean. A debug-build reference oracle (`..._reference`) cross-checks every
/// answer on small inputs.
#[derive(Default)]
pub(super) struct CrossReplayCoverScratch {
    epoch: u32,
    eligible_epoch: Vec<u32>,
    eligible_value: Vec<bool>,
    seen: ay_core::kani_compat::DetHashMap<TermId, u32>,
    stack: Vec<TermId>,
}

/// INTERFACE-DIET mode (`AY_INTERFACE_DIET`): withhold POSITIVE pure-UF=UF Int
/// equalities from the LIA Nelson-Oppen interface, then value-certify the
/// arrangement against RAW LIA values before accepting Sat. Read once per
/// process at construction; REFUSES to arm if any `AY_A5_*` toggle is set (the
/// A5 defer lanes and the diet both re-route UF-containing Int equalities and
/// must never compose). See `interface-diet-campaign` (memory).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum DietMode {
    /// Unset — byte-identical to the pre-diet combiner.
    Off,
    /// Reserved for the M2/M4 differential harness: recognised but does NOT yet
    /// withhold (byte-identical verdict). Kept so the flag surface is stable.
    Shadow,
    /// Withhold pure-UF=UF Int equalities + run the pre-Sat arrangement certifier.
    On,
}

impl DietMode {
    fn from_env() -> Self {
        static MODE: std::sync::OnceLock<DietMode> = std::sync::OnceLock::new();
        *MODE.get_or_init(|| {
            // Never arm alongside any A5 lane (mutually-exclusive re-routing).
            let any_a5 =
                std::env::vars_os().any(|(k, _)| k.to_string_lossy().starts_with("AY_A5_"));
            if any_a5 {
                return DietMode::Off;
            }
            match std::env::var("AY_INTERFACE_DIET").ok().as_deref() {
                Some("on") | Some("1") => DietMode::On,
                Some("shadow") => DietMode::Shadow,
                _ => DietMode::Off,
            }
        })
    }

    /// True only in `On` mode: the combiner actually withholds + certifies.
    pub(crate) fn withholds(self) -> bool {
        matches!(self, DietMode::On)
    }
}

/// A centralized Nelson-Oppen theory combiner.
///
/// Implements the Nelson-Oppen fixpoint loop once, parameterized by which
/// sub-solvers participate. EUF is always present; LIA, LRA, and Arrays
/// are optional.
///
/// This replaces the bespoke per-logic adapters (`UfLiaSolver`, `AufLiaSolver`,
/// etc.) with a single implementation of the check loop, equality propagation,
/// push/pop, and assert_literal routing. Fixing a bug in the N-O loop fixes
/// it for ALL logic combinations simultaneously.

pub struct TheoryCombiner<'a> {
    /// A5 lazy arith-equality adapter (experiment, AY_A5_LAZY_ARITH=1):
    /// Int EQUALITY atoms are EUF-owned during search (congruence handles
    /// them; z3's e-graph does the same, materializing rows for only ~3% of
    /// such atoms) and asserted into LIA in one batch at the final check.
    /// Inequalities/bounds stay eagerly routed. (term, value) pairs in
    /// assertion order; deduped by the final-check replay.
    deferred_arith_eqs: Vec<(TermId, bool)>,
    a5_lazy_arith: bool,
    /// INTERFACE-DIET mode, read once at construction (`AY_INTERFACE_DIET`).
    pub(super) interface_diet: DietMode,
    /// Per-`check()` bound on certifier materialization re-run rounds — a
    /// runaway certify↔materialize ping-pong fail-closes to `Unknown` (never a
    /// wrong verdict). Reset at each `nelson_oppen_check` entry.
    pub(super) diet_certify_rounds: u32,
    /// Re-entrancy guard: the final-check replay routes deferred atoms back
    /// through assert_literal; the defer branch must not re-capture them.
    a5_replaying: bool,
    /// A5 v2 relevance state: Int variables that appear in eagerly-routed
    /// arithmetic atoms (bounds/inequalities) — 'arith-connected'. A deferred
    /// equality MATERIALIZES into LIA the moment one of its leaf variables
    /// becomes connected (single-hop relevance; the final-check replay remains
    /// the completeness backstop for never-materialized atoms).
    a5_bounded_vars: DetHashSet<TermId>,
    /// leaf var -> indices into deferred_arith_eqs awaiting that var.
    a5_deferred_by_var: ay_core::kani_compat::DetHashMap<TermId, Vec<usize>>,
    /// Parallel to deferred_arith_eqs: already materialized into LIA.
    a5_materialized: Vec<bool>,
    /// Arithmetic-routed literal asserted since the last BCP-time LIA check
    /// (#qfuflia-lia-bcp-gate). Starts true; set on every LIA-routed assert
    /// and on push/pop/reset so lifecycle transitions always re-check.
    lia_bcp_dirty: bool,
    pub(super) terms: &'a TermStore,
    pub(super) euf: EufSolver<'a>,
    pub(super) lia: Option<LiaSolver<'a>>,
    pub(super) lra: Option<LraSolver>,
    pub(super) arrays: Option<ArraySolver<'a>>,
    /// Monotonic counter for mutations visible to the array sub-solver.
    ///
    /// Used to skip redundant `arrays.check()` calls in the N-O loop when the
    /// array state has not changed since the last successful, no-new-equalities
    /// array pass (#6820).
    pub(super) array_epoch: u64,
    /// Array epoch at which `arrays.check()` last returned `Sat` and emitted no
    /// new equalities. When equal to `array_epoch`, the next N-O iteration can
    /// skip the array step entirely.
    pub(super) array_quiescent_epoch: Option<u64>,
    /// Whether the ArraySolver participates in the BCP-time lanes
    /// (`TheorySolver::propagate` + `check_during_propagate`).
    ///
    /// `true` for every mixed-arithmetic combiner (AUFLIA/AUFLRA — unchanged
    /// behavior). `false` for the pure Array+EUF (QF_AX) combiner, where the
    /// eager ROW instance surface (`run_array_axiom_fixpoint_at`), EUF
    /// congruence, and SAT BCP carry the search. This avoids repeating the
    /// singleton, dirty-entry, and full `check_impl` scans at every BCP
    /// quiescence.
    ///
    /// SOUNDNESS SHAPE: this only skips the BCP-time OPTIMIZATION lanes the
    /// `TheorySolver` contract explicitly allows to be weaker than `check()`
    /// (`check_during_propagate` docs; `needs_final_check_after_sat() ==
    /// true` for this combiner). The full `check()` — the N-O fixpoint with
    /// the complete arrays battery and `final_check` ladder — still runs on
    /// every candidate model, so a missed BCP-time conflict/propagation can
    /// only surface later (more search or sound-unknown), never flip a
    /// verdict. Candidate models still pass the arrays final check and the
    /// independent model gate.
    ///
    /// Kill switch: `AY_QFAX_ARR_BCP_LANES=1` restores the legacy
    /// always-on lanes (A/B lever + safety valve, mirrors
    /// `AY_NO_PROP_FEEDBACK`).
    pub(super) arrays_bcp_lanes: bool,
    pub(super) interface: Option<InterfaceBridge>,
    pub(super) scope_depth: usize,
    pub(super) label: &'static str,
    pub(super) arith_prop_label: &'static str,
    pub(super) euf_prop_label: &'static str,
    pub(super) arr_prop_label: &'static str,

    // =========================================================================
    // Interrupt support (#8637)
    // =========================================================================
    /// Optional interrupt flag shared with the Executor. When set to `true`,
    /// the Nelson-Oppen fixpoint loop returns `Unknown` early.
    pub(super) interrupt: Option<Arc<AtomicBool>>,
    /// Optional deadline from the Executor's solve_deadline. When reached,
    /// the Nelson-Oppen fixpoint loop returns `Unknown` early (#8642).
    pub(super) deadline: Option<Instant>,

    /// #uflia-cong-repair-arm: enable the accept-point UF function-graph
    /// consistency scan (`discover_congruence_repair_eqs`). Default `false`
    /// (fast accept): the scan runs ONLY on the executor's armed re-solve,
    /// after the independent model gate refuted the first-pass model. Keeping
    /// it off on the first pass lets a latent-consistent collision stay SAT
    /// with zero wasteful splits, and fires the arg-split refinement only for
    /// models the gate actually rejects. Threaded from
    /// `Executor::arm_uflia_congruence_repair`; meaningful only in the UFLIA
    /// lane (the scan is `label == "UFLIA"`-scoped).
    pub(super) arm_uflia_congruence_repair: bool,

    /// #read-congruence-quantified-scope (#7956 tseitin regression): act on
    /// the store-carrying READ-CONGRUENCE index-pair obligations
    /// (`UndecidedIndexPair::sels`, #seed-1213-case-187) in
    /// `propagate_array_index_info`. Default `true` — the wrong-model
    /// construction fix for quantifier-free problems is fully preserved. The
    /// executor sets it `false` for ground (re-)solves inside the
    /// quantifier-instantiation pipeline: there the instantiated select terms
    /// routinely carry symbolic offsets the arithmetic solver has no value
    /// for, so the fail-closed "unknown value ⇒ keep" rule turned every pair
    /// into a model-equality split over unbounded Int index terms and sent
    /// the ground search wandering (10M+ conflict-free decisions on the
    /// verification-consumer ext_eq Tseitin encoding) instead of converging. Quantified
    /// SAT answers still pass full model validation over every assertion plus
    /// the independent model gate downstream, so disabling the pair
    /// obligations there restores the (pre-7d98c04d) monitored-coverage-gap
    /// status quo for quantified models without touching any gate.
    pub(super) read_congruence_pairs_enabled: bool,

    // =========================================================================
    // Nelson-Oppen observability counters (#8165)
    // =========================================================================
    /// Total N-O fixpoint iterations across all check calls.
    pub(super) nelson_oppen_rounds: u64,
    /// Maximum N-O iterations in a single check call.
    pub(super) nelson_oppen_max_rounds: u64,
    /// Number of equalities propagated from arithmetic to EUF.
    pub(super) equalities_propagated_to_euf: u64,
    /// Number of equalities propagated from EUF to arithmetic.
    pub(super) equalities_propagated_to_arith: u64,

    /// Component cache for EUF-derived Array equalities already notified to
    /// the array solver in the current scope. The array bridge only needs a
    /// spanning forest of merge notifications to connect `array_vars`; sending
    /// every EUF congruence edge replays the same ROW1/ROW2/store-chain work
    /// on storecomm-style formulas (#8785).
    pub(super) euf_array_notify_parent: HashMap<TermId, TermId>,
    /// Reason-carrying EUF-array notification edges emitted by this combiner.
    /// AUFLIA's lazy split loop creates a fresh combiner after each outer
    /// model-equality refinement, so these edges are exported and replayed in
    /// the next combiner only when all SAT-visible reasons are true again.
    pub(super) euf_array_notify_replay_edges: Vec<EufArrayNotifyReplayEdge>,
    /// O(1) membership mirror of `euf_array_notify_replay_edges`
    /// (#no-replay-quadratic M2): `record_euf_array_notify_replay_edge`
    /// used `Vec::contains` per recorded edge — quadratic within a round;
    /// a single giant merged component on QF_ALIA cs_lazy.i_6 records ~87k
    /// edges in one round (2026-07-12 instrumented count).
    pub(super) euf_array_notify_replay_edge_set: DetHashSet<EufArrayNotifyReplayEdge>,
    /// Replay edges imported into the fresh AUFLIA combiner before SAT model
    /// assignment import. They are replayed from `check()` after assignment
    /// import validates their reasons.
    pub(super) imported_euf_array_notify_replay_edges: Vec<EufArrayNotifyReplayEdge>,
    /// Reason-carrying array-derived equalities emitted by this combiner.
    /// These are exported across fresh AUFLIA combiners to avoid re-emitting
    /// the same large array-to-EUF equality batch every refinement round.
    pub(super) array_equality_replays: Vec<ArrayPropagatedEqualityReplay>,
    /// O(1) membership mirror of `array_equality_replays`
    /// (#no-replay-quadratic): the per-Nelson-Oppen-step dedup used
    /// `Vec::contains` over reason-carrying structs, quadratic in retained
    /// replays.
    pub(super) array_equality_replays_seen: DetHashSet<ArrayPropagatedEqualityReplay>,
    /// Cursor into the array solver's `sent_equality_replay_log`
    /// (#no-replay-quadratic): entries before it were already routed through
    /// the admit/pending pipeline in `check_arrays_step`.
    pub(super) array_replay_export_cursor: usize,
    /// Sent replays whose reasons did not hold when first seen; re-validated
    /// each `check_arrays_step` (exactly the semantics of the former
    /// full-set rescan, minus the quadratic rescans of admitted entries).
    pub(super) array_replay_pending: Vec<ArrayPropagatedEqualityReplay>,
    /// Membership mirror of `array_replay_pending`.
    pub(super) array_replay_pending_set: DetHashSet<ArrayPropagatedEqualityReplay>,
    /// Reason-carrying array-derived equalities imported into a fresh combiner.
    pub(super) imported_array_equality_replays: Vec<ArrayPropagatedEqualityReplay>,
    /// Reason-carrying cross-theory equalities emitted by this combiner.
    ///
    /// AUFLIA's split loop recreates the combiner after every model-equality
    /// refinement. Persisting validated equality replays keeps fresh LIA/EUF
    /// instances from rediscovering the same propagation wave from scratch.
    pub(super) cross_theory_equality_replays: Vec<CrossTheoryEqualityReplay>,
    /// Persistent endpoint index over `cross_theory_equality_replays`
    /// (#qfuflia-replay-index v3): term -> replay slots. Maintained
    /// incrementally by `record_cross_theory_equalities`; any other mutation
    /// of the replay vec must clear `cross_replay_index_valid`.
    pub(super) cross_replay_endpoint_index: ay_core::kani_compat::DetHashMap<TermId, Vec<usize>>,
    /// Whether `cross_replay_endpoint_index` matches
    /// `cross_theory_equality_replays`.
    pub(super) cross_replay_index_valid: bool,
    /// Reusable epoch-stamped DFS scratch for the cross-theory covered-by BFS
    /// (#qfuflia-replay-cover-scratch); see `CrossReplayCoverScratch`.
    pub(super) cross_replay_cover_scratch: CrossReplayCoverScratch,
    /// Canonical `(lhs, rhs, reason)` replays already routed through
    /// `insert_cross_theory_equality_replay_minimal` on
    /// `cross_theory_equality_replays` since the last `reset()`.
    ///
    /// PERF (#qfuflia-replay-memo): `record_cross_theory_equalities` re-derives
    /// the SAME cross-theory equalities on every N-O iteration/check, and each
    /// re-presentation paid a full O(replays) `covered_by` reachability scan
    /// (measured >98% of ~1M scans on FSet-heavy QF_UFLIA were exact
    /// re-presentations; each scanned ~550 replays). Because
    /// `cross_theory_equality_replays` is MONOTONIC between resets — `pop`/
    /// `soft_reset` never shrink it, and the `retain` inside `insert_minimal`
    /// only replaces a same-pair edge with a subset-reason (⊆) one that still
    /// covers everything the removed edge did — coverage is monotone, so once a
    /// canonical replay has been inserted-or-covered it stays inserted-or-covered
    /// and re-`insert_minimal` is provably a no-op. Skipping it on a memo hit is
    /// therefore behaviour-identical while replacing the O(replays) scan with an
    /// O(1) lookup. Cleared in `reset()` (the only place the replay vec is
    /// cleared); intentionally preserved across `soft_reset`/`pop`.
    pub(super) cross_theory_replay_processed: DetHashSet<CrossTheoryEqualityReplay>,
    /// Cross-theory equality replays imported into a fresh combiner.
    pub(super) imported_cross_theory_equality_replays: Vec<CrossTheoryEqualityReplay>,
    /// Current asserted SAT-visible literals, normalized through `not`.
    pub(super) current_assignments: HashMap<TermId, bool>,
    pub(super) current_assignment_trail: Vec<(TermId, Option<bool>)>,
    pub(super) current_assignment_scope_marks: Vec<usize>,

    /// Persistent per-pair rescue counter for array rescues over arithmetic
    /// conflicts (#6367). Shared from the pipeline state so counts survive
    /// `TheoryCombiner` recreations across outer refinement iterations.
    /// `None` means rescues are unbudgeted (legacy behaviour).
    pub(super) rescue_pair_counter: Option<crate::executor::SharedRescuePairCounter>,

    /// D0 datatype clash/acyclicity final-check pass over the EUF e-graph
    /// (`DESIGN_lazy_dt.md` stage D0; see `ay_dt::DtEgraphPass`). `Some` only
    /// when the executor registered the problem's datatypes
    /// ([`Self::register_datatypes`]); runs read-only at the Nelson-Oppen
    /// fixpoint just before a `Sat` verdict and can only block that verdict
    /// with an entailed datatype tautology lemma (or a fail-closed Unknown) —
    /// never influence it in the Sat direction.
    pub(super) dt_pass: Option<ay_dt::DtEgraphPass>,

    /// D1 lazy datatype tester/selector propagation during CDCL search
    /// (`DESIGN_lazy_dt.md` stage D1; see `ay_dt::DtLazyPropagator`). `Some`
    /// only when the executor also registered constructor SELECTOR signatures
    /// ([`Self::register_datatype_selectors`]) — today that is the
    /// `array_euf`/DtAx lane only, so the arithmetic combined lanes keep
    /// their exact pre-D1 behavior. Runs at BCP quiescence
    /// (`check_during_propagate`), gated on the e-graph merge change feed
    /// (`EufSolver::take_dt_merge_dirty`), and at the Nelson-Oppen fixpoint.
    /// Emits only independently re-derived DT tautology implication clauses
    /// via `NeedLemmas` (never bare propagations, never direct e-graph
    /// merges), so every conflict downstream remains checkable by the
    /// existing fail-closed verifiers.
    pub(super) dt_d1: Option<ay_dt::DtLazyPropagator>,
    /// Cached verify-only EUF solver used by the D1 pass to independently
    /// re-derive each propagation's explanation before emission (scope-local
    /// push/assert/check/pop per candidate; created lazily on first use).
    pub(super) dt_d1_verify: Option<EufSolver<'a>>,

    /// D2 splitting-on-demand over finite (all-nullary) datatype sorts
    /// (`DESIGN_lazy_dt.md` stage D2; see `ay_dt::DtSplitOnDemand`). `Some`
    /// only on the lazy (no-unroll) DT lane, where the executor materialized
    /// and registered domain-closure split bases
    /// ([`Self::register_datatype_splits`]). Runs at the Nelson-Oppen
    /// fixpoint; every emitted clause is an unconditional datatype
    /// exhaustiveness tautology validated structurally at registration.
    /// Its presence also enables the search-time D0 clash/cycle check at BCP
    /// quiescence (the lazy lane has no eager axiom encoding of those
    /// conflicts, so they must surface during search, not only at the
    /// fixpoint).
    pub(super) dt_d2: Option<ay_dt::DtSplitOnDemand>,
}

impl<'a> TheoryCombiner<'a> {
    /// M-A2 lazy-persistent-combiner: rebind the live combiner onto a SUPERSET
    /// (append-extended) term store so it can FOLLOW the executor's append-only
    /// `ctx.terms` as it grows between lazy-refinement rounds
    /// (ARRAY-PROCEDURE-CLOSER-BLUEPRINT §5 A2 / LAZY-M3 §M3.2).
    ///
    /// This closes the create-once + warm-reset lifecycle in production. The
    /// executor-BORROW half is handled by the caller (the shadow re-clones
    /// `ctx.terms` into a stable arena each round; the combiner holds
    /// `&'arena TermStore`, decoupled from `ctx.terms`, so the loop can still
    /// reborrow `&mut ctx.terms` between rounds). This method handles the
    /// SUB-SOLVER-SIZING half:
    ///
    /// * LIA / LRA keep their WARM simplex tableau + variable values (the §3.1
    ///   retained warm state) — their state is variable-keyed (not indexed by
    ///   `TermId`), so a grown store is safe; only the borrowed store pointer
    ///   follows the growth.
    /// * EUF / Arrays are REBUILT FRESH on the superset store. Their e-graph
    ///   (`enodes`/`uf`) and func-app congruence scan are Vec-indexed / sized
    ///   AGAINST THE STORE AT CONSTRUCTION and cannot represent a grown store's
    ///   new `select`/`store` term ids (a bare pointer swap OOB-panics in
    ///   `incremental_merge`). Rebuilding is correct-by-construction and, since
    ///   `soft_reset_warm` already COLD-resets EUF/Arrays (only their structure
    ///   is retained, and that structure is rebuilt from the store), it is
    ///   equivalent in retained state — just correctly sized. (An incremental
    ///   e-graph GROW that preserved EUF structural warmth across growth is the
    ///   remaining A2-authoritative optimization; for AUFLIA the store grows
    ///   almost every round, so the fresh path rebuilds EUF each round anyway.)
    ///
    /// Only sound when `new_terms` is a superset (same 0..old_len prefix) of the
    /// store this combiner was built on. Debug-only (shadow arm).
    #[cfg(debug_assertions)]
    pub fn rebind_terms(&mut self, new_terms: &'a TermStore) {
        self.terms = new_terms;
        // EUF and Arrays retain only STRUCTURE across a warm reset (their
        // assignment-derived merges are already cold-cleared by
        // `soft_reset_warm`). That structure is Vec-indexed / scanned against the
        // store size AT CONSTRUCTION (the e-graph `enodes`/`uf`, the func-app
        // congruence scan, the select/store caches) and CANNOT represent a grown
        // (superset) store's new term ids — a freshly-minted `select`/`store`
        // term id would index past `enodes.len()`. So rebuild them FRESH on the
        // superset store: correct-by-construction and equivalent in retained
        // state to the cold `soft_reset` they already receive, just correctly
        // sized. This is the sub-solver-sizing half of the A2 blocker — the Rust
        // borrow is handled by the arena; the e-graph must additionally grow.
        self.euf = EufSolver::new(new_terms);
        // LIA / LRA keep their WARM simplex tableau+values (the retained §3.1
        // warm state); only the borrowed store follows the growth.
        if let Some(lia) = &mut self.lia {
            lia.rebind_terms(new_terms);
        }
        if let Some(lra) = &mut self.lra {
            lra.set_terms(new_terms);
        }
        if self.arrays.is_some() {
            // The request sets are structural progress: their equality atoms
            // remain in the persistent SAT instance after an array solver is
            // rebuilt for the grown term store.  Dropping them here makes the
            // rebuilt solver re-emit an already-served `NeedModelEquality`
            // instead of continuing the current round.
            let requested_interface_eqs = self.export_array_requested_interface_eqs();
            let requested_model_eqs = self.export_array_requested_model_eqs();
            let exact_select_model_eq_keys = self.export_array_exact_select_model_eq_keys();
            // Mirror the `auf_lia` array configuration.
            let mut arrays = ArraySolver::new(new_terms);
            arrays.set_defer_expensive_checks(true);
            arrays.enable_registered_atom_scope(true);
            arrays.import_requested_interface_eqs(&requested_interface_eqs);
            arrays.import_requested_model_eqs(&requested_model_eqs);
            arrays.import_exact_select_model_eq_keys(&exact_select_model_eq_keys);
            self.arrays = Some(arrays);
            // The fresh array solver's `sent_equality_replay_log` starts empty;
            // drop the stale export cursor + pending replays that indexed the
            // previous solver's log (replays are a pure optimization — dropping
            // them only re-derives, never changes a verdict).
            self.array_replay_export_cursor = 0;
            self.array_replay_pending.clear();
            self.array_replay_pending_set.clear();
        }
        self.euf_array_notify_parent.clear();
        if let Some(interface) = &mut self.interface {
            interface.reset();
        }
    }

    // --- Constructors ---

    /// Create a combiner for EUF + Arrays (replaces ArrayEufSolver, QF_AX).
    pub fn array_euf(terms: &'a TermStore) -> Self {
        let mut arrays = ArraySolver::new(terms);
        arrays.set_defer_expensive_checks(true);
        arrays.enable_registered_atom_scope(true);
        Self {
            lia_bcp_dirty: true,
            deferred_arith_eqs: Vec::new(),
            a5_replaying: false,
            a5_bounded_vars: DetHashSet::default(),
            a5_deferred_by_var: ay_core::kani_compat::DetHashMap::default(),
            a5_materialized: Vec::new(),
            a5_lazy_arith: std::env::var_os("AY_A5_LAZY_ARITH").is_some(),
            interface_diet: DietMode::from_env(),
            diet_certify_rounds: 0,
            terms,
            euf: EufSolver::new(terms),
            lia: None,
            lra: None,
            arrays: Some(arrays),
            array_epoch: 0,
            array_quiescent_epoch: None,
            // Legacy-on by default; the QF_AX solve route demotes the lanes
            // for the shapes where they are measured pure overhead via
            // `set_arrays_bcp_lanes` (see the field docs).
            arrays_bcp_lanes: true,
            interface: None,
            scope_depth: 0,
            label: "AX",
            arith_prop_label: "",
            euf_prop_label: "AX-EUF",
            arr_prop_label: "AX-ARR",

            interrupt: None,
            deadline: None,
            arm_uflia_congruence_repair: false,
            read_congruence_pairs_enabled: true,

            nelson_oppen_rounds: 0,
            nelson_oppen_max_rounds: 0,
            equalities_propagated_to_euf: 0,
            equalities_propagated_to_arith: 0,
            euf_array_notify_parent: HashMap::default(),
            euf_array_notify_replay_edges: Vec::new(),
            euf_array_notify_replay_edge_set: Default::default(),
            imported_euf_array_notify_replay_edges: Vec::new(),
            array_equality_replays: Vec::new(),
            array_equality_replays_seen: DetHashSet::default(),
            array_replay_export_cursor: 0,
            array_replay_pending: Vec::new(),
            array_replay_pending_set: DetHashSet::default(),
            imported_array_equality_replays: Vec::new(),
            cross_theory_equality_replays: Vec::new(),
            cross_replay_endpoint_index: ay_core::kani_compat::DetHashMap::default(),
            cross_replay_index_valid: false,
            cross_replay_cover_scratch: CrossReplayCoverScratch::default(),
            cross_theory_replay_processed: DetHashSet::default(),
            imported_cross_theory_equality_replays: Vec::new(),
            current_assignments: HashMap::default(),
            current_assignment_trail: Vec::new(),
            current_assignment_scope_marks: Vec::new(),
            rescue_pair_counter: None,
            dt_pass: None,
            dt_d1: None,
            dt_d1_verify: None,
            dt_d2: None,
        }
    }

    /// Create a combiner for EUF + LIA (replaces UfLiaSolver, QF_UFLIA).
    pub fn uf_lia(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        // #uflia-eager-sweep: the eager UFLIA lane's inline theory-conflict
        // engine depends on the post-backtrack full re-propagation sweep
        // (bisect: f72a06aaa6 flipped it, #inc-implied-trail/#inc-prop-trail
        // deepened it — eager fingerprint smt.theory_conflicts 747 -> 132,
        // ~40 QF_UFLIA T:20 sats lost). Scoped to this lane — incremental
        // BMC/IC3 consumers keep the trail-restored fast path.
        lia.set_eager_repropagate_on_pop(true);
        Self {
            lia_bcp_dirty: true,
            deferred_arith_eqs: Vec::new(),
            a5_replaying: false,
            a5_bounded_vars: DetHashSet::default(),
            a5_deferred_by_var: ay_core::kani_compat::DetHashMap::default(),
            a5_materialized: Vec::new(),
            a5_lazy_arith: std::env::var_os("AY_A5_LAZY_ARITH").is_some(),
            interface_diet: DietMode::from_env(),
            diet_certify_rounds: 0,
            terms,
            euf: EufSolver::new(terms),
            lia: Some(lia),
            lra: None,
            arrays: None,
            array_epoch: 0,
            array_quiescent_epoch: None,
            interface: Some(InterfaceBridge::new()),
            scope_depth: 0,
            arrays_bcp_lanes: true,
            label: "UFLIA",
            arith_prop_label: "UFLIA-LIA",
            euf_prop_label: "UFLIA-EUF",
            arr_prop_label: "",

            interrupt: None,
            deadline: None,
            arm_uflia_congruence_repair: false,
            read_congruence_pairs_enabled: true,

            nelson_oppen_rounds: 0,
            nelson_oppen_max_rounds: 0,
            equalities_propagated_to_euf: 0,
            equalities_propagated_to_arith: 0,
            euf_array_notify_parent: HashMap::default(),
            euf_array_notify_replay_edges: Vec::new(),
            euf_array_notify_replay_edge_set: Default::default(),
            imported_euf_array_notify_replay_edges: Vec::new(),
            array_equality_replays: Vec::new(),
            array_equality_replays_seen: DetHashSet::default(),
            array_replay_export_cursor: 0,
            array_replay_pending: Vec::new(),
            array_replay_pending_set: DetHashSet::default(),
            imported_array_equality_replays: Vec::new(),
            cross_theory_equality_replays: Vec::new(),
            cross_replay_endpoint_index: ay_core::kani_compat::DetHashMap::default(),
            cross_replay_index_valid: false,
            cross_replay_cover_scratch: CrossReplayCoverScratch::default(),
            cross_theory_replay_processed: DetHashSet::default(),
            imported_cross_theory_equality_replays: Vec::new(),
            current_assignments: HashMap::default(),
            current_assignment_trail: Vec::new(),
            current_assignment_scope_marks: Vec::new(),
            rescue_pair_counter: None,
            dt_pass: None,
            dt_d1: None,
            dt_d1_verify: None,
            dt_d2: None,
        }
    }

    /// Create a combiner for EUF + LRA (replaces UfLraSolver, QF_UFLRA).
    pub fn uf_lra(terms: &'a TermStore) -> Self {
        let mut lra = LraSolver::new(terms);
        lra.set_combined_theory_mode(true);
        Self {
            lia_bcp_dirty: true,
            deferred_arith_eqs: Vec::new(),
            a5_replaying: false,
            a5_bounded_vars: DetHashSet::default(),
            a5_deferred_by_var: ay_core::kani_compat::DetHashMap::default(),
            a5_materialized: Vec::new(),
            a5_lazy_arith: std::env::var_os("AY_A5_LAZY_ARITH").is_some(),
            interface_diet: DietMode::from_env(),
            diet_certify_rounds: 0,
            terms,
            euf: EufSolver::new(terms),
            lia: None,
            lra: Some(lra),
            arrays: None,
            array_epoch: 0,
            array_quiescent_epoch: None,
            interface: Some(InterfaceBridge::new()),
            scope_depth: 0,
            arrays_bcp_lanes: true,
            label: "UFLRA",
            arith_prop_label: "UFLRA-LRA",
            euf_prop_label: "UFLRA-EUF",
            arr_prop_label: "",

            interrupt: None,
            deadline: None,
            arm_uflia_congruence_repair: false,
            read_congruence_pairs_enabled: true,

            nelson_oppen_rounds: 0,
            nelson_oppen_max_rounds: 0,
            equalities_propagated_to_euf: 0,
            equalities_propagated_to_arith: 0,
            euf_array_notify_parent: HashMap::default(),
            euf_array_notify_replay_edges: Vec::new(),
            euf_array_notify_replay_edge_set: Default::default(),
            imported_euf_array_notify_replay_edges: Vec::new(),
            array_equality_replays: Vec::new(),
            array_equality_replays_seen: DetHashSet::default(),
            array_replay_export_cursor: 0,
            array_replay_pending: Vec::new(),
            array_replay_pending_set: DetHashSet::default(),
            imported_array_equality_replays: Vec::new(),
            cross_theory_equality_replays: Vec::new(),
            cross_replay_endpoint_index: ay_core::kani_compat::DetHashMap::default(),
            cross_replay_index_valid: false,
            cross_replay_cover_scratch: CrossReplayCoverScratch::default(),
            cross_theory_replay_processed: DetHashSet::default(),
            imported_cross_theory_equality_replays: Vec::new(),
            current_assignments: HashMap::default(),
            current_assignment_trail: Vec::new(),
            current_assignment_scope_marks: Vec::new(),
            rescue_pair_counter: None,
            dt_pass: None,
            dt_d1: None,
            dt_d1_verify: None,
            dt_d2: None,
        }
    }

    /// Create a combiner for EUF + LIA + Arrays (replaces AufLiaSolver, QF_AUFLIA).
    pub fn auf_lia(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        let mut arrays = ArraySolver::new(terms);
        arrays.set_defer_expensive_checks(true);
        arrays.enable_registered_atom_scope(true);
        Self {
            lia_bcp_dirty: true,
            deferred_arith_eqs: Vec::new(),
            a5_replaying: false,
            a5_bounded_vars: DetHashSet::default(),
            a5_deferred_by_var: ay_core::kani_compat::DetHashMap::default(),
            a5_materialized: Vec::new(),
            a5_lazy_arith: std::env::var_os("AY_A5_LAZY_ARITH").is_some(),
            interface_diet: DietMode::from_env(),
            diet_certify_rounds: 0,
            terms,
            euf: EufSolver::new(terms),
            lia: Some(lia),
            lra: None,
            arrays: Some(arrays),
            array_epoch: 0,
            array_quiescent_epoch: None,
            interface: Some(InterfaceBridge::new()),
            scope_depth: 0,
            arrays_bcp_lanes: true,
            label: "AUFLIA",
            arith_prop_label: "AUFLIA-LIA",
            euf_prop_label: "AUFLIA-EUF",
            arr_prop_label: "AUFLIA-ARR",

            interrupt: None,
            deadline: None,
            arm_uflia_congruence_repair: false,
            read_congruence_pairs_enabled: true,

            nelson_oppen_rounds: 0,
            nelson_oppen_max_rounds: 0,
            equalities_propagated_to_euf: 0,
            equalities_propagated_to_arith: 0,
            euf_array_notify_parent: HashMap::default(),
            euf_array_notify_replay_edges: Vec::new(),
            euf_array_notify_replay_edge_set: Default::default(),
            imported_euf_array_notify_replay_edges: Vec::new(),
            array_equality_replays: Vec::new(),
            array_equality_replays_seen: DetHashSet::default(),
            array_replay_export_cursor: 0,
            array_replay_pending: Vec::new(),
            array_replay_pending_set: DetHashSet::default(),
            imported_array_equality_replays: Vec::new(),
            cross_theory_equality_replays: Vec::new(),
            cross_replay_endpoint_index: ay_core::kani_compat::DetHashMap::default(),
            cross_replay_index_valid: false,
            cross_replay_cover_scratch: CrossReplayCoverScratch::default(),
            cross_theory_replay_processed: DetHashSet::default(),
            imported_cross_theory_equality_replays: Vec::new(),
            current_assignments: HashMap::default(),
            current_assignment_trail: Vec::new(),
            current_assignment_scope_marks: Vec::new(),
            rescue_pair_counter: None,
            dt_pass: None,
            dt_d1: None,
            dt_d1_verify: None,
            dt_d2: None,
        }
    }

    /// Create a combiner for EUF + LRA + Arrays (replaces AufLraSolver, QF_AUFLRA).
    pub fn auf_lra(terms: &'a TermStore) -> Self {
        let mut lra = LraSolver::new(terms);
        lra.set_combined_theory_mode(true);
        let mut arrays = ArraySolver::new(terms);
        arrays.set_defer_expensive_checks(true);
        arrays.enable_registered_atom_scope(true);
        Self {
            lia_bcp_dirty: true,
            deferred_arith_eqs: Vec::new(),
            a5_replaying: false,
            a5_bounded_vars: DetHashSet::default(),
            a5_deferred_by_var: ay_core::kani_compat::DetHashMap::default(),
            a5_materialized: Vec::new(),
            a5_lazy_arith: std::env::var_os("AY_A5_LAZY_ARITH").is_some(),
            interface_diet: DietMode::from_env(),
            diet_certify_rounds: 0,
            terms,
            euf: EufSolver::new(terms),
            lia: None,
            lra: Some(lra),
            arrays: Some(arrays),
            array_epoch: 0,
            array_quiescent_epoch: None,
            interface: Some(InterfaceBridge::new()),
            scope_depth: 0,
            arrays_bcp_lanes: true,
            label: "AUFLRA",
            arith_prop_label: "AUFLRA-LRA",
            euf_prop_label: "AUFLRA-EUF",
            arr_prop_label: "AUFLRA-ARR",

            interrupt: None,
            deadline: None,
            arm_uflia_congruence_repair: false,
            read_congruence_pairs_enabled: true,

            nelson_oppen_rounds: 0,
            nelson_oppen_max_rounds: 0,
            equalities_propagated_to_euf: 0,
            equalities_propagated_to_arith: 0,
            euf_array_notify_parent: HashMap::default(),
            euf_array_notify_replay_edges: Vec::new(),
            euf_array_notify_replay_edge_set: Default::default(),
            imported_euf_array_notify_replay_edges: Vec::new(),
            array_equality_replays: Vec::new(),
            array_equality_replays_seen: DetHashSet::default(),
            array_replay_export_cursor: 0,
            array_replay_pending: Vec::new(),
            array_replay_pending_set: DetHashSet::default(),
            imported_array_equality_replays: Vec::new(),
            cross_theory_equality_replays: Vec::new(),
            cross_replay_endpoint_index: ay_core::kani_compat::DetHashMap::default(),
            cross_replay_index_valid: false,
            cross_replay_cover_scratch: CrossReplayCoverScratch::default(),
            cross_theory_replay_processed: DetHashSet::default(),
            imported_cross_theory_equality_replays: Vec::new(),
            current_assignments: HashMap::default(),
            current_assignment_trail: Vec::new(),
            current_assignment_scope_marks: Vec::new(),
            rescue_pair_counter: None,
            dt_pass: None,
            dt_d1: None,
            dt_d1_verify: None,
            dt_d2: None,
        }
    }

    /// Set the interrupt flag from the Executor (#8637, #8615).
    ///
    /// When this flag is set to `true`, the Nelson-Oppen fixpoint loop
    /// will exit early with `TheoryResult::Unknown`. The flag is also
    /// forwarded to the array solver (when present) so that array theory
    /// propagation loops can check it cooperatively (#8615).
    pub fn set_interrupt(&mut self, flag: Option<Arc<AtomicBool>>) {
        // #8615: Forward the interrupt flag to the array solver so it can
        // check the flag during long-running propagation loops.
        if let Some(ref f) = flag {
            if let Some(ref mut arrays) = self.arrays {
                arrays.set_interrupt(f.clone());
            }
        }
        self.interrupt = flag;
    }

    /// Set the solve deadline from the Executor (#8642).
    ///
    /// When the current time exceeds this deadline, the Nelson-Oppen
    /// fixpoint loop will exit early with `TheoryResult::Unknown`.
    ///
    /// #lia-deadline-forward: also push the deadline INTO the inner
    /// `LiaSolver` — the N-O loop only polls `is_interrupted()` BETWEEN
    /// theory checks, so without this a single dense `lia.check()` (cascade +
    /// farkas-probe augmentation) runs to its internal iteration limits and
    /// can overshoot the caller's wall budget by whole seconds (the
    /// documented UFLIA lazy-round spin; the bounded hybrid detour burns its
    /// window inside one round). `LiaSolver::should_timeout` polls this at
    /// its cascade checkpoints, so the check exits Unknown at the boundary —
    /// verdict-neutral by construction.
    pub fn set_deadline(&mut self, deadline: Option<Instant>) {
        self.deadline = deadline;
        if let (Some(dl), Some(lia)) = (deadline, self.lia.as_mut()) {
            lia.set_deadline(dl);
        }
    }

    /// #qfax-t3-atom-space: enable/disable the BCP-time arrays lanes
    /// (`propagate` + `check_during_propagate` routing into the ArraySolver).
    /// See the `arrays_bcp_lanes` field docs for the measured evidence and
    /// the soundness shape. The QF_AX solve route (`solve_array_euf`) turns
    /// the lanes OFF except for the storeinv-witness shape, where the
    /// singleton-support steering is load-bearing.
    pub fn set_arrays_bcp_lanes(&mut self, on: bool) {
        self.arrays_bcp_lanes = on;
    }

    /// #uflia-cong-repair-arm: enable/disable the accept-point UF
    /// function-graph consistency scan for this combiner. The Executor sets
    /// this `true` only for the armed re-solve that follows an independent
    /// model-gate refutation of the first-pass UFLIA model; on the fast first
    /// pass it stays `false`.
    pub fn set_arm_uflia_congruence_repair(&mut self, armed: bool) {
        self.arm_uflia_congruence_repair = armed;
    }

    /// #read-congruence-quantified-scope: enable/disable the store-carrying
    /// read-congruence index-pair obligations for this combiner (see the
    /// field doc on `read_congruence_pairs_enabled`). The executor passes
    /// `false` for ground (re-)solves inside the quantifier-instantiation
    /// pipeline and leaves the default `true` everywhere else.
    pub(crate) fn set_read_congruence_pairs_enabled(&mut self, enabled: bool) {
        self.read_congruence_pairs_enabled = enabled;
    }

    /// #probe-subset-cache: opt the inner LIA solver's farkas probe into the
    /// cached-subset-first batch check. Set by the UFLIA hybrid's bounded
    /// lazy DETOUR only (trajectory-owning caller); no-op without LIA.
    pub fn set_probe_subset_cache(&mut self, enabled: bool) {
        if let Some(lia) = self.lia.as_mut() {
            lia.set_probe_subset_cache(enabled);
        }
    }

    /// Mark this combiner as a verdict-only VERIFICATION instance
    /// (#uflia-verify-only).
    ///
    /// Verification callers (`make_verification_combiner` users) inspect only
    /// the `TheoryResult` VARIANT of `check()` and discard conflict payloads.
    /// This flag lets the LIA sub-solver skip its post-verdict shared-reason
    /// augmentation (`augment_farkas_with_shared_reasons`), whose
    /// full-check-per-equality probe loop dominated QF_UFLIA verification
    /// cost. The verdict variant is unchanged — augmentation runs strictly
    /// after the verdict is decided. Never set on production combiners.
    pub(crate) fn set_verify_only(&mut self, verify_only: bool) {
        if let Some(ref mut lia) = self.lia {
            lia.set_verify_only(verify_only);
        }
    }

    /// Register the problem's datatypes, enabling the D0 datatype
    /// clash/acyclicity final-check pass over the EUF e-graph
    /// (`DESIGN_lazy_dt.md` stage D0).
    ///
    /// `datatypes` pairs each datatype's internal name with its constructor
    /// names (the same internal, possibly instance-mangled names the term
    /// store uses — as produced by the frontend's `datatype_iter`). Without
    /// this call the pass is absent and `check()` behaves exactly as before.
    pub fn register_datatypes(&mut self, datatypes: &[(String, Vec<String>)]) {
        if datatypes.is_empty() {
            return;
        }
        let pass = self.dt_pass.get_or_insert_with(ay_dt::DtEgraphPass::new);
        for (dt_name, ctors) in datatypes {
            pass.register_datatype(dt_name, ctors);
        }
    }

    /// Register constructor selector signatures and enable the D1 lazy
    /// tester/selector propagation pass (`DESIGN_lazy_dt.md` stage D1).
    ///
    /// `datatypes` is the same registry passed to
    /// [`Self::register_datatypes`]; `selectors` pairs each constructor's
    /// internal name with its ordered selector names (nullary constructors
    /// have empty lists). Callers opt IN per lane: today only the
    /// `array_euf`/DtAx route (blocksworld's actual routing) calls this, so
    /// every other combined lane keeps its exact pre-D1 behavior. The
    /// `AY_DT_D1=0` environment kill-switch disables the pass entirely.
    pub fn register_datatype_selectors(
        &mut self,
        datatypes: &[(String, Vec<String>)],
        selectors: &[(String, Vec<String>)],
    ) {
        if datatypes.is_empty() || std::env::var_os("AY_DT_D1").is_some_and(|v| v == "0") {
            return;
        }
        let d1 = self.dt_d1.get_or_insert_with(ay_dt::DtLazyPropagator::new);
        for (dt_name, ctors) in datatypes {
            d1.register_datatype(dt_name, ctors);
        }
        for (ctor, sels) in selectors {
            if !sels.is_empty() {
                d1.register_ctor_selectors(ctor, sels);
            }
        }
    }

    /// Run the D1 lazy DT propagation pass (stage D1) and return entailed
    /// tautology implication clauses to inject via `NeedLemmas`.
    ///
    /// `force` skips the merge change-feed gate (used at the Nelson-Oppen
    /// fixpoint, where a candidate model is about to be accepted). Returns an
    /// empty vec when the pass is absent, inert, or nothing new merged.
    pub(super) fn dt_d1_lemmas(&mut self, force: bool) -> Vec<ay_core::TheoryLemma> {
        let Some(d1) = &mut self.dt_d1 else {
            return Vec::new();
        };
        if d1.is_inert() {
            return Vec::new();
        }
        // Consume the change feed only when the pass actually runs: the
        // `wants_rerun` flag tracks emission-cap leftovers separately.
        let dirty = self.euf.take_dt_merge_dirty();
        if !(dirty || force || d1.wants_rerun()) {
            return Vec::new();
        }
        let verifier = self
            .dt_d1_verify
            .get_or_insert_with(|| EufSolver::new(self.terms).verify_only());
        let before = d1.stats().0;
        // Fixpoint (`force`) calls emit only clauses the candidate model
        // VIOLATES: a `NeedLemmas` from the full `check()` costs one
        // split-loop iteration (unlike the inline BCP conduit), so
        // unconditional fixpoint emission burns the split budget into a
        // fail-closed Unknown on instances whose deepening rounds repeatedly
        // reach candidate models.
        let fixpoint_assignments = force.then_some(&self.current_assignments);
        let lemmas = d1.propagate_lemmas(self.terms, &mut self.euf, verifier, fixpoint_assignments);
        if !lemmas.is_empty() && std::env::var_os("AY_PHASE_TRACE").is_some() {
            let (total, failures) = d1.stats();
            // Doubling threshold keeps the trace to ~log2(total) lines.
            if before == 0 || total.leading_zeros() != before.leading_zeros() {
                let (r1, r2, r3) = d1.rule_stats();
                eprintln!(
                    "c phase-trace dt-d1-propagate round_lemmas={} total={} tester_eval={} transfer={} sel_eval={} rederive_failures={} force={}",
                    lemmas.len(),
                    total,
                    r1,
                    r2,
                    r3,
                    failures,
                    force,
                );
            }
        }
        lemmas
    }

    /// Register D2 splitting-on-demand bases and enable the pass
    /// (`DESIGN_lazy_dt.md` stage D2; lazy-lane only).
    ///
    /// `datatypes` is the registry passed to [`Self::register_datatypes`]
    /// with an extra all-nullary marker; `bases` pairs each enum-sorted term
    /// with its complete, declaration-ordered `(= t Cj)` atom family (the
    /// executor materializes the atoms — the theory cannot create terms).
    /// Every base is structurally re-validated inside the pass; malformed
    /// bases are rejected fail-closed. The `AY_DT_D2=0` environment
    /// kill-switch disables the pass entirely.
    pub fn register_datatype_splits(
        &mut self,
        datatypes: &[(String, Vec<String>, bool)],
        bases: &[(TermId, Vec<TermId>)],
    ) {
        if datatypes.is_empty()
            || bases.is_empty()
            || std::env::var_os("AY_DT_D2").is_some_and(|v| v == "0")
        {
            return;
        }
        let d2 = self.dt_d2.get_or_insert_with(ay_dt::DtSplitOnDemand::new);
        for (dt_name, ctors, all_nullary) in datatypes {
            d2.register_datatype(dt_name, ctors, *all_nullary);
        }
        for (t, atoms) in bases {
            d2.register_base(self.terms, *t, atoms);
        }
    }

    /// Run the D2 splitting-on-demand pass at the Nelson-Oppen fixpoint and
    /// return domain-closure split clauses to inject via `NeedLemmas`.
    ///
    /// Empty when the pass is absent/inert or every base is committed or
    /// candidate-satisfied. Each clause is an unconditional datatype
    /// exhaustiveness tautology (validated at registration), so injection
    /// can only prune models that violate datatype semantics.
    pub(super) fn dt_d2_lemmas(&mut self) -> Vec<ay_core::TheoryLemma> {
        let Some(d2) = &mut self.dt_d2 else {
            return Vec::new();
        };
        if d2.is_inert() {
            return Vec::new();
        }
        let lemmas = d2.fixpoint_splits(self.terms, &mut self.euf, &self.current_assignments);
        if !lemmas.is_empty() && std::env::var_os("AY_PHASE_TRACE").is_some() {
            let (bases, total, rejected) = d2.stats();
            eprintln!(
                "c phase-trace dt-d2-split round_lemmas={} bases={} total={} rejected_bases={}",
                lemmas.len(),
                bases,
                total,
                rejected,
            );
        }
        lemmas
    }

    /// Set the persistent per-pair rescue counter (#6367).
    ///
    /// When present, `try_array_rescue_on_arith_conflict` consults this
    /// counter to avoid re-rescuing the same `(lhs, rhs)` model-equality pair
    /// more than `DEFAULT_RESCUE_PAIR_BUDGET` times, which would otherwise
    /// loop for up to `_ITP_MAX_REFINEMENTS` iterations with no progress on
    /// `qf_auflia_array_sum_bound`-style inputs.
    ///
    /// The counter is owned by the split-loop pipeline state (see
    /// `combined/mod.rs`); this setter wires a fresh `TheoryCombiner` to
    /// that shared counter on every outer refinement iteration.
    pub(crate) fn set_rescue_pair_counter(
        &mut self,
        counter: Option<crate::executor::SharedRescuePairCounter>,
    ) {
        self.rescue_pair_counter = counter;
    }

    /// Check whether the interrupt flag is set or the deadline has passed.
    pub(super) fn is_interrupted(&self) -> bool {
        if let Some(ref flag) = self.interrupt {
            if flag.load(Ordering::Relaxed) {
                return true;
            }
        }
        if let Some(deadline) = self.deadline {
            if Instant::now() >= deadline {
                return true;
            }
        }
        false
    }

    // Model extraction and LIA state preservation: see combiner_models.rs

    // Private N-O check helpers: see combiner_check.rs
    // (evaluate_bridge, handle_fixpoint, propagate_array_indices, etc.)

    /// Check if a term is tracked as an interface arithmetic term.
    #[cfg(test)]
    pub(crate) fn has_interface_term(&self, term: TermId) -> bool {
        self.interface
            .as_ref()
            .is_some_and(|ib| ib.contains_arith_term(&term))
    }

    pub(super) fn mark_arrays_dirty(&mut self) {
        if self.arrays.is_some() {
            self.array_epoch = self.array_epoch.wrapping_add(1);
            self.array_quiescent_epoch = None;
        }
    }

    fn suggest_phase_with_arrays(&self, atom: TermId) -> Option<bool> {
        if let TermData::App(ref sym, ref args) = self.terms.get(atom) {
            if sym.name() == "=" && args.len() == 2 {
                if matches!(self.terms.sort(args[0]), Sort::Array(_)) {
                    return None;
                }
                let lhs_is_simple = !is_select_or_store(self.terms, args[0]);
                let rhs_is_simple = !is_select_or_store(self.terms, args[1]);
                if lhs_is_simple && rhs_is_simple {
                    return Some(false);
                }
            }
        }
        if let TermData::App(ref sym, ref args) = self.terms.get(atom) {
            let name = sym.name();
            if (name == "<=" || name == ">=" || name == "<" || name == ">")
                && args.len() == 2
                && (arg_involves_select_or_store(self.terms, args[0])
                    || arg_involves_select_or_store(self.terms, args[1]))
            {
                return None;
            }
        }
        if let Some(lia) = &self.lia {
            return lia.suggest_phase(atom);
        }
        if let Some(lra) = &self.lra {
            return lra.suggest_phase(atom);
        }
        None
    }
}

// #8594: Array dedup set persistence for the non-persistent eager arm.
//
// The non-persistent eager split loop creates a fresh TheoryCombiner each
// iteration. Without persisting the array solver's dedup sets, the same
// interface/model equalities are re-requested every iteration, exhausting
// the round budget without progress. These methods export/import the dedup
// sets so the split loop can carry them across theory instances.
impl TheoryCombiner<'_> {
    /// Collect the Int-sorted VARIABLE leaves of a literal (bounded walk),
    /// for A5 relevance tracking (#qfuflia-a5).
    fn a5_int_leaf_vars(terms: &TermStore, root: TermId, out: &mut Vec<TermId>) {
        let mut stack = vec![root];
        let mut seen = 0usize;
        while let Some(t) = stack.pop() {
            seen += 1;
            if seen > 256 {
                break;
            }
            match terms.get(t) {
                TermData::Var(_, _) => {
                    if matches!(terms.sort(t), Sort::Int) && !out.contains(&t) {
                        out.push(t);
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
    }

    /// Reason-set subset test. Both slices are SORTED by `(term, value)` and
    /// deduplicated — `EufArrayNotifyReplayEdge::new` is the only constructor
    /// and enforces it — so this is a linear merge instead of the former
    /// O(|lhs| x |rhs|) `Vec::contains` scan (#alia-notify-replay-index: the
    /// covered-by reachability below was ~100% of solver time on the QF_ALIA
    /// cs_lazy.i_* family, dominated by exactly this test; same disease and
    /// same cure as #qfuflia-replay-index below).
    #[cfg(test)]
    fn euf_array_notify_reason_subset(lhs: &[TheoryLit], rhs: &[TheoryLit]) -> bool {
        if lhs.len() > rhs.len() {
            return false;
        }
        let mut i = 0usize;
        for lit in rhs {
            if i == lhs.len() {
                break;
            }
            match (lhs[i].term.0, lhs[i].value).cmp(&(lit.term.0, lit.value)) {
                std::cmp::Ordering::Equal => i += 1,
                std::cmp::Ordering::Less => return false,
                std::cmp::Ordering::Greater => {}
            }
        }
        i == lhs.len()
    }

    /// Reason-set subset test. Both slices are SORTED by `(term, value)` and
    /// deduplicated — `CrossTheoryEqualityReplay::new` is the only constructor
    /// and enforces it — so this is a linear merge instead of the former
    /// O(|lhs| x |rhs|) `Vec::contains` scan (#qfuflia-replay-index: the
    /// covered-by reachability below was ~24% of thread time on the numeric
    /// QF_UFLIA families, dominated by exactly this test).
    fn cross_theory_replay_reason_subset(lhs: &[TheoryLit], rhs: &[TheoryLit]) -> bool {
        if lhs.len() > rhs.len() {
            return false;
        }
        let mut i = 0usize;
        for lit in rhs {
            if i == lhs.len() {
                break;
            }
            match (lhs[i].term.0, lhs[i].value).cmp(&(lit.term.0, lit.value)) {
                std::cmp::Ordering::Equal => i += 1,
                // lhs[i] sorts before the current rhs element, so it can no
                // longer appear in the (sorted) remainder: not a subset.
                std::cmp::Ordering::Less => return false,
                std::cmp::Ordering::Greater => {}
            }
        }
        i == lhs.len()
    }

    /// Minimal-insert of a cross-theory equality replay against a caller-owned
    /// endpoint index + tombstone array (#qfuflia-replay-index v3; used by the
    /// export/import path AND, since the 2026-07-12 reprofile, the replay
    /// intake path). Semantics-identical to the retired non-indexed twin:
    /// same covered-by answer (via `covered_by_indexed`, proven equivalent on
    /// the intake path), same dominated same-pair removal (tombstoned instead
    /// of compacted; the caller compacts once at the end, preserving relative
    /// order exactly like `Vec::retain`).
    fn insert_cross_theory_equality_replay_minimal_indexed(
        replays: &mut Vec<CrossTheoryEqualityReplay>,
        by_endpoint: &mut ay_core::kani_compat::DetHashMap<TermId, Vec<usize>>,
        removed: &mut Vec<bool>,
        cover_scratch: &mut CrossReplayCoverScratch,
        candidate: CrossTheoryEqualityReplay,
    ) -> bool {
        if candidate.reason.is_empty()
            || Self::cross_theory_equality_replay_covered_by_indexed(
                replays,
                by_endpoint,
                removed,
                cover_scratch,
                &candidate,
            )
        {
            return false;
        }

        // Tombstone same-pair replays whose reason is a superset of the
        // candidate's (the candidate strictly dominates them). Any same-pair
        // replay is incident to `candidate.lhs`, so the lhs bucket finds all.
        if let Some(indices) = by_endpoint.get(&candidate.lhs) {
            for &idx in indices {
                if removed[idx] {
                    continue;
                }
                let existing = &replays[idx];
                if existing.same_pair(&candidate)
                    && Self::cross_theory_replay_reason_subset(&candidate.reason, &existing.reason)
                {
                    removed[idx] = true;
                }
            }
        }
        let new_idx = replays.len();
        by_endpoint.entry(candidate.lhs).or_default().push(new_idx);
        by_endpoint.entry(candidate.rhs).or_default().push(new_idx);
        replays.push(candidate);
        removed.push(false);
        true
    }

    /// Drop tombstoned slots, preserving order (`Vec::retain` semantics).
    fn compact_cross_theory_equality_replays(
        replays: &mut Vec<CrossTheoryEqualityReplay>,
        removed: &[bool],
    ) {
        if removed.iter().any(|&r| r) {
            let mut keep = removed.iter();
            replays.retain(|_| !*keep.next().expect("tombstone vec tracks replays 1:1"));
        }
    }

    fn prune_cross_theory_equality_replay_vec(
        replays: &mut Vec<CrossTheoryEqualityReplay>,
        mut keep: impl FnMut(&CrossTheoryEqualityReplay) -> bool,
    ) {
        let mut retained = std::mem::take(replays);
        retained.sort_by_key(|replay| (replay.reason.len(), replay.lhs.0, replay.rhs.0));
        // #qfuflia-replay-index v3 on the export/import path: one endpoint
        // index for the whole pass instead of an O(|replays|) rebuild per
        // candidate inside the non-indexed `insert_minimal` (that rebuild was
        // Θ(re-entries × persistent²) on QF_ALIA pointer-safe-N, ~82% of
        // on-CPU samples — 2026-07-12 profile).
        let mut by_endpoint: ay_core::kani_compat::DetHashMap<TermId, Vec<usize>> =
            Default::default();
        let mut removed: Vec<bool> = Vec::new();
        let mut cover_scratch = CrossReplayCoverScratch::default();
        for replay in retained {
            if keep(&replay) {
                Self::insert_cross_theory_equality_replay_minimal_indexed(
                    replays,
                    &mut by_endpoint,
                    &mut removed,
                    &mut cover_scratch,
                    replay,
                );
            }
        }
        Self::compact_cross_theory_equality_replays(replays, &removed);
    }

    /// Returns true when already-retained replay edges connect the candidate
    /// endpoints using only reasons that are a subset of the candidate reason.
    /// Then whenever the candidate could replay, the retained path can replay
    /// too, so persisting the candidate would only add a redundant cycle.
    #[cfg(test)]
    pub(crate) fn euf_array_notify_replay_edge_covered_by(
        edges: &[EufArrayNotifyReplayEdge],
        candidate: &EufArrayNotifyReplayEdge,
    ) -> bool {
        let mut index = EufArrayNotifyEdgeIndex::build(edges);
        Self::euf_array_notify_replay_edge_covered_by_indexed(edges, &mut index, candidate)
    }

    /// #alia-notify-replay-index: index edges by endpoint WITHOUT any reason
    /// test (cheap pointer pushes), then test reason-subset eligibility
    /// LAZILY, only for edges incident to terms the DFS actually visits.
    /// The former implementation re-scanned the ENTIRE edge vector per
    /// visited node with an O(r^2) subset test and a `Vec::contains` seen
    /// set — O(E^2 x V x r^2) per outer AUFLIA round, 100% of solver samples
    /// on QF_ALIA cs_lazy.i_6 (2026-07-11 profile). Semantics-identical:
    /// same reachability question, same boolean answer.
    #[cfg(test)]
    fn euf_array_notify_replay_edge_covered_by_indexed(
        edges: &[EufArrayNotifyReplayEdge],
        index: &mut EufArrayNotifyEdgeIndex,
        candidate: &EufArrayNotifyReplayEdge,
    ) -> bool {
        #[cfg(debug_assertions)]
        let reference = (edges.len() <= 32)
            .then(|| Self::euf_array_notify_replay_edge_covered_by_reference(edges, candidate));
        #[cfg(debug_assertions)]
        macro_rules! checked_return {
            ($answer:expr) => {{
                let answer: bool = $answer;
                debug_assert!(
                    reference.is_none() || reference == Some(answer),
                    "indexed covered_by diverged from reference implementation"
                );
                return answer;
            }};
        }
        #[cfg(not(debug_assertions))]
        macro_rules! checked_return {
            ($answer:expr) => {
                return $answer
            };
        }

        if candidate.target == candidate.source {
            checked_return!(true);
        }
        // A retained edge with the same endpoints and reason ⊆ candidate's
        // covers the candidate by itself; the exact-duplicate fast path
        // catches the overwhelmingly common re-export case without a DFS.
        if index.dedup.contains(candidate) {
            checked_return!(true);
        }

        // Epoch-stamped reusable scratch: a fresh epoch invalidates all
        // previous `eligible` cache entries and `seen` marks without any
        // O(E)/O(V) clearing or per-candidate allocation.
        index.epoch = index.epoch.wrapping_add(1);
        if index.epoch == 0 {
            index.eligible_epoch.iter_mut().for_each(|e| *e = u32::MAX);
            index.seen.clear();
            index.epoch = 1;
        }
        let epoch = index.epoch;
        if index.eligible_epoch.len() < edges.len() {
            let filler = epoch.wrapping_sub(1);
            index.eligible_epoch.resize(edges.len(), filler);
            index.eligible_value.resize(edges.len(), false);
        }

        let EufArrayNotifyEdgeIndex {
            by_endpoint,
            eligible_epoch,
            eligible_value,
            seen,
            stack,
            ..
        } = index;
        stack.clear();
        stack.push(candidate.target);
        while let Some(term) = stack.pop() {
            if seen.insert(term, epoch) == Some(epoch) {
                continue;
            }
            if term == candidate.source {
                checked_return!(true);
            }
            if let Some(indices) = by_endpoint.get(&term) {
                for &idx in indices {
                    let edge = &edges[idx];
                    let ok = if eligible_epoch[idx] == epoch {
                        eligible_value[idx]
                    } else {
                        let ok =
                            Self::euf_array_notify_reason_subset(&edge.reason, &candidate.reason);
                        eligible_epoch[idx] = epoch;
                        eligible_value[idx] = ok;
                        ok
                    };
                    if !ok {
                        continue;
                    }
                    let next = if edge.target == term {
                        edge.source
                    } else {
                        edge.target
                    };
                    stack.push(next);
                }
            }
        }
        checked_return!(false)
    }

    /// The pre-#alia-notify-replay-index implementation, kept only as a
    /// debug-build oracle for small inputs (see `checked_return!` above).
    #[cfg(all(test, debug_assertions))]
    fn euf_array_notify_replay_edge_covered_by_reference(
        edges: &[EufArrayNotifyReplayEdge],
        candidate: &EufArrayNotifyReplayEdge,
    ) -> bool {
        if candidate.target == candidate.source {
            return true;
        }
        let mut stack = vec![candidate.target];
        let mut seen = Vec::new();
        while let Some(term) = stack.pop() {
            if seen.contains(&term) {
                continue;
            }
            if term == candidate.source {
                return true;
            }
            seen.push(term);
            for edge in edges {
                if !edge.reason.iter().all(|lit| candidate.reason.contains(lit)) {
                    continue;
                }
                if edge.target == term {
                    stack.push(edge.source);
                } else if edge.source == term {
                    stack.push(edge.target);
                }
            }
        }
        false
    }

    pub(crate) fn prune_current_euf_array_notify_replay_edges(
        &self,
        edges: &mut Vec<EufArrayNotifyReplayEdge>,
    ) {
        // #no-replay-quadratic M2 (superset retention): validity filter +
        // exact-duplicate dedup only — NO covered-by transitive-reduction
        // BFS. The covered-by pass over the retained set every round was
        // O(retained x BFS); on cs_lazy.i_6 a single giant merged component
        // pushes the set to ~87k edges, and an instrumented run showed the
        // BFS rejecting ZERO of 87,283 fresh candidates while consuming 100%
        // of solver samples. Dropping it can only retain MORE edges (a
        // superset): replaying a redundant edge re-asserts an equality whose
        // reasons hold — a true fact the covered path would have derived
        // anyway — so no needed replay is ever dropped and no wrong verdict
        // is possible; the cost is memory plus O(alpha) no-op union-find
        // merges at replay.
        let mut retained = std::mem::take(edges);
        retained.sort_by_key(|edge| (edge.reason.len(), edge.target.0, edge.source.0));
        let mut seen: DetHashSet<EufArrayNotifyReplayEdge> = Default::default();
        for edge in retained {
            if edge.target != edge.source
                && self.euf_array_notify_replay_edge_reasons_hold(&edge)
                && seen.insert(edge.clone())
            {
                edges.push(edge);
            }
        }
    }

    pub(crate) fn append_current_euf_array_notify_replay_edges(
        &self,
        edges: &mut Vec<EufArrayNotifyReplayEdge>,
    ) -> usize {
        let mut exported_edges = self.export_euf_array_notify_replay_edges();
        let exported_count = exported_edges.len();
        exported_edges.sort_by_key(|edge| (edge.reason.len(), edge.target.0, edge.source.0));
        // #no-replay-quadratic M2 (superset retention): exact-duplicate
        // hash dedup against the persistent set instead of a covered-by BFS
        // per candidate — see `prune_current_euf_array_notify_replay_edges`
        // for the measurements and the superset soundness argument.
        let mut seen: DetHashSet<EufArrayNotifyReplayEdge> = edges.iter().cloned().collect();
        for edge in exported_edges {
            if edge.target != edge.source
                && self.euf_array_notify_replay_edge_reasons_hold(&edge)
                && seen.insert(edge.clone())
            {
                edges.push(edge);
            }
        }
        exported_count
    }

    pub(super) fn record_current_assignment(&mut self, literal: TermId, value: bool) {
        let (term, value) = ay_core::unwrap_not(self.terms, literal, value);
        let previous = self.current_assignments.insert(term, value);
        self.current_assignment_trail.push((term, previous));
    }

    pub(super) fn restore_current_assignments_to_mark(&mut self, mark: usize) {
        while self.current_assignment_trail.len() > mark {
            let (term, previous) = self
                .current_assignment_trail
                .pop()
                .expect("assignment trail length checked above");
            match previous {
                Some(value) => {
                    self.current_assignments.insert(term, value);
                }
                None => {
                    self.current_assignments.remove(&term);
                }
            }
        }
    }

    pub(super) fn clear_current_assignments(&mut self) {
        self.current_assignments.clear();
        self.current_assignment_trail.clear();
        self.current_assignment_scope_marks.clear();
    }

    /// Deterministic digest of the combiner's ASSIGNMENT-DERIVED state
    /// (LAZY-M3-PERSISTENT-COMBINER-BLUEPRINT §3.2 / §3.3(b) debug oracle).
    ///
    /// Weighted additive fold over exactly the state that `soft_reset` /
    /// `soft_reset_warm` return to the fresh-empty value: the combiner-boundary
    /// current-assignment trail + the EUF->array notification parent map + the
    /// EUF sub-solver's own Nelson-Oppen carry (via
    /// [`EufSolver::assignment_derived_digest`]). The fold is `0` iff all of
    /// that state is empty, so after a warm reset this MUST return `0` — equal
    /// to a freshly-constructed combiner. A non-zero value means a §3.2 undo was
    /// dropped (a stale speculative merge / propagation leaked across the
    /// reset), which is the wrong-`sat` vector this milestone must exclude.
    ///
    /// SCOPE (honest limitation): this digests the *assignment-derived* leak
    /// surface at the combiner + EUF boundary — the part the invariant requires
    /// to equal a *bare* fresh combiner. It does NOT digest retained STRUCTURAL
    /// state (e-graph node set, interface registrations, the six replay sets):
    /// that state legitimately differs from a bare-fresh combiner and only
    /// matches `fresh + import_structural_snapshot + pre_theory_import`. The
    /// end-to-end verdict-equivalence oracle (create-once warm-reset vs fresh,
    /// same asserted trail) covers the retained-structural half.
    ///
    /// Compiled in all builds (not `cfg`-gated) because `soft_reset_warm`'s
    /// `debug_assert_eq!` references it; it is only *executed* in debug builds.
    pub(super) fn assignment_derived_digest(&self) -> u64 {
        self.euf
            .assignment_derived_digest()
            .wrapping_add((self.current_assignments.len() as u64).wrapping_mul(0x2545F491))
            .wrapping_add((self.current_assignment_trail.len() as u64).wrapping_mul(0x1D8E4E27))
            .wrapping_add(
                (self.current_assignment_scope_marks.len() as u64).wrapping_mul(0x3C6EF372),
            )
            .wrapping_add((self.euf_array_notify_parent.len() as u64).wrapping_mul(0xA54FF53A))
            .wrapping_add((self.scope_depth as u64).wrapping_mul(0x510E527F))
    }

    pub(super) fn current_reasons_hold(&self, reason: &[TheoryLit]) -> bool {
        !reason.is_empty()
            && reason
                .iter()
                .all(|lit| self.current_assignments.get(&lit.term) == Some(&lit.value))
    }

    pub(super) fn array_equality_replay_is_valid(
        &self,
        replay: &ArrayPropagatedEqualityReplay,
    ) -> bool {
        replay.reason.is_empty() || self.current_reasons_hold(&replay.reason)
    }

    pub(super) fn record_euf_array_notify_replay_edge(
        &mut self,
        target: TermId,
        source: TermId,
        reason: Vec<TheoryLit>,
    ) {
        if reason.is_empty() {
            return;
        }
        let edge = EufArrayNotifyReplayEdge::new(target, source, reason);
        // O(1) hash-set dedup (#no-replay-quadratic M2); the former
        // `Vec::contains` was quadratic within a round (~87k edges recorded
        // by one giant merged component on cs_lazy.i_6, 2026-07-12 count).
        if self.euf_array_notify_replay_edge_set.insert(edge.clone()) {
            self.euf_array_notify_replay_edges.push(edge);
        }
    }

    fn direct_array_equality_assignment(
        &self,
        literal: TermId,
        value: bool,
    ) -> Option<(TermId, TermId, TheoryLit)> {
        let (term, value) = ay_core::unwrap_not(self.terms, literal, value);
        if !value {
            return None;
        }
        let TermData::App(sym, args) = self.terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        if !matches!(self.terms.sort(args[0]), Sort::Array(_))
            || !matches!(self.terms.sort(args[1]), Sort::Array(_))
        {
            return None;
        }
        Some((args[0], args[1], TheoryLit::new(term, true)))
    }

    fn current_true_equality_lit(&self, lhs: TermId, rhs: TermId) -> Option<TheoryLit> {
        if lhs == rhs || self.terms.sort(lhs) != self.terms.sort(rhs) {
            return None;
        }
        let eq = self.terms.find_eq(lhs, rhs)?;
        (self.current_assignments.get(&eq) == Some(&true)).then_some(TheoryLit::new(eq, true))
    }

    pub(super) fn current_structural_congruence_reason(
        &self,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<Vec<TheoryLit>> {
        let mut reason = Vec::new();
        let mut visiting = Vec::new();
        if self.collect_current_structural_congruence_reason(
            lhs,
            rhs,
            128,
            &mut visiting,
            &mut reason,
        ) && !reason.is_empty()
        {
            reason.sort_by_key(|lit| (lit.term.0, lit.value));
            reason.dedup_by_key(|lit| (lit.term, lit.value));
            Some(reason)
        } else {
            None
        }
    }

    fn collect_current_structural_congruence_reason(
        &self,
        lhs: TermId,
        rhs: TermId,
        depth_left: usize,
        visiting: &mut Vec<(TermId, TermId)>,
        reason: &mut Vec<TheoryLit>,
    ) -> bool {
        if lhs == rhs {
            return true;
        }
        if self.terms.sort(lhs) != self.terms.sort(rhs) || depth_left == 0 {
            return false;
        }
        if let Some(lit) = self.current_true_equality_lit(lhs, rhs) {
            reason.push(lit);
            return true;
        }

        let pair = if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) };
        if visiting.contains(&pair) {
            return true;
        }

        let (lhs_sym, lhs_args) = match self.terms.get(lhs) {
            TermData::App(sym, args) => (sym, args),
            _ => return false,
        };
        let (rhs_sym, rhs_args) = match self.terms.get(rhs) {
            TermData::App(sym, args) => (sym, args),
            _ => return false,
        };
        if lhs_sym != rhs_sym || lhs_args.len() != rhs_args.len() {
            return false;
        }

        visiting.push(pair);
        let ok = lhs_args.iter().zip(rhs_args.iter()).all(|(&left, &right)| {
            self.collect_current_structural_congruence_reason(
                left,
                right,
                depth_left - 1,
                visiting,
                reason,
            )
        });
        visiting.pop();
        ok
    }

    fn record_euf_array_notify_parent_edge(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: Vec<TheoryLit>,
    ) -> bool {
        let lhs_root = Self::array_notify_find(&mut self.euf_array_notify_parent, lhs);
        let rhs_root = Self::array_notify_find(&mut self.euf_array_notify_parent, rhs);
        if lhs_root == rhs_root {
            return false;
        }

        let (target, source) = if lhs_root.0 <= rhs_root.0 {
            (lhs_root, rhs_root)
        } else {
            (rhs_root, lhs_root)
        };
        self.euf_array_notify_parent.insert(source, target);
        self.record_euf_array_notify_replay_edge(target, source, reason);
        true
    }

    pub(crate) fn export_euf_array_notify_replay_edges(&self) -> Vec<EufArrayNotifyReplayEdge> {
        self.euf_array_notify_replay_edges.clone()
    }

    pub(crate) fn euf_array_notify_replay_edge_reasons_hold(
        &self,
        edge: &EufArrayNotifyReplayEdge,
    ) -> bool {
        self.current_reasons_hold(&edge.reason)
    }

    pub(crate) fn import_euf_array_notify_replay_edges(
        &mut self,
        edges: &[EufArrayNotifyReplayEdge],
    ) {
        self.imported_euf_array_notify_replay_edges = edges.to_vec();
    }

    pub(crate) fn export_array_equality_replays(&self) -> Vec<ArrayPropagatedEqualityReplay> {
        let mut replays = self.array_equality_replays.clone();
        if let Some(arrays) = &self.arrays {
            // Hash-set dedup; the former `Vec::contains` was O(sent x kept)
            // per export call. Same membership predicate, same order.
            let mut seen: DetHashSet<ArrayPropagatedEqualityReplay> =
                replays.iter().cloned().collect();
            for replay in arrays.export_sent_equality_replays() {
                if seen.insert(replay.clone()) {
                    replays.push(replay);
                }
            }
        }
        replays
    }

    pub(crate) fn export_cross_theory_equality_replays(&self) -> Vec<CrossTheoryEqualityReplay> {
        self.cross_theory_equality_replays.clone()
    }

    pub(crate) fn import_cross_theory_equality_replays(
        &mut self,
        replays: &[CrossTheoryEqualityReplay],
    ) {
        self.imported_cross_theory_equality_replays = replays.to_vec();
        Self::prune_cross_theory_equality_replay_vec(
            &mut self.imported_cross_theory_equality_replays,
            |_| true,
        );
    }

    pub(crate) fn import_array_equality_replays(
        &mut self,
        replays: &[ArrayPropagatedEqualityReplay],
    ) {
        self.imported_array_equality_replays = replays.to_vec();
        let valid: DetHashSet<_> = replays
            .iter()
            .filter(|replay| self.array_equality_replay_is_valid(replay))
            .cloned()
            .collect();
        if !valid.is_empty() {
            self.import_array_sent_equality_replays(&valid);
        }
    }

    pub(super) fn cross_theory_equality_replay_is_valid(
        &self,
        replay: &CrossTheoryEqualityReplay,
    ) -> bool {
        self.current_reasons_hold(&replay.reason)
    }

    pub(super) fn record_cross_theory_equalities(&mut self, equalities: &[DiscoveredEquality]) {
        // #qfuflia-replay-index v3: PERSISTENT endpoint index over the
        // retained replays. `insert_minimal` rebuilt its coverage view
        // O(replays) per candidate; on instances whose merged array classes
        // discover thousands of equalities per Nelson-Oppen round against
        // thousands of retained replays (QF_ALIA cs_lazy.i_*), that rebuild
        // was >95% of the solve (2026-07-11 sample profile). The index maps
        // term -> replay slots, is extended incrementally on insert, and is
        // rebuilt only after compaction or an external mutation
        // (`cross_replay_index_valid`). Semantics are identical to
        // per-candidate `insert_cross_theory_equality_replay_minimal`.
        if !self.cross_replay_index_valid {
            self.cross_replay_endpoint_index.clear();
            for (idx, replay) in self.cross_theory_equality_replays.iter().enumerate() {
                self.cross_replay_endpoint_index
                    .entry(replay.lhs)
                    .or_default()
                    .push(idx);
                self.cross_replay_endpoint_index
                    .entry(replay.rhs)
                    .or_default()
                    .push(idx);
            }
            self.cross_replay_index_valid = true;
        }
        let mut removed: Vec<bool> = vec![false; self.cross_theory_equality_replays.len()];
        let mut mutated = false;

        for eq in equalities {
            let mut reason = eq.reason.clone();
            reason.sort_by_key(|lit| (lit.term.0, lit.value));
            reason.dedup_by_key(|lit| (lit.term, lit.value));
            if reason.is_empty() {
                let Some(structural_reason) =
                    self.current_structural_congruence_reason(eq.lhs, eq.rhs)
                else {
                    continue;
                };
                reason = structural_reason;
            }
            let replay = CrossTheoryEqualityReplay::new(eq.lhs, eq.rhs, reason);
            if self.cross_theory_equality_replay_is_valid(&replay) {
                // #qfuflia-replay-memo: a canonical replay already routed through
                // `insert_minimal` since the last reset re-inserts as a no-op
                // (coverage over `cross_theory_equality_replays` is monotone
                // between resets — see the field doc). Skip it BEFORE the
                // `covered_by` BFS; the memo hit rate is >98% on FSet-heavy
                // QF_UFLIA. The `is_valid` (reason-currently-holds) gate stays
                // ABOVE the memo so a replay whose reason no longer holds is
                // never suppressed.
                if self.cross_theory_replay_processed.contains(&replay) {
                    continue;
                }
                self.cross_theory_replay_processed.insert(replay.clone());

                if replay.reason.is_empty()
                    || Self::cross_theory_equality_replay_covered_by_indexed(
                        &self.cross_theory_equality_replays,
                        &self.cross_replay_endpoint_index,
                        &removed,
                        &mut self.cross_replay_cover_scratch,
                        &replay,
                    )
                {
                    continue;
                }
                // Tombstone same-pair replays whose reason is a superset of
                // the candidate's (the candidate strictly dominates them).
                if let Some(indices) = self.cross_replay_endpoint_index.get(&replay.lhs) {
                    for &idx in indices {
                        if removed[idx] {
                            continue;
                        }
                        let existing = &self.cross_theory_equality_replays[idx];
                        if existing.same_pair(&replay)
                            && Self::cross_theory_replay_reason_subset(
                                &replay.reason,
                                &existing.reason,
                            )
                        {
                            removed[idx] = true;
                            mutated = true;
                        }
                    }
                }
                let new_idx = self.cross_theory_equality_replays.len();
                self.cross_replay_endpoint_index
                    .entry(replay.lhs)
                    .or_default()
                    .push(new_idx);
                self.cross_replay_endpoint_index
                    .entry(replay.rhs)
                    .or_default()
                    .push(new_idx);
                self.cross_theory_equality_replays.push(replay);
                removed.push(false);
            }
        }

        if mutated {
            let mut keep = removed.iter();
            self.cross_theory_equality_replays
                .retain(|_| !*keep.next().expect("tombstone vec tracks replays 1:1"));
            // Compaction shifted slots; rebuild lazily on the next batch.
            self.cross_replay_index_valid = false;
        }
    }

    /// `cross_theory_equality_replay_covered_by` over a prebuilt endpoint
    /// index with tombstones (#qfuflia-replay-index v3). Reason-subset
    /// eligibility is tested lazily, only for edges incident to BFS-visited
    /// terms.
    fn cross_theory_equality_replay_covered_by_indexed(
        replays: &[CrossTheoryEqualityReplay],
        by_endpoint: &ay_core::kani_compat::DetHashMap<TermId, Vec<usize>>,
        removed: &[bool],
        scratch: &mut CrossReplayCoverScratch,
        candidate: &CrossTheoryEqualityReplay,
    ) -> bool {
        super::theory_stats::inc_replay_covered_by_calls();
        // Debug-build reference oracle: for small replay sets, cross-check the
        // epoch-stamped DFS answer against the naive full-scan reachability
        // (#qfuflia-replay-cover-scratch), mirroring the notify sibling's
        // `checked_return!` discipline.
        #[cfg(debug_assertions)]
        let reference = (replays.len() <= 32).then(|| {
            Self::cross_theory_equality_replay_covered_by_reference(replays, removed, candidate)
        });
        #[cfg(debug_assertions)]
        macro_rules! checked_return {
            ($answer:expr) => {{
                let answer: bool = $answer;
                debug_assert!(
                    reference.is_none() || reference == Some(answer),
                    "indexed cross-theory covered_by diverged from reference implementation"
                );
                return answer;
            }};
        }
        #[cfg(not(debug_assertions))]
        macro_rules! checked_return {
            ($answer:expr) => {
                return $answer
            };
        }

        if candidate.lhs == candidate.rhs {
            checked_return!(true);
        }

        // Epoch-stamped reusable scratch: a fresh epoch invalidates all prior
        // `eligible` cache entries and `seen` marks with NO O(E)/O(V) clearing
        // and NO per-call allocation (kills the former `reserve_rehash`).
        scratch.epoch = scratch.epoch.wrapping_add(1);
        if scratch.epoch == 0 {
            scratch
                .eligible_epoch
                .iter_mut()
                .for_each(|e| *e = u32::MAX);
            scratch.seen.clear();
            scratch.epoch = 1;
        }
        let epoch = scratch.epoch;
        if scratch.eligible_epoch.len() < replays.len() {
            let filler = epoch.wrapping_sub(1);
            scratch.eligible_epoch.resize(replays.len(), filler);
            scratch.eligible_value.resize(replays.len(), false);
        }

        let CrossReplayCoverScratch {
            eligible_epoch,
            eligible_value,
            seen,
            stack,
            ..
        } = scratch;
        stack.clear();
        stack.push(candidate.lhs);
        while let Some(term) = stack.pop() {
            if seen.insert(term, epoch) == Some(epoch) {
                continue;
            }
            if term == candidate.rhs {
                checked_return!(true);
            }
            if let Some(indices) = by_endpoint.get(&term) {
                for &idx in indices {
                    if removed[idx] {
                        continue;
                    }
                    let replay = &replays[idx];
                    let ok = if eligible_epoch[idx] == epoch {
                        eligible_value[idx]
                    } else {
                        let ok = Self::cross_theory_replay_reason_subset(
                            &replay.reason,
                            &candidate.reason,
                        );
                        eligible_epoch[idx] = epoch;
                        eligible_value[idx] = ok;
                        ok
                    };
                    if !ok {
                        continue;
                    }
                    stack.push(if replay.lhs == term {
                        replay.rhs
                    } else {
                        replay.lhs
                    });
                }
            }
        }
        checked_return!(false)
    }

    /// Naive full-scan reachability, kept only as a debug-build oracle for
    /// `cross_theory_equality_replay_covered_by_indexed` on small inputs
    /// (#qfuflia-replay-cover-scratch). Independent of the endpoint index and
    /// the epoch scratch, so a divergence flags a bug in either.
    #[cfg(debug_assertions)]
    fn cross_theory_equality_replay_covered_by_reference(
        replays: &[CrossTheoryEqualityReplay],
        removed: &[bool],
        candidate: &CrossTheoryEqualityReplay,
    ) -> bool {
        if candidate.lhs == candidate.rhs {
            return true;
        }
        let mut stack = vec![candidate.lhs];
        let mut seen: Vec<TermId> = Vec::new();
        while let Some(term) = stack.pop() {
            if seen.contains(&term) {
                continue;
            }
            if term == candidate.rhs {
                return true;
            }
            seen.push(term);
            for (idx, replay) in replays.iter().enumerate() {
                if removed[idx] {
                    continue;
                }
                if !Self::cross_theory_replay_reason_subset(&replay.reason, &candidate.reason) {
                    continue;
                }
                if replay.lhs == term {
                    stack.push(replay.rhs);
                } else if replay.rhs == term {
                    stack.push(replay.lhs);
                }
            }
        }
        false
    }

    pub(crate) fn append_current_cross_theory_equality_replays(
        &self,
        replays: &mut Vec<CrossTheoryEqualityReplay>,
    ) -> usize {
        let exported = self.export_cross_theory_equality_replays();
        let exported_count = exported.len();
        let mut exported = exported;
        Self::prune_cross_theory_equality_replay_vec(&mut exported, |replay| {
            self.cross_theory_equality_replay_is_valid(replay)
        });
        // Build the endpoint index over the persistent set ONCE, then route
        // every candidate through the indexed insert (#qfuflia-replay-index
        // v3). The former per-candidate `covered_by` + `insert_minimal` pair
        // each rebuilt an O(|replays|) endpoint map — the outer `covered_by`
        // was fully redundant with the identical check inside
        // `insert_minimal`, so dropping it changes nothing.
        let mut by_endpoint: ay_core::kani_compat::DetHashMap<TermId, Vec<usize>> =
            Default::default();
        for (idx, replay) in replays.iter().enumerate() {
            by_endpoint.entry(replay.lhs).or_default().push(idx);
            by_endpoint.entry(replay.rhs).or_default().push(idx);
        }
        let mut removed: Vec<bool> = vec![false; replays.len()];
        let mut cover_scratch = CrossReplayCoverScratch::default();
        for replay in exported {
            Self::insert_cross_theory_equality_replay_minimal_indexed(
                replays,
                &mut by_endpoint,
                &mut removed,
                &mut cover_scratch,
                replay,
            );
        }
        Self::compact_cross_theory_equality_replays(replays, &removed);
        exported_count
    }

    pub(crate) fn prune_current_cross_theory_equality_replays(
        &self,
        replays: &mut Vec<CrossTheoryEqualityReplay>,
    ) {
        Self::prune_cross_theory_equality_replay_vec(replays, |replay| {
            self.cross_theory_equality_replay_is_valid(replay)
        });
    }

    pub(crate) fn append_current_array_equality_replays(
        &self,
        replays: &mut Vec<ArrayPropagatedEqualityReplay>,
    ) -> usize {
        let exported = self.export_array_equality_replays();
        let exported_count = exported.len();
        // Hash-set dedup instead of a per-candidate `Vec::contains` linear
        // scan over the monotonically growing persistent set — that scan was
        // O(exported x persistent) per outer re-entry (top frame on QF_ALIA
        // pointer-safe-10 after the cross-theory replay index landed).
        // Same membership predicate (derived Eq == derived Hash), same order.
        let mut seen: DetHashSet<ArrayPropagatedEqualityReplay> = replays.iter().cloned().collect();
        for replay in exported {
            if self.array_equality_replay_is_valid(&replay) && !seen.contains(&replay) {
                seen.insert(replay.clone());
                replays.push(replay);
            }
        }
        exported_count
    }

    pub(crate) fn prune_current_array_equality_replays(
        &self,
        replays: &mut Vec<ArrayPropagatedEqualityReplay>,
    ) {
        let mut retained = std::mem::take(replays);
        retained.sort_by_key(|replay| (replay.reason.len(), replay.lhs.0, replay.rhs.0));
        let mut seen: DetHashSet<ArrayPropagatedEqualityReplay> = DetHashSet::default();
        for replay in retained {
            if self.array_equality_replay_is_valid(&replay) && seen.insert(replay.clone()) {
                replays.push(replay);
            }
        }
    }

    pub(crate) fn replay_valid_array_equalities_to_euf(&mut self) -> usize {
        if self.imported_array_equality_replays.is_empty() && self.array_equality_replays.is_empty()
        {
            return 0;
        }

        let mut replays = self.imported_array_equality_replays.clone();
        for replay in &self.array_equality_replays {
            if !replays.contains(replay) {
                replays.push(replay.clone());
            }
        }

        let mut replayed = 0usize;
        let mut seeded = DetHashSet::default();
        for replay in &replays {
            if !self.array_equality_replay_is_valid(replay) {
                continue;
            }
            self.euf
                .assert_shared_equality(replay.lhs, replay.rhs, &replay.reason);
            seeded.insert(replay.clone());
            if self.array_equality_replays_seen.insert(replay.clone()) {
                self.array_equality_replays.push(replay.clone());
            }
            replayed += 1;
        }
        if !seeded.is_empty() {
            self.import_array_sent_equality_replays(&seeded);
        }

        replayed
    }

    pub(crate) fn replay_valid_cross_theory_equalities(&mut self) -> usize {
        if self.imported_cross_theory_equality_replays.is_empty()
            && self.cross_theory_equality_replays.is_empty()
        {
            return 0;
        }

        // #certora-replay-dedup: build the imported ∪ persistent working set
        // WITHOUT the former per-entry `Vec::contains` scan — Θ(persistent²)
        // deep struct compares on EVERY check(), measured at ~38% of on-CPU
        // samples on the Certora QF_UFLIA VC family (65782_8, 2026-07-14
        // profile: ~200 retained replays × ~230 checks/s). The common case
        // (nothing imported) is a straight clone; otherwise an O(1)-lookup
        // hash-set dedup keeps the exact same first-occurrence order and
        // membership the linear scan produced. Everything downstream
        // (validity prune + minimization + indexed re-insert) is unchanged —
        // an earlier variant that skipped the minimization for persistent
        // members asserted covered replays with different reason sets and
        // regressed 4 wisas/Hash greens to unknown (A/B 2026-07-14).
        let mut replays = if self.imported_cross_theory_equality_replays.is_empty() {
            self.cross_theory_equality_replays.clone()
        } else {
            let mut replays = self.imported_cross_theory_equality_replays.clone();
            let mut seen: DetHashSet<CrossTheoryEqualityReplay> = replays.iter().cloned().collect();
            for replay in &self.cross_theory_equality_replays {
                if seen.insert(replay.clone()) {
                    replays.push(replay.clone());
                }
            }
            replays
        };
        Self::prune_cross_theory_equality_replay_vec(&mut replays, |replay| {
            self.cross_theory_equality_replay_is_valid(replay)
        });

        let mut replayed = 0usize;
        let mut arrays_changed = false;
        // #qfuflia-replay-index v3 on the replay-intake path (same precedent
        // as export/import, fd6aca6211): build the endpoint index over the
        // persistent set ONCE per intake batch and route every candidate
        // through the indexed insert. The former per-candidate
        // `insert_cross_theory_equality_replay_minimal` rebuilt an
        // O(|replays|) endpoint map inside its `covered_by` for EVERY
        // candidate — Θ(re-entries × persistent²) on QF_ALIA pointer-safe-N,
        // ~82% of --no-proof on-CPU samples (2026-07-12 reprofile). Same
        // covered/not-covered answers; tombstoned removal compacted once at
        // the end preserves `Vec::retain` order exactly.
        let mut by_endpoint: ay_core::kani_compat::DetHashMap<TermId, Vec<usize>> =
            Default::default();
        for (idx, replay) in self.cross_theory_equality_replays.iter().enumerate() {
            by_endpoint.entry(replay.lhs).or_default().push(idx);
            by_endpoint.entry(replay.rhs).or_default().push(idx);
        }
        let mut removed: Vec<bool> = vec![false; self.cross_theory_equality_replays.len()];
        let mut cover_scratch = CrossReplayCoverScratch::default();
        let mut inserted_any = false;
        for replay in &replays {
            if !self.cross_theory_equality_replay_is_valid(replay) {
                continue;
            }

            self.euf
                .assert_shared_equality(replay.lhs, replay.rhs, &replay.reason);
            self.euf
                .seed_propagated_equality_pair(replay.lhs, replay.rhs);
            if let Some(lia) = &mut self.lia {
                lia.assert_shared_equality(replay.lhs, replay.rhs, &replay.reason);
                lia.seed_propagated_equality_pair(replay.lhs, replay.rhs);
            } else if let Some(lra) = &mut self.lra {
                lra.assert_shared_equality(replay.lhs, replay.rhs, &replay.reason);
            }
            if let Some(arrays) = &mut self.arrays {
                arrays.assert_shared_equality(replay.lhs, replay.rhs, &replay.reason);
                arrays_changed = true;
            }

            if Self::insert_cross_theory_equality_replay_minimal_indexed(
                &mut self.cross_theory_equality_replays,
                &mut by_endpoint,
                &mut removed,
                &mut cover_scratch,
                replay.clone(),
            ) {
                inserted_any = true;
            }
            replayed += 1;
        }
        if inserted_any {
            Self::compact_cross_theory_equality_replays(
                &mut self.cross_theory_equality_replays,
                &removed,
            );
            // The batch mutated the persistent set (pushes and possibly a
            // compaction shift); the persistent endpoint index is stale.
            self.cross_replay_index_valid = false;
        }
        if arrays_changed {
            self.mark_arrays_dirty();
        }

        replayed
    }

    pub(crate) fn replay_valid_euf_array_notifications(&mut self) -> usize {
        if self.arrays.is_none()
            || (self.imported_euf_array_notify_replay_edges.is_empty()
                && self.euf_array_notify_replay_edges.is_empty())
        {
            return 0;
        }

        let mut edges = self.imported_euf_array_notify_replay_edges.clone();
        for edge in &self.euf_array_notify_replay_edges {
            if !edges.contains(edge) {
                edges.push(edge.clone());
            }
        }
        let mut notifications = Vec::new();
        for edge in &edges {
            if !self.current_reasons_hold(&edge.reason) {
                continue;
            }

            let target_root =
                Self::array_notify_find(&mut self.euf_array_notify_parent, edge.target);
            let source_root =
                Self::array_notify_find(&mut self.euf_array_notify_parent, edge.source);
            if target_root == source_root {
                continue;
            }
            let (target, source) = if target_root.0 <= source_root.0 {
                (target_root, source_root)
            } else {
                (source_root, target_root)
            };
            self.euf_array_notify_parent.insert(source, target);
            notifications.push((target, source));
        }

        if let Some(arrays) = &mut self.arrays {
            for &(target, source) in &notifications {
                arrays.notify_equality(target, source);
            }
        }
        if !notifications.is_empty() {
            self.mark_arrays_dirty();
        }
        notifications.len()
    }

    /// Export the array solver's `requested_interface_eqs` dedup set (#8594).
    pub fn export_array_requested_interface_eqs(&self) -> DetHashSet<(TermId, TermId)> {
        self.arrays
            .as_ref()
            .map(ArraySolver::export_requested_interface_eqs)
            .unwrap_or_default()
    }

    /// Import previously persisted `requested_interface_eqs` (#8594).
    pub fn import_array_requested_interface_eqs(&mut self, eqs: &DetHashSet<(TermId, TermId)>) {
        if let Some(arrays) = &mut self.arrays {
            arrays.import_requested_interface_eqs(eqs);
        }
    }

    /// Export the array solver's `requested_model_eqs` dedup set (#8594).
    pub fn export_array_requested_model_eqs(&self) -> DetHashSet<(TermId, TermId)> {
        self.arrays
            .as_ref()
            .map(ArraySolver::export_requested_model_eqs)
            .unwrap_or_default()
    }

    /// Import previously persisted `requested_model_eqs` (#8594).
    pub fn import_array_requested_model_eqs(&mut self, eqs: &DetHashSet<(TermId, TermId)>) {
        if let Some(arrays) = &mut self.arrays {
            arrays.import_requested_model_eqs(eqs);
        }
    }

    /// Export exact-select model-equality keys from the array solver.
    pub fn export_array_exact_select_model_eq_keys(&self) -> DetHashSet<ExactSelectModelEqKey> {
        self.arrays
            .as_ref()
            .map(ArraySolver::export_exact_select_model_eq_keys)
            .unwrap_or_default()
    }

    /// Import exact-select model-equality keys into the array solver.
    pub fn import_array_exact_select_model_eq_keys(
        &mut self,
        keys: &DetHashSet<ExactSelectModelEqKey>,
    ) {
        if let Some(arrays) = &mut self.arrays {
            arrays.import_exact_select_model_eq_keys(keys);
        }
    }

    /// Export reason-carrying equality propagations from the array solver.
    pub fn export_array_sent_equality_replays(&self) -> DetHashSet<ArrayPropagatedEqualityReplay> {
        self.arrays
            .as_ref()
            .map(ArraySolver::export_sent_equality_replays)
            .unwrap_or_default()
    }

    /// Import reason-carrying equality propagations into the array solver.
    pub fn import_array_sent_equality_replays(
        &mut self,
        replays: &DetHashSet<ArrayPropagatedEqualityReplay>,
    ) {
        if let Some(arrays) = &mut self.arrays {
            arrays.import_sent_equality_replays(replays);
        }
    }
}

impl TheorySolver for TheoryCombiner<'_> {
    fn register_atom(&mut self, atom: TermId) {
        if let Some(arrays) = &mut self.arrays {
            arrays.register_atom(atom);
        }
        if let Some(lia) = &mut self.lia {
            lia.register_atom(atom);
        }
        if let Some(lra) = &mut self.lra {
            lra.register_atom(atom);
        }
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.record_current_assignment(literal, value);
        let direct_array_equality = self.direct_array_equality_assignment(literal, value);
        self.euf.assert_literal(literal, value);
        if let Some(arrays) = &mut self.arrays {
            arrays.assert_literal(literal, value);
            // #6820: only invalidate array quiescence when the literal
            // can change the array solver's equality / disequality state.
            // This includes array terms plus equality/distinct literals on
            // non-array operands (for example index equalities such as
            // `(= i j)`), while pure non-equality SAT literals remain safe
            // to skip.
            if involves_array(self.terms, literal) {
                self.mark_arrays_dirty();
            }
        }
        if let Some((lhs, rhs, reason)) = direct_array_equality {
            self.record_euf_array_notify_parent_edge(lhs, rhs, vec![reason]);
        }
        if let Some(lia) = &mut self.lia {
            let is_int_equality_atom = {
                let inner = match self.terms.get(literal) {
                    TermData::Not(inner) => *inner,
                    _ => literal,
                };
                matches!(
                    self.terms.get(inner),
                    TermData::App(sym, args)
                        if sym.name() == "=" && args.len() == 2
                            && matches!(self.terms.sort(args[0]), Sort::Int)
                )
            };
            if self.a5_lazy_arith
                && is_int_equality_atom
                && involves_int_arithmetic(self.terms, literal)
            {
                // A5 v2 (#qfuflia-a5): defer only equalities over vars with no
                // arith connection yet; materialize immediately if any leaf
                // var already carries a bound (single-hop relevance).
                let mut leaves = Vec::new();
                Self::a5_int_leaf_vars(self.terms, literal, &mut leaves);
                if leaves.iter().any(|v| self.a5_bounded_vars.contains(v)) {
                    self.lia_bcp_dirty = true;
                    lia.assert_literal(literal, value);
                } else {
                    let idx = self.deferred_arith_eqs.len();
                    self.deferred_arith_eqs.push((literal, value));
                    self.a5_materialized.push(false);
                    for v in leaves {
                        self.a5_deferred_by_var.entry(v).or_default().push(idx);
                    }
                }
            } else if involves_int_arithmetic(self.terms, literal) {
                self.lia_bcp_dirty = true;
                lia.assert_literal(literal, value);
                // A5 v2: this eager arith literal CONNECTS its vars — wake any
                // deferred equalities waiting on them.
                if self.a5_lazy_arith {
                    let mut leaves = Vec::new();
                    Self::a5_int_leaf_vars(self.terms, literal, &mut leaves);
                    for v in leaves {
                        if self.a5_bounded_vars.insert(v) {
                            if let Some(waiting) = self.a5_deferred_by_var.remove(&v) {
                                for idx in waiting {
                                    if !self.a5_materialized[idx] {
                                        self.a5_materialized[idx] = true;
                                        let (t, val) = self.deferred_arith_eqs[idx];
                                        lia.assert_literal(t, val);
                                    }
                                }
                            }
                        }
                    }
                }
            } else if !self.a5_replaying
                && std::env::var_os("AY_A5_UF_EQ_DEFER").is_some()
                && is_uf_int_equality(self.terms, literal).is_some()
            {
                // A5 v6 (z3's actual split, #qfuflia-a5): UF-containing Int
                // equalities are EUF-owned during search — congruence handles
                // them; LIA's shared-equality machinery sees them only at the
                // final check (replay below). Pure-arith equalities (the
                // offset chains whose BCP pruning the v1 experiment proved
                // essential) stay on the eager branch above.
                self.deferred_arith_eqs.push((literal, value));
            } else if let Some((lhs, rhs)) = is_uf_int_equality(self.terms, literal) {
                // #8147: is_uf_int_equality unwraps Not internally, so we must
                // account for negation when deciding equality vs disequality.
                // A literal `(not (= a b))` with value=true means a != b.
                //
                // The reason literal must use the INNER equality term (not the
                // Not-wrapped form) so that downstream code in nelson_oppen.rs
                // can find the negated equality via `!lit.value` (#6131).
                let inner = match self.terms.get(literal) {
                    TermData::Not(inner) => Some(*inner),
                    _ => None,
                };
                let effective_value = value ^ inner.is_some();
                // Use inner (unwrapped) term for the reason, with inverted value.
                // This ensures: equality => reason=(eq_term, true),
                //               disequality => reason=(eq_term, false).
                let reason_term = inner.unwrap_or(literal);
                let reason_value = if inner.is_some() { !value } else { value };
                let reason = TheoryLit::new(reason_term, reason_value);
                if effective_value {
                    // INTERFACE-DIET C1: withhold POSITIVE pure-UF=UF Int
                    // equalities from the LIA N-O interface (the selector-eq
                    // flood). EUF already received this literal at the top of
                    // assert_literal, so the e-graph stays the single source of
                    // truth; the pre-Sat certifier re-derives + value-certifies
                    // the arrangement. UF=const/var/linear equalities and ALL
                    // disequalities stay eager (bridge const-prop intact).
                    if self.interface_diet.withholds()
                        && crate::term_helpers::is_pure_uf_uf_int_equality(self.terms, lhs, rhs)
                    {
                        lia.mark_interface_hidden();
                    } else {
                        lia.assert_shared_equality(lhs, rhs, &[reason]);
                    }
                } else {
                    lia.assert_shared_disequality(lhs, rhs, &[reason]);
                }
                self.lia_bcp_dirty = true;
            }
            if let Some(interface) = &mut self.interface {
                interface.track_interface_term(self.terms, literal);
                interface.collect_int_constants(self.terms, literal);
                interface.track_uf_arith_args(self.terms, literal);
            }
        } else if let Some(lra) = &mut self.lra {
            if self.arrays.is_some() {
                if let Some((lhs, rhs)) = is_select_real_equality(self.terms, literal) {
                    // #8147: is_select_real_equality unwraps Not internally.
                    // Use inner (unwrapped) term for reason (see LIA path above).
                    let inner = match self.terms.get(literal) {
                        TermData::Not(inner) => Some(*inner),
                        _ => None,
                    };
                    let effective_value = value ^ inner.is_some();
                    let reason_term = inner.unwrap_or(literal);
                    let reason_value = if inner.is_some() { !value } else { value };
                    let reason = TheoryLit::new(reason_term, reason_value);
                    if effective_value {
                        lra.assert_shared_equality(lhs, rhs, &[reason]);
                    } else {
                        lra.assert_shared_disequality(lhs, rhs, &[reason]);
                    }
                    if let Some(interface) = &mut self.interface {
                        interface.track_interface_term(self.terms, literal);
                        interface.collect_real_constants(self.terms, literal);
                        interface.track_uf_arith_args(self.terms, literal);
                    }
                    return;
                }
            }
            if involves_real_arithmetic(self.terms, literal) {
                lra.assert_literal(literal, value);
            } else if let Some((lhs, rhs)) = is_uf_real_equality(self.terms, literal) {
                // #8147: is_uf_real_equality unwraps Not internally.
                // Use inner (unwrapped) term for reason (see LIA path above).
                let inner = match self.terms.get(literal) {
                    TermData::Not(inner) => Some(*inner),
                    _ => None,
                };
                let effective_value = value ^ inner.is_some();
                let reason_term = inner.unwrap_or(literal);
                let reason_value = if inner.is_some() { !value } else { value };
                let reason = TheoryLit::new(reason_term, reason_value);
                if effective_value {
                    lra.assert_shared_equality(lhs, rhs, &[reason]);
                } else {
                    lra.assert_shared_disequality(lhs, rhs, &[reason]);
                }
            }
            if let Some(interface) = &mut self.interface {
                interface.track_interface_term(self.terms, literal);
                interface.collect_real_constants(self.terms, literal);
                interface.track_uf_arith_args(self.terms, literal);
            }
        }
    }

    fn check(&mut self) -> TheoryResult {
        // TEMP-DIAG (#certora-w8): env-gated combiner-check telemetry.
        {
            static TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            if *TRACE.get_or_init(|| std::env::var_os("AY_CERTORA_TRACE").is_some()) {
                use std::sync::atomic::{AtomicU64, Ordering};
                static CALLS: AtomicU64 = AtomicU64::new(0);
                let n = CALLS.fetch_add(1, Ordering::Relaxed) + 1;
                if n.is_multiple_of(1024) {
                    safe_eprintln!(
                        "[CHK-TRACE] checks={} replays={} imported={} shared_eqs_lia={}",
                        n,
                        self.cross_theory_equality_replays.len(),
                        self.imported_cross_theory_equality_replays.len(),
                        self.lia.as_ref().map_or(0, |l| l.shared_equalities_len())
                    );
                }
            }
        }
        // A5 lazy adapter: materialize the deferred Int equality atoms into
        // LIA before the full check (idempotent per atom set — LIA dedups
        // re-asserted atoms via bound_atoms/asserted maps).
        if (self.a5_lazy_arith || std::env::var_os("AY_A5_UF_EQ_DEFER").is_some())
            && !self.deferred_arith_eqs.is_empty()
        {
            let deferred = self.deferred_arith_eqs.clone();
            self.a5_replaying = true;
            for (i, (t, v)) in deferred.into_iter().enumerate() {
                if self.a5_materialized.get(i).copied().unwrap_or(false) {
                    continue;
                }
                if let Some(idx) = self.a5_materialized.get_mut(i) {
                    *idx = true;
                }
                // Re-route through the full assert path so UF-containing
                // equalities take their proper shared-equality branch.
                TheorySolver::assert_literal(self, t, v);
            }
            self.a5_replaying = false;
            self.lia_bcp_dirty = true;
        }
        self.replay_valid_cross_theory_equalities();
        self.replay_valid_euf_array_notifications();
        self.replay_valid_array_equalities_to_euf();
        let __no_result = self.nelson_oppen_check();
        // Candidate-REJECTION diagnosis (env-gated `AY_REJECT_INSTRUMENT`,
        // verdict-neutral): categorise what the N-O combiner returns for each
        // candidate model — the rejector that demands another round. Also sample
        // the LIA shared-equality interface size at result time (INTERFACE-DIET
        // C5/R4 flood metric).
        let __shared_eq_len = self.lia.as_ref().map_or(0, |l| l.shared_equalities_len());
        crate::reject_instrument::record_combiner_result(&__no_result, self.terms, __shared_eq_len);
        __no_result
    }

    fn check_during_propagate(&mut self) -> TheoryResult {
        if let Some(lia) = &mut self.lia {
            // #qfuflia-lia-bcp-gate: skip the arithmetic BCP-time check when
            // no arithmetic-routed literal has been asserted since the last
            // one — on the SMT-COMP QF_UFLIA xs family 174k of 174k BCP-time
            // LIA checks ran with zero new arithmetic input, and their fixed
            // cost was the entire 60s budget. Sound by construction: the
            // BCP-time check is an early-conflict OPTIMIZATION; the final
            // check after SAT remains authoritative for anything skipped.
            if self.lia_bcp_dirty {
                let result = defer_non_local_result(lia.check_during_propagate());
                if !matches!(result, TheoryResult::Sat) {
                    return result;
                }
                self.lia_bcp_dirty = false;
            }
        } else if let Some(lra) = &mut self.lra {
            let result = defer_non_local_result(lra.check_during_propagate());
            if !matches!(result, TheoryResult::Sat) {
                return result;
            }
        }

        let euf_result = defer_non_local_result(self.euf.check_during_propagate());
        if !matches!(euf_result, TheoryResult::Sat) {
            return euf_result;
        }

        // BCP-time arrays check: an early-conflict OPTIMIZATION only — the
        // full `check()` after SAT stays authoritative (see the
        // `arrays_bcp_lanes` field docs, #qfax-t3-atom-space).
        if self.arrays_bcp_lanes {
            if let Some(arrays) = &mut self.arrays {
                let result = defer_non_local_result(arrays.check_during_propagate());
                if !matches!(result, TheoryResult::Sat) {
                    return result;
                }
            }
        }

        // Search-time D0 clash/ground-diseq/cycle check (lazy lane only,
        // stage D2). The lazy lane has no eager axiom encoding of
        // constructor distinctness/injectivity, so datatype conflicts must
        // surface DURING search: a wrong branch (e.g. a BMC goal equality
        // merging two structurally different ground towers) is refuted at
        // BCP quiescence by the D0 pass's verified tautology clause instead
        // of surviving to the fixpoint. Gated on the shared merge change
        // feed (peeked here, consumed by the D1 pass below); `Inconclusive`
        // (dedup/unverifiable) is NOT a verdict point at search time — the
        // fixpoint call remains the fail-closed authority.
        if self.dt_d2.is_some() && self.euf.dt_merge_dirty() {
            if let Some(dt) = &mut self.dt_pass {
                match dt.check(self.terms, &mut self.euf) {
                    ay_dt::DtPassOutcome::Lemmas(lemmas) => {
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                    ay_dt::DtPassOutcome::Ok | ay_dt::DtPassOutcome::Inconclusive => {}
                }
            }
        }

        // D1 lazy DT tester/selector propagation at BCP quiescence
        // (`DESIGN_lazy_dt.md` stage D1). Gated on the e-graph merge change
        // feed, so merge-free BCP rounds pay one Option check. Emitted
        // clauses are independently re-derived DT tautologies injected inline
        // by the extension (#6546) — they only prune DT-inconsistent
        // assignments and can never manufacture a false-UNSAT.
        if self.dt_d1.is_some() {
            let lemmas = self.dt_d1_lemmas(false);
            if !lemmas.is_empty() {
                return TheoryResult::NeedLemmas(lemmas);
            }
        }

        TheoryResult::Sat
    }

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn propagate(&mut self) -> Vec<ay_core::TheoryPropagation> {
        let mut props = self.euf.propagate();
        if let Some(lia) = &mut self.lia {
            props.extend(lia.propagate());
        }
        if let Some(lra) = &mut self.lra {
            props.extend(lra.propagate());
        }
        // BCP-time arrays propagations: skipped when the lanes are demoted
        // (see the `arrays_bcp_lanes` field docs, #qfax-t3-atom-space). The
        // N-O `propagate_equalities` cross-theory sharing lane and the full
        // `check()` battery are unaffected.
        if self.arrays_bcp_lanes {
            if let Some(arrays) = &mut self.arrays {
                props.extend(arrays.propagate());
            }
        }
        props
    }

    fn has_pending_propagations(&self) -> bool {
        self.euf.has_pending_propagations()
            || self
                .lia
                .as_ref()
                .is_some_and(TheorySolver::has_pending_propagations)
            || self
                .lra
                .as_ref()
                .is_some_and(TheorySolver::has_pending_propagations)
            || self
                .arrays
                .as_ref()
                .is_some_and(TheorySolver::has_pending_propagations)
    }

    fn push(&mut self) {
        self.lia_bcp_dirty = true;
        self.scope_depth += 1;
        self.current_assignment_scope_marks
            .push(self.current_assignment_trail.len());
        self.euf.push();
        if let Some(lia) = &mut self.lia {
            lia.push();
        }
        if let Some(lra) = &mut self.lra {
            lra.push();
        }
        if let Some(arrays) = &mut self.arrays {
            arrays.push();
        }
        if self.arrays.is_some() {
            self.mark_arrays_dirty();
        }
        if let Some(interface) = &mut self.interface {
            interface.push();
        }
    }

    fn pop(&mut self) {
        self.lia_bcp_dirty = true;
        if self.scope_depth == 0 {
            // Graceful no-op: pop at depth 0 is a caller error but not fatal.
            return;
        }
        self.scope_depth -= 1;
        if let Some(mark) = self.current_assignment_scope_marks.pop() {
            self.restore_current_assignments_to_mark(mark);
        }
        self.euf.pop();
        if let Some(lia) = &mut self.lia {
            lia.pop();
        }
        if let Some(lra) = &mut self.lra {
            lra.pop();
        }
        if let Some(arrays) = &mut self.arrays {
            arrays.pop();
        }
        self.euf_array_notify_parent.clear();
        if self.arrays.is_some() {
            self.mark_arrays_dirty();
        }
        if let Some(interface) = &mut self.interface {
            interface.pop();
        }
    }

    fn reset(&mut self) {
        self.lia_bcp_dirty = true;
        assert!(
            self.scope_depth == 0,
            "BUG: TheoryCombiner({})::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.label,
            self.scope_depth,
        );
        self.euf.reset();
        if let Some(lia) = &mut self.lia {
            lia.reset();
        }
        if let Some(lra) = &mut self.lra {
            lra.reset();
        }
        if let Some(arrays) = &mut self.arrays {
            arrays.reset();
        }
        self.euf_array_notify_parent.clear();
        self.euf_array_notify_replay_edges.clear();
        self.euf_array_notify_replay_edge_set.clear();
        self.imported_euf_array_notify_replay_edges.clear();
        self.array_equality_replays.clear();
        self.imported_array_equality_replays.clear();
        self.cross_theory_equality_replays.clear();
        self.cross_replay_index_valid = false;
        // Coverage memo is only valid while `cross_theory_equality_replays` grows
        // monotonically; `reset()` empties it, so the memo must be emptied too or
        // a formerly-covered candidate would be wrongly skipped against the now-
        // empty replay set. (#qfuflia-replay-memo)
        self.cross_theory_replay_processed.clear();
        self.imported_cross_theory_equality_replays.clear();
        self.clear_current_assignments();
        if self.arrays.is_some() {
            self.mark_arrays_dirty();
        }
        if let Some(interface) = &mut self.interface {
            interface.reset();
        }
    }

    fn soft_reset(&mut self) {
        self.lia_bcp_dirty = true;
        assert!(
            self.scope_depth == 0,
            "BUG: TheoryCombiner({})::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.label,
            self.scope_depth,
        );
        self.euf.soft_reset();
        if let Some(lia) = &mut self.lia {
            lia.soft_reset();
        }
        if let Some(lra) = &mut self.lra {
            lra.soft_reset();
        }
        if let Some(arrays) = &mut self.arrays {
            arrays.soft_reset();
        }
        self.euf_array_notify_parent.clear();
        // Preserve reason-carrying EUF->array notification replay edges across
        // extension soft resets. `TheoryExtension::init()` soft-resets at SAT
        // restarts before replay can run; clearing here drops the validated
        // persistence state and forces AX/EUF store-chain exploration to start
        // over. Replay still validates every reason against current assignments.
        self.clear_current_assignments();
        if self.arrays.is_some() {
            self.mark_arrays_dirty();
        }
        if let Some(interface) = &mut self.interface {
            interface.reset();
        }
    }

    /// Lazy warm-reset for the AUFLIA combiner
    /// (LAZY-M3-PERSISTENT-COMBINER-BLUEPRINT §M3.1 / §3).
    ///
    /// Create-once + per-round warm-reset: RETAIN all §3.1 persistable state
    /// (structural theory caches; the six monotone dedup/replay sets —
    /// `euf_array_notify_replay_edges`, `array_equality_replays`,
    /// `cross_theory_equality_replays` and their mirrors; learned cuts /
    /// Diophantine state; the shared rescue counter) and RESET all §3.2
    /// assignment-derived state (EUF merges + Nelson-Oppen carry, the
    /// current-assignment trail, the EUF->array notify parent map, speculative
    /// interface-bridge state, LIA/LRA candidate assignments).
    ///
    /// The partition is deliberately identical to `soft_reset` — which already
    /// clears exactly the §3.2 leak surface while preserving the §3.1 replay
    /// sets — EXCEPT that the arithmetic sub-solvers use their warm-start
    /// `soft_reset_warm` (retain simplex tableau/values so the next round
    /// re-pivots only violated bounds) instead of the cold `soft_reset`. The
    /// warm-started numeric values are a monotone, model-independent
    /// optimization and are intentionally NOT part of the assignment-derived
    /// digest below.
    ///
    /// SOUNDNESS INVARIANT (§3.3(b)): after this reset the combiner's
    /// assignment-derived state MUST equal a freshly-constructed combiner's —
    /// i.e. [`assignment_derived_digest`] MUST be `0`. The `debug_assert` is the
    /// standing oracle: it fires on every warm-reset in debug builds, and any
    /// divergence means the persist-vs-reset partition dropped a §3.2 undo.
    ///
    /// NOTE (M3.1 is shadow-only): AUFLIA still runs the per-round *fresh*
    /// combiner in `solve_auf_lia`; `soft_reset_warm` is the create-once
    /// primitive that M3.2 will wire in as a shadow (fresh stays authoritative).
    /// Building a live persistent combiner across the outer loop is blocked by
    /// the executor borrow architecture (the loop mutably reborrows `self`
    /// between rounds) and is M3.2's create-once arm.
    fn soft_reset_warm(&mut self) {
        self.lia_bcp_dirty = true;
        assert!(
            self.scope_depth == 0,
            "BUG: TheoryCombiner({})::soft_reset_warm() called with non-zero scope depth {} (unbalanced push/pop)",
            self.label,
            self.scope_depth,
        );
        // §3.2: unwind this round's EUF merges + clear all Nelson-Oppen carry
        // (preserving the pristine post-init e-graph structure).
        self.euf.soft_reset();
        // §3.1 warm-start: retain the simplex tableau/values.
        if let Some(lia) = &mut self.lia {
            TheorySolver::soft_reset_warm(lia);
        }
        if let Some(lra) = &mut self.lra {
            TheorySolver::soft_reset_warm(lra);
        }
        // Arrays: reset assignment-derived select/store model guesses. (The
        // structural registered-atom scope + the exported replay sets are the
        // retained §3.1 state and are NOT cleared here.)
        if let Some(arrays) = &mut self.arrays {
            arrays.soft_reset();
        }
        self.euf_array_notify_parent.clear();
        self.clear_current_assignments();
        if self.arrays.is_some() {
            self.mark_arrays_dirty();
        }
        if let Some(interface) = &mut self.interface {
            interface.reset();
        }
        // §3.3(b) standing debug oracle: reset state must equal a fresh
        // combiner's (empty assignment-derived state ⇒ digest 0). If this
        // diverges the persist-vs-reset partition is wrong — fix the partition,
        // never weaken the assert.
        debug_assert_eq!(
            self.assignment_derived_digest(),
            0,
            "BUG: TheoryCombiner({})::soft_reset_warm left non-empty assignment-derived state \
             (a §3.2 undo was dropped — stale speculative merge/propagation leak). \
             This violates the LAZY-M3 §3.3(b) soundness invariant.",
            self.label,
        );
    }

    fn supports_theory_aware_branching(&self) -> bool {
        if self.arrays.is_some() {
            return true;
        }
        if let Some(lia) = &self.lia {
            return lia.supports_theory_aware_branching();
        }
        if let Some(lra) = &self.lra {
            return lra.supports_theory_aware_branching();
        }
        false
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        if self.arrays.is_some() {
            return self.suggest_phase_with_arrays(atom);
        }
        if let Some(lia) = &self.lia {
            return lia.suggest_phase(atom);
        }
        if let Some(lra) = &self.lra {
            return lra.suggest_phase(atom);
        }
        None
    }

    fn phase_hint_epoch(&self) -> Option<u64> {
        // Every suggestion this combiner emits is a pure function of the
        // arithmetic solver's phase state: `suggest_phase` delegates to LIA
        // (itself a pure delegate to its inner LRA) or LRA, and the
        // `suggest_phase_with_arrays` overrides are STATIC term-shape
        // predicates that never change for a given atom. So the arithmetic
        // epoch fully covers suggestion change, and forwarding it revives the
        // SAT seeder's O(atoms)-scan epoch skip on combined lanes
        // (#certora-phase-epoch — the scan ran on EVERY BCP quiescence, ~19%
        // of the solve window on 10^5-atom Certora QF_UFLIA files). The LIA
        // arm size-gates itself (see LiaSolver::phase_hint_epoch — the skip
        // is value-exact but not trajectory-exact, and small crafted greens
        // depend on the historical every-quiescence re-seed trajectory); the
        // LRA arm applies the same gate here for the same reason.
        if let Some(lia) = &self.lia {
            return lia.phase_hint_epoch();
        }
        if let Some(lra) = &self.lra {
            const PHASE_EPOCH_MIN_ATOMS: usize = 8192;
            if lra.registered_atom_count() < PHASE_EPOCH_MIN_ATOMS {
                return None;
            }
            return lra.phase_hint_epoch();
        }
        None
    }

    fn sort_atom_index(&mut self) {
        if let Some(lia) = &mut self.lia {
            lia.sort_atom_index();
        }
        if let Some(lra) = &mut self.lra {
            lra.sort_atom_index();
        }
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        if let Some(lia) = &self.lia {
            return lia.generate_bound_axiom_terms();
        }
        if let Some(lra) = &self.lra {
            return lra.generate_bound_axiom_terms();
        }
        Vec::new()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        if let Some(lia) = &self.lia {
            return lia.generate_incremental_bound_axioms(atom);
        }
        if let Some(lra) = &self.lra {
            return lra.generate_incremental_bound_axioms(atom);
        }
        Vec::new()
    }

    fn note_applied_theory_lemma(&mut self, clause: &[TheoryLit]) {
        // Forward to arrays sub-solver for dedup tracking.
        // #6694 fix: the array solver's pop() now clears applied_theory_lemmas,
        // so backtracking no longer causes stale dedup entries.
        if let Some(arrays) = &mut self.arrays {
            arrays.note_applied_theory_lemma(clause);
        }
    }

    fn supports_farkas_semantic_check(&self) -> bool {
        self.lra.is_some()
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        let mut stats = vec![
            ("nelson_oppen_rounds", self.nelson_oppen_rounds),
            ("nelson_oppen_max_rounds", self.nelson_oppen_max_rounds),
            (
                "equalities_propagated_to_euf",
                self.equalities_propagated_to_euf,
            ),
            (
                "equalities_propagated_to_arith",
                self.equalities_propagated_to_arith,
            ),
        ];
        // Forward the arrays sub-solver's per-theory statistics (M0,
        // SELECT-PAIRS blueprint) so they reach the -st stats channel.
        if let Some(arrays) = &self.arrays {
            stats.extend(TheorySolver::collect_statistics(arrays));
        }
        // Forward EUF's per-theory statistics (#euf-lazy-explain: the lazy
        // emitted/explained counters must be visible on combined solves too).
        stats.extend(TheorySolver::collect_statistics(&self.euf));
        if let Some(d1) = &self.dt_d1 {
            let (emitted, failures) = d1.stats();
            stats.push(("dt_d1_lemmas_emitted", emitted));
            stats.push(("dt_d1_rederive_failures", failures));
        }
        stats
    }

    fn registered_atom_count(&self) -> usize {
        let mut count = self.euf.registered_atom_count();
        if let Some(lia) = &self.lia {
            count += lia.registered_atom_count();
        }
        if let Some(lra) = &self.lra {
            count += lra.registered_atom_count();
        }
        count
    }

    fn explain_propagation(&mut self, lit: TermId, reason_data: u64) -> Option<Vec<TheoryLit>> {
        // Routing note (#euf-lazy-explain): EUF lazy tokens carry bit 63 SET
        // plus an EUF magic, which the LRA/LIA decoder treats as its own
        // eagerly-materialized "interval" encoding and rejects with `None`
        // without reading any state — so the LIA-then-LRA-then-EUF cascade
        // below can never hand an EUF token to arithmetic (or vice versa:
        // EUF declines anything without its magic).
        if let Some(lia) = &mut self.lia {
            if let Some(result) = lia.explain_propagation(lit, reason_data) {
                return Some(result);
            }
        }
        if let Some(lra) = &mut self.lra {
            if let Some(result) = lra.explain_propagation(lit, reason_data) {
                return Some(result);
            }
        }
        self.euf.explain_propagation(lit, reason_data)
    }

    fn set_lazy_propagation_supported(&mut self, supported: bool) {
        // #8467 capability handshake: forward to every sub-solver whose
        // propagations flow through `Self::propagate()` (see the doc on the
        // trait method). LIA/LRA currently emit lazy unconditionally and
        // ignore this; EUF gates its lazy emission on it.
        //
        // #euf-lazy-explain scope: EUF lazy emission is granted only in
        // ARITHMETIC-FREE combinations (arrays+EUF — the QF_AX lane, where
        // it collapsed the swap_t3 red's conflicts 161k -> 110k). On
        // UFLIA-class combinations the hash_sat model-search guards measured
        // hard sat->unknown trajectory flips under lazy EUF propagations
        // (hash_sat_09_11: sat 0.73s eager -> unknown@30s lazy; these
        // searches are order-chaotic — a lazy enqueue carries no permanent
        // clause and bumps only the propagated var's VSIDS activity, so the
        // decision order diverges) while the saved explain() work there is
        // negligible (~300 EUF emissions/solve — EUF explain is not the
        // UFLIA bottleneck, search quality is; see
        // the development design notes).
        // Keeping arithmetic combinations on eager EUF reasons preserves the
        // baseline search bit-for-bit.
        let euf_supported = supported && self.lia.is_none() && self.lra.is_none();
        self.euf.set_lazy_propagation_supported(euf_supported);
        if let Some(lia) = &mut self.lia {
            lia.set_lazy_propagation_supported(supported);
        }
        if let Some(lra) = &mut self.lra {
            lra.set_lazy_propagation_supported(supported);
        }
        if let Some(arrays) = &mut self.arrays {
            arrays.set_lazy_propagation_supported(supported);
        }
    }

    fn mark_propagation_rejected(&mut self, lit: TermId, reason_data: u64) {
        if let Some(lia) = &mut self.lia {
            lia.mark_propagation_rejected(lit, reason_data);
        }
        if let Some(lra) = &mut self.lra {
            lra.mark_propagation_rejected(lit, reason_data);
        }
        self.euf.mark_propagation_rejected(lit, reason_data);
    }

    fn note_conflict_atom(&mut self, atom: TermId) {
        if let Some(lia) = &mut self.lia {
            lia.note_conflict_atom(atom);
        }
        if let Some(lra) = &mut self.lra {
            lra.note_conflict_atom(atom);
        }
        self.euf.note_conflict_atom(atom);
    }
}
