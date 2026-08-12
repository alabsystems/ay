// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF solver core implementation.
//!
//! Contains `EufSolver` struct definition, constructor, and utility methods.
//! Incremental E-graph operations are in `egraph.rs`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::{Sort, TheoryLit, TheoryPropagation};
use std::collections::VecDeque;
use std::sync::OnceLock;

/// #6359: Cached debug flags for EUF solver.
struct EufDebugFlags {
    debug_euf: bool,
    debug_nelson_oppen: bool,
    /// Kill switch for Bool-argument congruence completeness. Default OFF
    /// (disabled) as of 2026-06-17: the completion is UNSOUND/incomplete — it
    /// decides Bool-valued-UF-arg atoms but produces a FALSE-SAT on witnesses
    /// like `(= (fb true) (fb p0))` ∧ `(not (= (fb (or p1 p0)) (fb p0)))`
    /// (AY sat, truth unsat; found by the declared-division soundness audit).
    /// With it OFF, EUF leaves these clauseless Bool-arg atoms UNDECIDED and
    /// returns a sound `unknown` (the pre-f6915645 behavior), which is correct.
    /// OFF process-wide (the former `AY_EUF_BOOL_ARG_MERGE` env override is
    /// removed — no environment variable may enable an unsound path); the
    /// standalone EUF unit tests enable it per-instance via
    /// `set_bool_arg_congruence`. When enabled, Bool-sorted terms that appear
    /// as UF arguments participate in the true/false equivalence-class merge
    /// so congruence fires on their parent applications.
    bool_arg_congruence: bool,
    /// Read-only SOUND Bool-arg congruence MODEL VALIDATION. Default ON.
    /// At a candidate `Sat` verdict, refuses to certify a model that is provably
    /// non-congruent over Bool UF-args (two apps with identical non-Bool args
    /// and identical Bool-arg truth values in different classes) by downgrading
    /// `Sat` -> `Unknown`. Only ever downgrades — never asserts UNSAT — so it has
    /// no false-UNSAT risk (unlike the merge). This is the SOUND fallback that
    /// keeps the flagship from false-SAT on Bool-arg congruence gaps the lemma
    /// cannot close (e.g. `uf_fs2`). Always ON (the former
    /// `AY_EUF_BOOL_ARG_VALIDATE=0` env kill-switch is removed — no
    /// environment variable may turn off a soundness guard); `solve_euf`
    /// tunes it per-instance via `set_bool_arg_validate`.
    bool_arg_validate: bool,
    /// Transitive (congruence-closing) variant of the validation. Default ON.
    bool_arg_validate_transitive: bool,
}

static EUF_DEBUG_FLAGS: OnceLock<EufDebugFlags> = OnceLock::new();

fn euf_debug_flags() -> &'static EufDebugFlags {
    EUF_DEBUG_FLAGS.get_or_init(|| EufDebugFlags {
        debug_euf: ay_core::debug_channel_active(ay_core::DebugChannel::Euf),
        debug_nelson_oppen: ay_core::debug_channel_active(ay_core::DebugChannel::EufNelsonOppen),
        // EUF-side Bool-arg truth-value class merge. DEFAULT OFF.
        //
        // This merges UF-application arguments that share a *model* truth value
        // into the true/false class so congruence fires on their parent apps,
        // INCLUDING builtin/connective and (with the constant fold added here)
        // constant Bool args. It is the only mechanism that can relate
        // syntactically-different-but-model-equal complex Bool args (the
        // `uf_fs2` witness). However it remains UNSOUND in the false-UNSAT
        // direction: run during BCP over the extended builtin Bool-arg set, it
        // can emit congruence conflicts whose reason literals are not faithfully
        // explainable, yielding a wrong learned clause and a false UNSAT
        // (reproducer: deeply nested `fb(xor(..))`/`fb(and(..))` over a
        // partial assignment). The conflict verifier cannot catch this (it
        // re-runs the same deterministic merge). It is therefore kept OFF,
        // permanently and process-wide (the former `AY_EUF_BOOL_ARG_MERGE=1`
        // env force-enable is removed — no environment variable may enable an
        // unsound path); the SOUND production driver is the formula-level
        // congruence-lemma injection in `solve_euf`. The standalone EUF unit
        // tests enable it per-instance via `set_bool_arg_congruence`.
        bool_arg_congruence: false,
        // Read-only SOUND model-validation guard (always ON). Only ever
        // downgrades Sat -> Unknown (no false-UNSAT risk). It is the soundness
        // net for Bool-arg congruence false-SATs in BOTH incremental and
        // non-incremental mode (the eager congruence lemma closes them
        // non-incrementally but is unsound across push/pop). The baseline-class
        // gate in `bool_arg_model_is_congruent` confines it to genuine Bool-arg
        // congruence violations so it does not over-fire on dense incremental
        // models. (Former `AY_EUF_BOOL_ARG_VALIDATE=0` /
        // `AY_EUF_BOOL_ARG_VALIDATE_TRANSITIVE=0` env kill-switches removed —
        // no environment variable may turn off a soundness guard.)
        bool_arg_validate: true,
        bool_arg_validate_transitive: true,
    })
}

/// Parse the `AY_EUF_CONG_NEG` kill switch / depth knob (#cong-neg-prop):
/// `0` = lookahead off, `1` = one-step (the default), `2..=8` = cascade
/// depth (hypothesis merge counts as depth 1), unset/invalid = default.
/// Cached process-wide (read on every solver construction otherwise —
/// EufSolver::new sits on the DPLL(T) restart path).
///
/// The default is 1: cascade depths were measured on SMT-LIB QF_UF
/// (2026-07) and made things WORSE — PEQ012_size4 depth 2 cut theory
/// conflicts 18% (2,895 -> 2,367) but left total conflicts flat (29.5k) at
/// 2.2x wall (0.84s -> 1.85s), and NEQ033_size5 blew up 5,486 -> 24,360
/// conflicts / 14s -> 239s (the long multi-level reasons produce weak
/// learned clauses that derail the search, on top of the per-scan
/// simulation cost). Depths 2-3 remain available for A/B.
fn cong_neg_depth_from_env() -> u32 {
    static DEPTH: OnceLock<u32> = OnceLock::new();
    *DEPTH.get_or_init(|| {
        const DEFAULT_DEPTH: u32 = 1;
        match std::env::var("AY_EUF_CONG_NEG") {
            Ok(s) => s.trim().parse::<u32>().map_or(DEFAULT_DEPTH, |d| d.min(8)),
            Err(_) => DEFAULT_DEPTH,
        }
    })
}

/// #cong-neg-backoff: whether the adaptive-suspend for the cascade
/// negative-congruence lookahead is enabled. Default true; `AY_EUF_CONG_NEG_ADAPTIVE=0`
/// restores the legacy always-on lookahead (kill switch).
fn cong_neg_adaptive_from_env() -> bool {
    static ADAPTIVE: OnceLock<bool> = OnceLock::new();
    *ADAPTIVE.get_or_init(|| {
        !matches!(
            std::env::var("AY_EUF_CONG_NEG_ADAPTIVE").as_deref(),
            Ok("0")
        )
    })
}

/// #euf-atom-filter: whether to restrict the negative-congruence
/// propagation-candidate list (`eq_terms`) to equalities that are SAT atoms
/// (have a Boolean variable in the DPLL solver). Default ON; `AY_EUF_ATOM_FILTER=0`
/// restores the legacy unfiltered behavior (every same-sorted equality in the
/// TermStore is a propagation candidate, even ones the SAT layer can never
/// receive). The filter only ever REMOVES provably-inert candidates: a
/// propagation on an equality with no SAT variable is dropped at the DPLL
/// boundary, so dropping it up front changes no verdict. `check()` (the
/// conflict authority) ignores `eq_terms`. Installed only on SAT-boundary solvers (see
/// `TheorySolver::set_sat_atom_terms`).
pub(crate) fn atom_filter_from_env() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| !matches!(std::env::var("AY_EUF_ATOM_FILTER").as_deref(), Ok("0")))
}

use crate::types::{
    CongruenceTable, ENode, EqualityReason, FuncAppMeta, MergeReason, UndoRecord, UnionFind,
};

/// EUF theory solver
pub struct EufSolver<'a> {
    pub(crate) terms: &'a TermStore,
    pub(crate) uf: UnionFind,
    pub(crate) assigns: HashMap<TermId, bool>,
    pub(crate) trail: Vec<(TermId, Option<bool>)>,
    pub(crate) scopes: Vec<usize>,
    pub(crate) dirty: bool,
    /// Equality graph: maps (min(a,b), max(a,b)) -> reason why a = b
    pub(crate) equality_edges: HashMap<(u32, u32), EqualityReason>,
    /// Pre-computed list of function application terms with their argument ids
    /// This avoids iterating all terms and cloning during congruence closure
    pub(crate) func_apps: Vec<FuncAppMeta>,
    /// #euf-guard-index: indices into `func_apps` of the apps that have at least
    /// one Bool-sorted argument. `bool_arg_model_is_congruent` cares ONLY about
    /// those, but scanned all of `func_apps` and `continue`d on the rest — once
    /// per check, on the hottest path in the division AY loses on CPU. Whether an
    /// app has a Bool arg is decided by argument SORTS, which never change, so
    /// this is computed once here and reused. Rebuilt with `func_apps` (the two
    /// are cleared together and `func_apps_init` gates both).
    pub(crate) bool_arg_app_idx: Vec<u32>,
    /// Index from term_id -> index in func_apps for O(1) lookup
    pub(crate) func_app_index: HashMap<u32, usize>,
    /// Whether func_apps has been initialized
    pub(crate) func_apps_init: bool,
    /// Whether ANY function application has a theory (Int/Real/BitVec) return
    /// sort — i.e. whether `func_app_values` tracking can ever fire. Computed
    /// once in `init_func_apps`. In pure QF_UF (all sorts uninterpreted) this is
    /// false, letting `record_assignment` skip the per-assignment
    /// `try_track_func_app_value` call entirely (it showed as ~20% of EUF
    /// self-time on QF_UF via `is_theory_func_app`, always returning false).
    /// Conservative default `true` (never skip until proven safe).
    pub(crate) has_theory_func_apps: bool,
    /// Bool-sorted terms that appear as arguments to UF applications.
    /// These must participate in the true/false equivalence-class merge so
    /// congruence closure fires on their parent applications — even when the
    /// Bool arg is a builtin (`and`/`or`/`=`/`distinct`) or connective
    /// (`not`/`xor`/`=>`/`ite`) term that the SAT layer owns. Populated lazily
    /// alongside `func_apps` in `init_func_apps()`. (#bool-arg-congruence)
    pub(crate) bool_uf_arg_terms: HashSet<u32>,
    /// Direct conflict detected when assigning term to both true and false
    /// Stores (term, positive_assignment) - the conflict is between term=true and term=false
    pub(crate) pending_conflict: Option<TermId>,

    // ========================================================================
    // Incremental E-graph structures (Phase 1 infrastructure)
    // ========================================================================
    /// E-nodes indexed by term ID - tracks class membership and parent pointers
    pub(crate) enodes: Vec<ENode>,
    /// Whether enodes have been initialized
    pub(crate) enodes_init: bool,
    /// Precomputed Bool-sortedness per term id (index = term_id.0). Term sorts
    /// are static, so this replaces the per-term `terms.sort(t) == Bool` check
    /// (which showed as ~25% of QF_UF profile self-time via `Sort::eq`) in the
    /// hot `incremental_merge_bool_valued_atoms` scan with an O(1) lookup.
    /// Populated alongside `enodes` in `init_enodes()`. Behaviour-identical.
    pub(crate) bool_sorted: Vec<bool>,
    /// Reusable scratch for the bool-valued-atom merge scan, to avoid a fresh
    /// Vec allocation on every propagation call. Behaviour-identical.
    pub(crate) bool_assigns_buf: Vec<(u32, bool)>,
    /// #euf-idle-rebuild: when true, the next `incremental_rebuild` must
    /// re-derive the merge queue from surviving state
    /// (`refill_incremental_merge_queue_from_state`) and run a FULL
    /// bool-valued-atom merge rescan — queued/applied merges may have been
    /// discarded or unwound. Set on pop/reset/soft_reset/unwind (every site
    /// that clears `to_merge` or unwinds e-graph merges); starts true. Between
    /// those events the queue is maintained incrementally by
    /// `record_assignment` / `assert_shared_equality` / `bool_merge_pending`,
    /// so the per-BCP-batch O(|assigns| log |assigns|) refill + rescan
    /// (measured 80s of an 81s hwbench firewire_tree.3 solve) collapses to
    /// once per backtrack.
    pub(crate) egraph_requeue_needed: bool,
    /// #euf-idle-rebuild: qualifying Bool-atom assignments recorded since the
    /// last bool-valued-atom merge pass (the incremental feed between
    /// `egraph_requeue_needed` full rescans).
    pub(crate) bool_merge_pending: Vec<(u32, bool)>,
    /// #euf-idle-rebuild: persistent anchor members of the true/false merge
    /// classes (the representatives the full rescan elected). `None` until the
    /// first qualifying assignment of that polarity.
    pub(crate) bool_true_anchor: Option<u32>,
    /// See `bool_true_anchor`.
    pub(crate) bool_false_anchor: Option<u32>,
    /// Persistent congruence table
    pub(crate) cong_table: CongruenceTable,
    /// Worklist of pending merges to process
    pub(crate) to_merge: VecDeque<MergeReason>,
    /// Undo trail for push/pop support
    pub(crate) undo_trail: Vec<UndoRecord>,
    /// Scope marks for undo trail
    pub(crate) undo_scopes: Vec<usize>,
    // ========================================================================
    // Nelson-Oppen shared equality state
    // ========================================================================
    /// Shared equalities from other theories (e.g., LIA discovering x = y).
    /// Format: (min(lhs,rhs), max(lhs,rhs)) -> reason_literals
    pub(crate) shared_equality_reasons: HashMap<(u32, u32), Vec<TheoryLit>>,
    /// Equality assertions already propagated to other theories.
    /// Tracks the equality term ID (= lhs rhs) to avoid duplicate propagation.
    pub(crate) propagated_eqs: HashSet<TermId>,
    /// Congruence-derived equalities already propagated to other theories.
    /// Tracks (min(lhs, rhs), max(lhs, rhs)) pairs for canonical ordering.
    /// Added for #319 - congruence-derived equalities must also be propagated.
    pub(crate) propagated_eq_pairs: HashSet<(TermId, TermId)>,
    /// Pending equalities to propagate to other theories (EUF→LIA direction).
    /// Populated by rebuild_closure(), drained by propagate_equalities().
    /// Format: (lhs, rhs, reason_literals)
    pub(crate) pending_propagations: Vec<(TermId, TermId, Vec<TheoryLit>)>,
    // ========================================================================
    // Function application value tracking (#385)
    // ========================================================================
    /// Tracks constant values for function applications returning Int/Real/BV.
    /// When `(= (f x) 100)` is asserted as true, stores (func_app_term_id, const_term_id).
    /// Used by extract_model() to provide actual values in EufModel.func_app_const_terms.
    pub(crate) func_app_values: HashMap<TermId, TermId>,
    /// Optional extraction scope for model building.
    ///
    /// In incremental mode, the append-only TermStore retains terms from popped
    /// scopes. Model extraction must ignore terms that are no longer reachable
    /// from the live assertion roots, or dead predicate applications can shadow
    /// live interpretations in the function table (#6813).
    pub(crate) model_term_scope: Option<HashSet<TermId>>,
    // ========================================================================
    // Pre-indexed equality terms (#2673)
    // ========================================================================
    /// Pre-computed list of equality terms: (eq_term_id, lhs, rhs).
    /// Avoids scanning all terms in propagate(). Initialized lazily like func_apps.
    pub(crate) eq_terms: Vec<(TermId, TermId, TermId)>,
    /// Whether eq_terms has been initialized
    pub(crate) eq_terms_init: bool,
    /// #euf-atom-filter: when `Some`, `init_eq_terms` restricts the
    /// negative-congruence propagation-candidate list to equalities whose
    /// `TermId` appears in this set — i.e. equalities that are SAT atoms (have
    /// a Boolean variable the DPLL solver can assign). `None` = unfiltered
    /// (every same-sorted equality is a candidate, the legacy behavior).
    /// Installed by SAT-boundary-only executors (pure QF_UF, UF+LIA) via
    /// `set_sat_atom_terms` BEFORE the first `propagate()`.
    pub(crate) sat_atom_eq_terms: Option<HashSet<TermId>>,
    // ========================================================================
    // Incremental positive-equality propagation (class_eqs index)
    // ========================================================================
    /// Inverse index: e-graph class representative -> indices into `eq_terms`
    /// whose lhs or rhs currently resolves to that representative. Lets
    /// `propagate_positive_equalities` visit only equalities touching classes
    /// that merged since the last scan, instead of rescanning every equality
    /// each call (the O(n_eqs)-per-propagate churn that dominated QF_UF). Built
    /// during a full scan and updated on merge by draining the absorbed class's
    /// list into the survivor's. Stale after pop — a full scan rebuilds it.
    pub(crate) class_eqs: HashMap<u32, Vec<usize>>,
    /// Class reps that gained members via merge since the last positive scan.
    /// The incremental scan visits only `class_eqs[rep]` for these reps.
    pub(crate) pos_dirty_reps: HashSet<u32>,
    /// When set, the next positive scan does a FULL rescan (and rebuilds
    /// `class_eqs`). True initially and after every `pop` (class state changed).
    pub(crate) pos_full_scan_needed: bool,
    /// Incremental positive scan; always `true` (the former `AY_EUF_INC_POS=0`
    /// legacy-full-rescan kill-switch is removed).
    pub(crate) inc_pos_enabled: bool,
    // ========================================================================
    // Incremental disequality propagation (diseq_pair_index)
    // ========================================================================
    /// Index of asserted disequalities keyed by their endpoints' CURRENT class
    /// representatives `(min_rep, max_rep) -> (lhs, rhs, eq_term)`. Lets
    /// `propagate_disequalities` react to new disequalities and merges instead
    /// of rebuilding the index from every assignment and rescanning every
    /// equality each call (the per-BCP O(assigns + n_eqs) churn that dominated
    /// QF_UFLIA model search). Kept current on merge by rekeying the absorbed
    /// representative's entries; stale after pop — a full scan rebuilds it.
    pub(crate) diseq_pair_index: HashMap<(u32, u32), (TermId, TermId, TermId)>,
    /// Inverse index: representative -> pair keys registered under it, for
    /// merge-time rekeying. May contain stale keys (tolerated: lookups into
    /// `diseq_pair_index` filter them).
    pub(crate) diseq_keys_by_rep: HashMap<u32, Vec<(u32, u32)>>,
    /// Negated equalities asserted since the last negative scan whose index
    /// entries (and propagation candidates) are resolved at the next
    /// `propagate_disequalities` call, after the closure rebuild.
    pub(crate) pending_neg_eqs: Vec<(TermId, TermId, TermId)>,
    /// Class reps that gained members via merge since the last negative scan.
    /// The incremental scan revisits `class_eqs[rep]` for these reps against
    /// `diseq_pair_index`.
    pub(crate) neg_dirty_reps: HashSet<u32>,
    /// When set, the next negative scan does a FULL rescan (and rebuilds
    /// `diseq_pair_index`). True initially and after every `pop`.
    pub(crate) neg_full_scan_needed: bool,
    /// Disequality-conflict candidates discovered eagerly: a merge that
    /// collapsed an indexed pair's two sides into one class, or a negated
    /// equality asserted over an already-merged pair. `check()` verifies each
    /// candidate against the CURRENT state (still asserted false, reps still
    /// equal) before reporting a conflict, so stale candidates are harmless.
    /// With the index current, every diseq violation passes through one of
    /// those two events, so `check_disequality_conflicts` can skip its
    /// full-assigns scan+sort in incremental mode.
    pub(crate) pending_diseq_conflicts: Vec<(TermId, TermId, TermId)>,
    /// Pair keys newly inserted into `diseq_pair_index` by `sync_diseq_index`
    /// and not yet matched against unassigned equalities. Consumed by the
    /// incremental negative propagation scan; cleared on pop (the full rescan
    /// re-derives everything).
    pub(crate) pending_diseq_match_keys: Vec<((u32, u32), (TermId, TermId, TermId))>,
    // ========================================================================
    // Watermark-cached term-store indexes (#euf-check-scans)
    // ========================================================================
    // check() used to rescan the WHOLE term store (constants) and all
    // assignments (distinct / Bool-congruence candidates) on every call —
    // thousands of BCP-time checks per second on QF_UFLIA model search. The
    // term store is append-only, so each index extends incrementally from a
    // watermark; membership never changes for already-scanned terms.
    /// Non-Bool constant terms, extended from `term_cache_watermark`.
    pub(crate) const_terms_cache: Vec<TermId>,
    /// `distinct` application terms, extended from `term_cache_watermark`.
    pub(crate) distinct_terms_cache: Vec<TermId>,
    /// Bool-congruence candidate terms (Bool-sorted Var / non-builtin App),
    /// extended from `term_cache_watermark`.
    pub(crate) bool_cong_candidates_cache: Vec<TermId>,
    /// Number of term-store entries already folded into the caches above.
    pub(crate) term_cache_watermark: usize,
    /// Whether the next FULL negative scan must run the cong-neg LOOKAHEAD
    /// over every candidate atom (#cong-neg-prop, pop-path cost fix).
    ///
    /// `true` initially and after reset/soft-reset/unwind (the SAT clause DB
    /// may have been rebuilt, so previously-emitted lookahead clauses are
    /// gone and must be re-derivable). `false` for full scans forced by a
    /// plain `pop()`: every lookahead implication proposed before the pop was
    /// emitted as a PERMANENT SAT clause (see `cong_neg_emitted` — the SAT
    /// layer keeps theory-propagation clauses with watches forever), so BCP
    /// re-fires it after backtracking without the theory recomputing it. A
    /// post-pop full scan therefore only needs the cheap direct-index
    /// candidate pass; re-running the O(n_eqs) lookahead sweep was the #1
    /// profile cost on QG-classification/NEQ (12.35M of 12.5M lookahead runs
    /// on iso_icl_repgen_sk003 came from post-pop full scans, ~0.03% hit
    /// rate, all dropped by the emit dedup). Missing one of the rare
    /// emit-time defensive skips this way costs only search guidance —
    /// `check()` remains the conflict/soundness authority.
    pub(crate) neg_full_scan_la_needed: bool,
    /// Incremental negative scan; always `true` (the former `AY_EUF_INC_NEG=0`
    /// legacy-full-rescan kill-switch is removed). Requires `inc_pos_enabled`
    /// (the incremental scan reads `class_eqs`).
    pub(crate) inc_neg_enabled: bool,
    /// Eager negative-congruence propagation (#cong-neg-prop): when the direct
    /// diseq-pair check misses, do a bounded merge-lookahead SIMULATION —
    /// would asserting this equality make two existing applications congruent
    /// whose classes carry an asserted disequality, either directly (depth 1)
    /// or through a short cascade of further congruence merges (depth >= 2)?
    /// If so, propagate the equality FALSE with a full congruence reason built
    /// from the live proof forest (nothing is cached, so reasons can never go
    /// stale). This is the A2 search-pruning fix: without it, the SAT solver
    /// walks into ~half of all EUF theory conflicts one decision at a time on
    /// finite-model QF_UF (PEQ family).
    /// `AY_EUF_CONG_NEG` kill switch doubles as the depth knob: `0` = off,
    /// `1` = one-step (default — cascade depths measured NEGATIVE, see
    /// `cong_neg_depth_from_env`), `2..=8` = cascade depth.
    /// Derived: `cong_neg_depth > 0`.
    pub(crate) cong_neg_enabled: bool,
    /// Max simulated-merge depth for the lookahead (hypothesis merge = 1).
    /// See `cong_neg_enabled`; 0 disables the lookahead entirely.
    pub(crate) cong_neg_depth: u32,
    /// Count of negative-congruence lookahead propagations emitted (#cong-neg-prop).
    pub(crate) cong_neg_propagation_count: u64,
    /// #cong-neg-backoff: adaptive-suspend enabled (env `AY_EUF_CONG_NEG_ADAPTIVE`,
    /// default true; `0` = legacy always-on). When false the backoff below is
    /// inert and the cascade lookahead runs on every candidate as before.
    pub(crate) cong_neg_adaptive: bool,
    /// #cong-neg-backoff: cascade lookahead currently suspended (a barren streak
    /// of non-firing runs on a large problem tripped the cap). Guidance-only, so
    /// suspension never affects soundness — see `cong_diseq_lookahead_memo`.
    /// #cong-neg-cold: has the cascade lookahead EVER fired in this solve?
    /// The size gate alone cannot separate the two workloads that matter:
    /// non-incremental QF_UF/NEQ (tiny, lookahead barren — costs 2.1-2.5x) and
    /// incremental CLEARSY (also under the gate, but the lookahead's rare fires
    /// are worth 49 check-sats). Firing history discriminates them where size
    /// does not: a solve that has never fired is a candidate for early suspend;
    /// one that has fired keeps the historical never-suspend behaviour.
    pub(crate) cong_neg_ever_fired: bool,
    pub(crate) cong_neg_suspended: bool,
    /// #cong-neg-backoff: consecutive non-firing full lookahead runs since the
    /// last fire. Resets to 0 on any fire; suspends at `CONG_NEG_BARREN_CAP`.
    pub(crate) cong_neg_barren: u32,
    /// #cong-neg-backoff: skipped-run counter while suspended; a re-probe fires
    /// once it reaches `CONG_NEG_REPROBE`.
    pub(crate) cong_neg_probe_skip: u32,
    /// Always `true` (the former `AY_EUF_EXPLAIN_NOSORT=0` kill-switch is
    /// removed): when true, proof-forest
    /// `explain` collects reasons across the whole recursion into one buffer and
    /// sorts+dedups ONCE at the top, instead of sorting+deduping at every
    /// recursive congruence sub-explain (O(depth) redundant sorts). Sound: the
    /// final reason SET is identical; only intermediate ordering differs.
    pub(crate) explain_nosort_enabled: bool,
    /// Reusable memo (taken/restored per top-level `explain` call) that skips
    /// re-explaining shared congruence sub-pairs — the profiled hot spot on
    /// congruence-heavy QF_UF. Sound by construction (see `ExplainMemo`); env
    /// `AY_EUF_EXPLAIN_MEMO=0` disables it for A/B. Stored here only to keep its
    /// capacity across calls; it is `mem::take`-n into a local for the recursion
    /// so re-entrant BFS-fallback `explain` calls each get their own.
    pub(crate) explain_memo: crate::explain::ExplainMemo,
    pub(crate) explain_memo_enabled: bool,
    /// Defer the (expensive, recursive) Nelson-Oppen congruence-propagation
    /// reason from congruence-discovery time (merge.rs) to DRAIN time
    /// (`propagate_equalities`), by queueing the equality with an empty reason
    /// and computing `explain(lhs,rhs)` only when a consumer actually drains it.
    /// In standalone QF_UF nothing ever drains `pending_propagations`, so the
    /// explain is never computed at all — a big win on congruence-heavy pure
    /// QF_UF; in combined N-O it is computed at drain (same total work, later).
    /// Default ON; `AY_EUF_LAZY_NOPROP=0` disables. Sound: `explain(lhs,rhs)` walks the same
    /// congruence proof-forest edge the eager arg-pair loop did, so the reason
    /// SET is identical; and any valid reason justifies the propagation.
    pub(crate) lazy_noprop_reasons: bool,
    // ========================================================================
    // Pre-indexed ITE terms (#5575)
    // ========================================================================
    /// Pre-computed list of ITE term indices (non-Bool sort only).
    /// Avoids scanning all terms in rebuild_closure/incremental_rebuild.
    pub(crate) ite_terms: Vec<u32>,
    /// Whether ite_terms has been initialized
    pub(crate) ite_terms_init: bool,
    /// #euf-ite-worklist: condition term id -> ITE terms guarded by it (built
    /// alongside `ite_terms`). Lets an assignment enqueue exactly the ITE terms
    /// it can possibly fire, instead of the sweep rescanning all of them.
    pub(crate) ite_by_cond: HashMap<u32, Vec<u32>>,
    /// ITE terms whose condition was assigned since the last sweep.
    pub(crate) pending_ite: Vec<u32>,
    /// Force the next sweep to scan ALL ite_terms. Set on the same events that
    /// set `egraph_requeue_needed` (pop / reset / soft_reset / unwind), where
    /// merges are discarded or unwound and the incremental worklist can no
    /// longer be trusted.
    pub(crate) ite_sweep_full_needed: bool,
    // ========================================================================
    // Reusable scratch buffers (#5575)
    // ========================================================================
    /// Scratch buffer for check() disequality collection (Stage 1)
    pub(crate) scratch_diseqs: Vec<(TermId, TermId, TermId)>,
    /// Scratch buffer for check() distinct constraints (Stage 2)
    pub(crate) scratch_distincts: Vec<(TermId, Vec<TermId>)>,
    /// Scratch buffer for check() constant conflict detection (Stage 3)
    pub(crate) scratch_rep_to_const: HashMap<u32, (TermId, Constant)>,
    /// Scratch buffer for check() Boolean congruence (Stage 4)
    pub(crate) scratch_bool_terms: Vec<(TermId, bool)>,
    /// Scratch buffer for derived-value Bool UF-arg terms in bool-congruence
    /// check (#bool-arg-congruence).
    pub(crate) scratch_bool_uf_args: Vec<u32>,
    /// Scratch buffer for check() Boolean rep tracking (Stage 4)
    pub(crate) scratch_rep_value: HashMap<u32, (TermId, bool)>,
    /// Scratch buffer for propagate() positive equality candidates
    pub(crate) scratch_potential_props: Vec<(TermId, TermId, TermId)>,
    /// Scratch buffer for propagate() negative propagation candidates
    pub(crate) scratch_neg_props: Vec<(TermId, TermId, TermId, TermId, TermId, TermId)>,
    /// Scratch buffer for propagate() negative-CONGRUENCE lookahead candidates
    /// (#cong-neg-prop): `(eq_term, lhs, rhs, cascade)` — asserting
    /// `lhs = rhs` would (through the cascade's simulated merges) make the
    /// cascade's `hit` applications congruent, and their simulated classes
    /// carry the cascade's asserted disequality, so `eq_term` is
    /// theory-entailed FALSE.
    pub(crate) scratch_cong_neg_props: Vec<(TermId, TermId, TermId, crate::types::CongNegCascade)>,
    /// Scan-local memo for the negative-congruence lookahead (#cong-neg-prop),
    /// keyed by the atom's endpoint CLASS pair `(min_rep, max_rep)` — the
    /// lookahead result depends only on the class pair, and one scan often
    /// visits many atoms over the same pair (totality clauses). Cleared at the
    /// start of every negative scan (the E-graph is frozen within a scan, so
    /// entries cannot go stale while the memo lives).
    pub(crate) scratch_cong_neg_memo:
        ay_core::kani_compat::DetHashMap<(u32, u32), Option<crate::types::CongNegCascade>>,
    /// #euf-guard-scratch: reusable congruence map + `Vec` pool for the
    /// transitive fixpoint inside `bool_arg_model_is_congruent`. That fixpoint
    /// built a fresh `DetHashMap` per guard call AND a `Vec<u32>` of argument
    /// representatives per func_app per round. The guard runs once per complete
    /// candidate model (~16k times on the heaviest Inc QF_Equality file), so
    /// both were pure allocator churn. Taken/restored per call, in the same
    /// style as `scratch_cong_neg_la`.
    pub(crate) scratch_bool_arg_cong: ay_core::kani_compat::DetHashMap<(u64, Vec<u32>), u32>,
    pub(crate) scratch_bool_arg_pool: Vec<Vec<u32>>,
    /// Reusable simulation state for the cascade lookahead (#cong-neg-prop):
    /// taken/restored per `cong_diseq_lookahead` call so the hot miss path
    /// allocates nothing.
    pub(crate) scratch_cong_neg_la: crate::types::CongNegScratch,
    /// Reusable buffer for one `class_eqs` bucket per dirty rep in the
    /// incremental scans (replaces a per-rep `Vec` clone on the hot path).
    pub(crate) scratch_class_eq_idxs: Vec<usize>,
    /// Reusable per-scan "eq atom already visited" set for the incremental
    /// scans (replaces a fresh allocation per scan).
    pub(crate) scratch_seen_eq_idxs: ay_core::kani_compat::DetHashSet<usize>,
    /// Clauses already emitted by the negative-congruence lookahead, keyed by
    /// `(propagated atom, FNV hash of the sorted reason set)` (#cong-neg-prop).
    /// The SAT layer stores every theory-propagation clause PERMANENTLY with
    /// watches (clause_add_theory.rs: "theory lemmas are always kept"), so BCP
    /// re-fires the implication after backtracking without the theory's help —
    /// re-emitting an identical clause only duplicates it in the clause DB and
    /// re-pays the explain() cost (NEQ033_size5: ~100k duplicate emissions,
    /// 9.6s -> 45s). Persistent across pops for exactly that reason; cleared
    /// on reset/soft_reset (the SAT clause DB is rebuilt then too).
    pub(crate) cong_neg_emitted: HashSet<(TermId, u64)>,
    /// Scratch buffer for rebuild_closure() equalities to propagate
    pub(crate) scratch_equalities: Vec<(TermId, TermId, TermId)>,
    /// Scratch buffer for rebuild_closure() shared equality keys
    pub(crate) scratch_shared_eq_keys: Vec<(u32, u32)>,
    // ========================================================================
    // Cached env vars (#2673)
    // ========================================================================
    /// Cached AY_DEBUG_EUF flag (avoids syscall per hot-path call)
    pub(crate) debug_euf: bool,
    /// Cached AY_DEBUG_EUF_NELSON_OPPEN flag
    pub(crate) debug_nelson_oppen: bool,
    /// Bool-argument congruence completeness merge. Permanently OFF
    /// process-wide (see `EufDebugFlags::bool_arg_congruence`): the merge is
    /// unsound in the false-UNSAT direction, so no environment variable can
    /// enable it — the former `AY_EUF_BOOL_ARG_CONGRUENCE`/`_MERGE` overrides
    /// were removed. The standalone EUF unit tests toggle it per-instance via
    /// `set_bool_arg_congruence`; the SOUND production guard is the
    /// `bool_arg_validate` model validation below.
    pub(crate) bool_arg_congruence: bool,
    /// Bool-arg validation flag (always ON at construction): SOUND post-SAT
    /// Bool-arg congruence model validation (downgrade Sat -> Unknown only).
    pub(crate) bool_arg_validate: bool,
    /// Transitive Bool-arg validation flag (always ON at construction): close
    /// congruence over the tentatively-merged Bool-arg apps before checking for
    /// a disequality/distinct violation, so nested cases (e.g. `f(fb(A))` vs
    /// `f(fb(B))` under a `distinct`) are caught.
    pub(crate) bool_arg_validate_transitive: bool,
    /// Bool-arg app pairs the last `bool_arg_model_is_congruent` call found to be
    /// FORCED equal by congruence under the candidate model — i.e. same function,
    /// same non-Bool argument representatives, same Bool-argument truth values.
    ///
    /// Recorded so a caller that sees the guard downgrade `Sat` -> `Unknown` can
    /// repair the model instead of giving up: inject `(/\ a_i = b_i) -> f(a)=f(b)`
    /// for exactly these pairs and re-solve (targeted CEGAR). This set is
    /// MODEL-SPECIFIC and small, which is the point — the blanket alternative of
    /// injecting a lemma for every Bool-arg pair in the reachable set is measured
    /// DEAD in incremental mode (`executor/theories/euf.rs`: CLEARSY completeness
    /// collapses 121 -> ~50 solved check-sats as the fresh equality atoms inflate
    /// the EUF proof-forest and the per-conflict `explain()` walk).
    ///
    /// Diagnostic only: nothing in the solver reads it, so populating it cannot
    /// change any verdict.
    pub(crate) last_bool_arg_forced_edges: Vec<(TermId, TermId)>,
    // Per-theory runtime statistics (#4706)
    pub(crate) check_count: u64,
    pub(crate) conflict_count: u64,
    pub(crate) propagation_count: u64,
    // ========================================================================
    // Disequality propagation state (#8469)
    // ========================================================================
    /// Dirty epoch counter — incremented on every E-graph class merge AND
    /// every new negated equality assertion. Used for dirty tracking:
    /// collect_disequalities_for_propagation can skip re-scanning when no
    /// merges or new disequalities have occurred since the last scan.
    /// Also bumped on pop() since undo-replay changes the E-graph.
    pub(crate) merge_epoch: u64,
    /// Epoch at which disequalities were last scanned. When equal to
    /// merge_epoch, collect_disequalities_for_propagation returns immediately.
    pub(crate) diseq_scan_epoch: u64,
    // (shared_interface_terms removed in #8469 cleanup — superseded by
    // shared_arith_terms, which is the only field populated by DPLL adapters.)
    // ========================================================================
    // Shared disequalities from other theories (#8469)
    // ========================================================================
    /// Disequalities asserted by other theories (e.g., LIA discovering x != y
    /// from tight bounds). Stored as canonical `(min(lhs,rhs), max(lhs,rhs))`
    /// -> reason literals. Used to detect conflicts when merging equivalence
    /// classes: if `a` and `b` are in a shared disequality and a merge makes
    /// them equal, that's a conflict.
    pub(crate) shared_disequalities: HashMap<(u32, u32), Vec<TheoryLit>>,
    /// Conflict detected in assert_shared_disequality when lhs and rhs are
    /// already in the same equivalence class. Drained by check().
    pub(crate) pending_shared_diseq_conflict: Option<Vec<TheoryLit>>,
    // ========================================================================
    // Soundness: poisoned flag (#8454)
    // ========================================================================
    /// Set when an internal invariant violation is detected (e.g., trail
    /// underflow in pop()). When true, the next check() returns
    /// TheoryResult::Unknown to prevent the solver from producing incorrect
    /// results based on corrupted E-graph state.
    pub(crate) poisoned: bool,
    // ========================================================================
    // Nelson-Oppen disequality propagation (#8469)
    // ========================================================================
    /// Shared arithmetic interface terms for disequality propagation.
    /// Set by the combined solver adapter via `set_shared_arith_terms()`.
    /// When populated, `propagate_equalities()` collects EUF-implied
    /// disequalities and returns them in the `EqualityPropagationResult`.
    pub(crate) shared_arith_terms: Vec<TermId>,
    /// Deduplication set for disequality propagation (#8455).
    /// Tracks canonical `(min, max)` TermId pairs already propagated to
    /// avoid re-propagating in subsequent fixpoint iterations.
    pub(crate) propagated_diseq_pairs: HashSet<(TermId, TermId)>,
    // ========================================================================
    // Persistent propagation output buffer (#8599, Finding 6)
    // ========================================================================
    /// Reusable output buffer for `propagate()`. Avoids allocating a fresh
    /// `Vec<TheoryPropagation>` on every call. Pattern: `mem::take` from
    /// field, `clear()`, fill, store back, `drain(..).collect()` to return.
    pub(crate) propagation_output_buf: Vec<TheoryPropagation>,
    // ========================================================================
    // Fine-grained disequality dirty tracking (#8471)
    // ========================================================================
    /// Representatives involved in merges since the last disequality scan.
    /// When `collect_disequalities_for_propagation` runs, only false_eqs
    /// whose `rep_a` or `rep_b` is in this set (or newly asserted) need
    /// processing. This avoids the O(|false_eqs| * |class|^2) full scan
    /// on every N-O iteration when only a few classes changed.
    pub(crate) dirty_merge_reps: HashSet<u32>,
    /// Negated equalities asserted since the last disequality scan.
    /// These must be processed regardless of whether their reps are dirty,
    /// because they represent new disequality constraints.
    pub(crate) new_negated_eqs: Vec<(TermId, TermId, TermId)>,
    /// True when at least one real e-class merge happened since the last
    /// [`Self::take_dt_merge_dirty`] call. Change-feed gate for the lazy
    /// datatype propagation pass (`DESIGN_lazy_dt.md` stage D1): the pass
    /// only re-scans the e-graph when a merge could have produced new
    /// constructor commitments. Intentionally NOT cleared on pop: a weaker
    /// post-pop e-graph cannot enable new propagations, and any new merge
    /// after the pop sets it again.
    pub(crate) dt_merge_dirty: bool,
    // ========================================================================
    // Incremental UF-mirror sync (dirty-node tracking)
    // ========================================================================
    /// E-nodes whose equivalence-class representative changed since the last
    /// `sync_egraph_to_uf`. Only these nodes need their `uf.parent[node]` entry
    /// refreshed; every other node's mirror entry is still equal to its current
    /// `enode_find_const`. Populated by `incremental_merge` (absorbed-class nodes)
    /// and by `pop`'s `SetRoot` undo replay (nodes whose root is restored). Path
    /// compression (`enode_find` writing `root`) is intentionally NOT tracked: it
    /// shortens the root chain but never changes the value `enode_find_const`
    /// returns, so the mirror value is unaffected.
    pub(crate) uf_dirty_nodes: HashSet<u32>,
    /// When set, the next `sync_egraph_to_uf` does a FULL O(n) rebuild of the UF
    /// mirror (and clears `uf_dirty_nodes`). True initially and whenever the
    /// mirror's "all-untracked-nodes-are-current" invariant cannot be trusted
    /// (enodes grew, or a hard reset occurred).
    pub(crate) uf_full_sync_needed: bool,
    /// Incremental dirty-node UF-mirror sync; always `true` (the former
    /// `AY_EUF_INC_SYNC=0` legacy full-O(n)-sync kill-switch is removed).
    pub(crate) inc_sync_enabled: bool,
    /// Incremental (trail-based) congruence-table restore on pop
    /// (#euf-inc-cong-undo). When `true` (default), `incremental_merge` records
    /// `CongSet`/`CongRemove` undo entries for every `cong_table` mutation and
    /// pop() replays them instead of running the full O(func_apps) rebuild.
    /// This is the dominant per-pop cost on the giant Certora QF_UFLIA files
    /// (one pop rebuilds 10^5+ signatures). Kill-switch: `AY_EUF_INC_CONG_UNDO=0`
    /// falls back to the from-scratch rebuild.
    pub(crate) inc_cong_undo_enabled: bool,
    /// Minimum `func_apps` count for the incremental pop-restore to activate
    /// (#euf-inc-cong-undo size gate). Defaults to `CONG_UNDO_MIN_FUNC_APPS`;
    /// `AY_EUF_CONG_UNDO_MIN=<n>` overrides it (used by tests/fuzz to exercise
    /// the incremental path on small inputs, where the debug key-set assert
    /// then validates every pop).
    pub(crate) cong_undo_min_func_apps: usize,
    /// #euf-inc-undo-adaptive: latched once the rebuild work this solve has
    /// ALREADY spent overtakes the undo work it WOULD have spent. Governs both
    /// the congruence-table and disequality-index undo paths — same failure
    /// mode, same safe switch point. Only ever set with no open scope.
    pub(crate) undo_latched: bool,
    /// Accrued cost of the from-scratch path: `func_apps.len()` per rebuild pop.
    pub(crate) rebuild_work: u64,
    /// Accrued cost the incremental path would have had: one unit per parent
    /// reinserted during a merge, counted whether or not it is active so the
    /// two sides are always comparable.
    pub(crate) undo_work: u64,
    /// Incremental (trail-based) disequality-pair-index restore on pop
    /// (#euf-inc-diseq-undo). When active (default; kill-switch
    /// `AY_EUF_INC_DISEQ_UNDO=0`), `incremental_merge` (rekey) and
    /// `sync_diseq_index` record `DiseqSet`/`DiseqRemove` undo entries for every
    /// `diseq_pair_index` mutation, and pop() replays them instead of running
    /// the from-scratch O(|assigns|) rebuild (the confirmed #1 Certora
    /// search-phase cost: propagate_disequalities' index rebuild after every
    /// pop). Mirrors `inc_cong_undo_enabled`.
    pub(crate) inc_diseq_undo_enabled: bool,
    /// Minimum `func_apps` count for the incremental diseq pop-restore to
    /// activate (#euf-inc-diseq-undo size gate). Defaults to
    /// `CONG_UNDO_MIN_FUNC_APPS`; `AY_EUF_DISEQ_UNDO_MIN=<n>` overrides it
    /// (tests/fuzz set it to 0 to exercise the incremental path on small inputs,
    /// where the debug key-set cross-check then validates every pop). The
    /// trail-undo trades the O(|assigns|) rebuild for a small per-merge/per-sync
    /// overhead, so — like the cong-undo — it is a net loss on merge-heavy /
    /// pop-light small files and only pays off on the giant industrial files.
    pub(crate) diseq_undo_min_func_apps: usize,
    /// #euf-inc-diseq-undo: set by an incremental pop after it restores
    /// `diseq_pair_index` via the undo trail. The next full negative scan
    /// (`propagate_disequalities_full_scan`) checks this and SKIPS its
    /// O(|assigns|) clear+rebuild — the index is already exact — running only
    /// the candidate scan (which is byte-identical to baseline, operating on
    /// identical index CONTENTS). Reset by that scan and by every index-clearing
    /// path (init/reset/soft_reset/unwind/fallback pop).
    pub(crate) neg_index_prebuilt: bool,
    /// #euf-inc-diseq-undo: scope depth (`self.scopes.len()`) at which
    /// `diseq_pair_index` was last built FROM SCRATCH (a full negative scan).
    /// Entries baked in below this depth carry no undo records, so the
    /// incremental pop-restore is valid only down to it; a pop that lands below
    /// `diseq_index_base_depth` falls back to a from-scratch rebuild. In the
    /// steady case the first full scan runs at depth 0, so the guard never
    /// fires; it is insurance against a full scan forced at depth > 0.
    pub(crate) diseq_index_base_depth: usize,
    /// #euf-inc-diseq-undo: set by an incremental pop, whose undo-trail replay
    /// restores the FORWARD index (`diseq_pair_index`) exactly but leaves the
    /// INVERSE index (`diseq_keys_by_rep`) keyed by the pre-pop representatives.
    /// The inverse index is then rebuilt lazily from the restored forward index
    /// at the first site that reads/writes it (`ensure_diseq_keys_fresh`), so a
    /// deep multi-level backtrack pays the O(|diseqs|) rebuild once, not once
    /// per popped level.
    pub(crate) diseq_keys_dirty: bool,
    // ========================================================================
    // Verification-only mode (#8529 perf)
    // ========================================================================
    /// When `true`, this solver instance is used ONLY to recompute the
    /// Sat/Unsat verdict of `check()` for the soundness verifier
    /// (`verify_euf_conflict` / `verify_euf_propagation`). The caller reads
    /// nothing but the verdict and discards all reason vectors.
    ///
    /// In this mode `incremental_merge` performs the congruence merges that
    /// determine the verdict exactly as normal, but SKIPS building the
    /// Nelson-Oppen propagation reason vectors (the un-memoized recursive
    /// `explain()` calls that queue `pending_propagations`). Those reasons are
    /// consumed only by `propagate_equalities()`, which the verifier never
    /// calls (`check()` never reads `pending_propagations`), so skipping them
    /// is provably verdict-preserving while removing the dominant cost on the
    /// per-conflict / per-propagation re-verification path.
    ///
    /// MUST remain `false` on the real solve-path solver, whose drained
    /// `pending_propagations` ARE used as SAT theory propagations.
    pub(crate) verify_only: bool,
    /// Verification scope (#A2 PEQ perf): when set, `init_func_apps` registers
    /// ONLY function applications inside this subterm-closed term set. Used
    /// exclusively by `verify_only_scoped` verification instances, which
    /// assert a handful of literals and read only the check() verdict.
    ///
    /// VERDICT-PRESERVATION: EUF (un)satisfiability of a conjunction of
    /// literals is decided by congruence closure over the SUBTERM-CLOSED set
    /// of those literals (the classic congruence-closure decision procedure).
    /// Congruence steps only ever equate terms that already exist in the
    /// closure being computed, and an application outside the asserted
    /// literals' subterm closure can never appear in any derivation from
    /// them. Registering the (unrelated) rest of the term store's apps only
    /// adds parent-list/congruence-table churn on every class merge — the
    /// dominant cost of per-conflict verification on congruence-heavy QF_UF
    /// (PEQ: one fresh O(all-apps) solver per theory conflict).
    ///
    /// MUST remain `None` on the real solve-path solver.
    pub(crate) func_app_scope: Option<HashSet<u32>>,
    /// #euf-prop-gap: env-gated (`AY_EUF_GAP_STATS=1`) profiling counters for
    /// the eager-propagation gap. Zero-cost when disabled (one bool test on
    /// the assert path). Flushed to process-wide statics on Drop.
    pub(crate) gap_stats_enabled: bool,
    pub(crate) gap_stats: PropGapStats,
    // ========================================================================
    // Lazy propagation justifications (#8467 protocol, #euf-lazy-explain)
    // ========================================================================
    /// Whether the consumer of `propagate()` supports the lazy justification
    /// protocol (`reason_data` + `explain_propagation`). Set to `true` by the
    /// eager SAT extension via `set_lazy_propagation_supported`; stays `false`
    /// for consumers that turn `reason` directly into clauses (legacy DpllT
    /// loop, verification instances). Kill switch: `AY_EUF_LAZY_EXPLAIN=0`
    /// forces eager reasons even when the consumer supports lazy.
    pub(crate) lazy_explain_enabled: bool,
    /// Emission counter driving the warmup-then-sample EAGER carve-out (see
    /// `lazy_emit_gate`): the first `LAZY_EMIT_WARMUP` positive/diseq
    /// propagations per solver and every 64th thereafter keep materialized
    /// reasons so the extension's structural + sampled semantic verification
    /// gates retain their coverage cadence on the eager stream.
    pub(crate) lazy_emit_counter: u64,
    /// Disequality witness for lazily-emitted NEGATIVE propagations:
    /// propagated eq atom -> `(diseq_a, diseq_b, diseq_term)` captured at
    /// emit time. Overwritten on re-emission; entries are validated in full
    /// against the CURRENT e-graph/assignment state at materialization time,
    /// so stale entries can only cause a (sound) rejection, never a wrong
    /// reason. Cleared on reset/soft_reset.
    pub(crate) lazy_neg_witness: HashMap<TermId, (TermId, TermId, TermId)>,
    /// Lazy propagations emitted (reason_data set, empty reason Vec).
    pub(crate) lazy_emitted_count: u64,
    /// Lazy propagations whose reason was actually materialized on demand.
    pub(crate) lazy_explained_count: u64,
    /// Lazy materializations rejected (state moved on / validation failed);
    /// the SAT layer demotes these to decisions (sound).
    pub(crate) lazy_explain_rejected_count: u64,
}

/// #euf-prop-gap: counters measuring how often the SAT layer assigns an
/// equality atom whose value the e-graph (stale pre-batch view) already
/// entails (`*_redundant` — a propagation would have saved the assignment)
/// or contradicts (`*_conflict` — a propagation would have PREVENTED the
/// upcoming theory conflict). Merge counts are split by reason kind to
/// locate WHEN entailments arise (BCP-time direct/congruence merges vs
/// final-check-time Nelson-Oppen shared merges).
#[derive(Default, Debug)]
pub(crate) struct PropGapStats {
    /// New equality-atom assignments seen by `record_assignment`.
    pub eq_asserts: u64,
    /// Asserted TRUE while sides already co-class (redundant assign).
    pub pos_redundant: u64,
    /// Asserted FALSE while sides already co-class (avoidable conflict).
    pub neg_conflict: u64,
    /// Asserted TRUE while classes diseq-entailed (avoidable conflict).
    pub pos_conflict: u64,
    /// Asserted FALSE while classes diseq-entailed (redundant assign).
    pub neg_redundant: u64,
    /// Applied merges by reason kind.
    pub merges_direct: u64,
    pub merges_congruence: u64,
    pub merges_shared: u64,
    pub merges_other: u64,
    /// Emission-path split: positive-equality / direct-diseq proposals, and
    /// how many were EXACT (atom, reason-set) repeats of an earlier emission
    /// (i.e., a clause the SAT layer already stores permanently).
    pub pos_emitted: u64,
    pub pos_dup: u64,
    pub neg_emitted: u64,
    pub neg_dup: u64,
    /// Dedup probe set for the duplicate counters above (profiling only).
    pub emitted_probe: ay_core::kani_compat::DetHashSet<(TermId, u64, bool)>,
}

impl PropGapStats {
    /// Order-insensitive hash of a reason set (profiling only): XOR of
    /// per-literal FNV-1a hashes, so unsorted emission order doesn't matter.
    pub(crate) fn reason_hash(reasons: &[TheoryLit]) -> u64 {
        let mut acc: u64 = 0;
        for l in reasons {
            let mut h: u64 = 0xcbf2_9ce4_8422_2325;
            let mut mix = |b: u64| {
                h ^= b;
                h = h.wrapping_mul(0x0000_0100_0000_01B3);
            };
            mix(u64::from(l.term.0));
            mix(u64::from(l.value));
            acc ^= h;
        }
        acc
    }

    /// Record an emission on `path_pos` (true = positive path); returns
    /// whether it was an exact repeat.
    pub(crate) fn record_emission(&mut self, term: TermId, reasons: &[TheoryLit], path_pos: bool) {
        let h = Self::reason_hash(reasons);
        let dup = !self.emitted_probe.insert((term, h, path_pos));
        if path_pos {
            self.pos_emitted += 1;
            if dup {
                self.pos_dup += 1;
            }
        } else {
            self.neg_emitted += 1;
            if dup {
                self.neg_dup += 1;
            }
        }
    }
}

impl PropGapStats {
    /// Emit the cumulative per-instance counters (#euf-prop-gap). Called
    /// periodically from `record_assignment` (a `Drop` impl on `EufSolver`
    /// would force the `terms` borrow to live to end-of-scope and break the
    /// pipeline macros' NLL patterns, so periodic printing it is).
    pub(crate) fn print(&self, propagation_count: u64) {
        ay_core::safe_eprintln!(
            "[EUF-GAP] eq_asserts={} pos_redundant={} neg_conflict={} pos_conflict={} neg_redundant={} | merges direct={} cong={} shared={} other={} | sat_props={} | pos_emitted={} pos_dup={} neg_emitted={} neg_dup={}",
            self.eq_asserts,
            self.pos_redundant,
            self.neg_conflict,
            self.pos_conflict,
            self.neg_redundant,
            self.merges_direct,
            self.merges_congruence,
            self.merges_shared,
            self.merges_other,
            propagation_count,
            self.pos_emitted,
            self.pos_dup,
            self.neg_emitted,
            self.neg_dup,
        );
    }
}

/// #euf-inc-cong-undo size gate. The from-scratch `cong_table` rebuild in pop()
/// is O(func_apps); the incremental trail-undo trades it for a small per-merge
/// overhead (two extra undo-record pushes per reinserted parent). That trade is
/// a NET LOSS on merge-heavy / pop-light solves whose func_apps set is small
/// enough that the rebuild was already cheap (measured: `QF_UF_fischer.7`,
/// ~1.5k asserts, +17% wall), and a large WIN only when func_apps is big enough
/// that a single rebuild dominates (the giant Certora QF_UFLIA files, 10^5+
/// func_apps). Below this floor we keep the byte-identical baseline rebuild, so
/// the change can never regress a normal-sized file. `func_apps` is frozen after
/// `init_func_apps`, so the gate is constant within a solve (record and replay
/// decisions always agree).
pub(crate) const CONG_UNDO_MIN_FUNC_APPS: usize = 16384;

/// #euf-inc-undo-adaptive: no tuned threshold — the switch is driven by the two
/// costs themselves, both counted at run time.
///
/// The decision is a straight comparison: a from-scratch pop costs O(func_apps),
/// and incremental undo costs roughly one record per parent reinserted during a
/// merge. Both are countable, so instead of guessing a size or a pop count, the
/// solver accumulates the rebuild work it has ALREADY spent and the undo work it
/// WOULD have spent, and switches when the former overtakes the latter.
///
/// This is why a static gate could not win here. Measured on a 600-file SQ
/// QF_Equality sample, two interleaved rounds each:
///   floor 16384  249.0s   — better on the broad mix (mostly pop-light)
///   no floor     257.0s   — but 1.50x FASTER on the 10 pop-heavy NEQ files,
///                           and turns NEQ006_size6 from `unknown` into `unsat`
/// Neither setting is right for both workloads, and a pop-count threshold is
/// just a third magic number. Comparing the accrued costs needs no constant and
/// adapts per solve.
/// #euf-inc-diseq-undo size gate. Borrowed `CONG_UNDO_MIN_FUNC_APPS` (16384)
/// until it was measured independently, and the two turn out NOT to behave the
/// same way. For the disequality index the incremental path is not merely
/// faster — it is MORE COMPLETE.
///
/// Measured on SQ QF_Equality (600-file sample): 598/600 solved with the
/// rebuild path, 599/600 with the incremental one, 0 wrong either way. The file
/// is `QF_AX/swap/swap_invalid_t1_np_sf_ai_00010_009.cvc.smt2`, declared `sat`
/// and confirmed `sat` by z3, which the rebuild path abandons as `unknown` after
/// 4.2s while the incremental path answers in 2.0s. That is a correct answer the
/// O(|assigns|) rebuild was LOSING, so gating it behind a size threshold costs
/// completeness, not just time.
///
/// The pop-light case the congruence gate protects (`QF_UF_fischer.7`) is
/// unaffected here (0.11s / 0.01s either way), so there is no measured reason to
/// keep a floor at all.
pub(crate) const DISEQ_UNDO_MIN_FUNC_APPS: usize = 0;

impl<'a> EufSolver<'a> {
    /// Whether the incremental (trail-based) cong_table pop-restore is active
    /// for THIS solve: opted in (`AY_EUF_INC_CONG_UNDO` != 0) AND the func_apps
    /// set is large enough that skipping the O(func_apps) rebuild pays for the
    /// per-merge undo overhead (see `CONG_UNDO_MIN_FUNC_APPS`).
    #[inline]
    pub(crate) fn cong_undo_active(&self) -> bool {
        self.inc_cong_undo_enabled
            && (self.func_apps.len() >= self.cong_undo_min_func_apps || self.undo_latched)
    }

    /// #euf-inc-cong-undo: consider switching a backtrack-heavy solve over to
    /// incremental congruence undo.
    ///
    /// SAFETY, and the reason this is a separate method: `pop()` chooses replay
    /// vs rebuild by calling `cong_undo_active()`, so a scope must never be
    /// undone in replay mode if its merges were recorded in rebuild mode. The
    /// switch is therefore taken ONLY with NO OPEN SCOPE. Entries below the
    /// first scope mark are never replayed (pop only rewinds to its mark), so
    /// once there is no open scope every future scope records and replays
    /// consistently. That restores exactly the invariant the constant size gate
    /// gave for free.
    ///
    /// Note `undo_trail.is_empty()` is the WRONG condition and was tried first:
    /// level-0 merges from top-level assertions sit in the trail permanently, so
    /// it is essentially never empty and the latch never fires.
    pub(crate) fn maybe_latch_undo(&mut self) {
        if !self.undo_latched
            && self.inc_cong_undo_enabled
            && self.rebuild_work > self.undo_work
            && self.undo_scopes.is_empty()
        {
            self.undo_latched = true;
        }
    }

    /// #euf-inc-cong-undo safety net: after the incremental (trail-based)
    /// pop-restore of the congruence table, assert its signature key set is
    /// IDENTICAL to a from-scratch rebuild's. Both must equal "the set of
    /// distinct live signatures over `func_apps` under the restored roots".
    /// A mismatch means a missing/extra entry — i.e. an incomplete congruence
    /// closure that could hide a conflict. Debug/test/fuzz only.
    #[cfg(debug_assertions)]
    pub(crate) fn debug_assert_cong_table_key_set_matches_rebuild(&self) {
        let mut rebuilt = std::collections::BTreeSet::new();
        for meta in &self.func_apps {
            let sig = CongruenceTable::make_signature(meta.func_hash, &meta.args, &self.enodes);
            rebuilt.insert(sig);
        }
        let live = self.cong_table.signature_set();
        debug_assert_eq!(
            live,
            rebuilt,
            "BUG(#euf-inc-cong-undo): cong_table key set after incremental \
             pop-restore diverged from a from-scratch rebuild \
             (live={} entries, rebuilt={} entries)",
            live.len(),
            rebuilt.len()
        );
    }

    /// Whether the incremental (trail-based) `diseq_pair_index` pop-restore is
    /// active for THIS solve: opted in (`AY_EUF_INC_DISEQ_UNDO` != 0) AND the
    /// func_apps set is large enough that skipping the O(|assigns|) rebuild pays
    /// for the per-merge/per-sync undo overhead (see the size-gate rationale on
    /// `CONG_UNDO_MIN_FUNC_APPS`). `func_apps` is frozen after `init_func_apps`,
    /// so the decision is constant within a solve — record and replay always
    /// agree on whether entries were trailed.
    #[inline]
    pub(crate) fn diseq_undo_active(&self) -> bool {
        // #euf-inc-undo-latch: same size-gate problem as `cong_undo_active` — a
        // small but backtrack-heavy solve pays an O(|assigns|) rebuild per pop.
        // Measured on SQ QF_Equality (600-file sample): enabling this takes the
        // division from 598/600 to 599/600 solved, 0 wrong, and is slightly
        // faster. An extra ANSWER outranks the CPU either way.
        self.inc_diseq_undo_enabled
            && (self.func_apps.len() >= self.diseq_undo_min_func_apps || self.undo_latched)
    }

    /// #euf-inc-diseq-undo safety net: after the incremental (trail-based)
    /// pop-restore of `diseq_pair_index`, assert its KEY SET (the set of live
    /// disequal rep-pairs `(min_rep,max_rep)`) is IDENTICAL to a from-scratch
    /// rebuild's — the same set the `propagate_disequalities_full_scan` first
    /// loop would produce from the surviving assignments. A missing key hides a
    /// disequality (potential missed conflict / false SAT); an extra key invents
    /// one (potential false conflict). Only the canonical WITNESS per key may
    /// legitimately differ (any disequality between the two classes is a valid
    /// witness, re-validated at every consumption site), so witnesses are not
    /// compared. Debug/test/fuzz only.
    #[cfg(debug_assertions)]
    pub(crate) fn debug_assert_diseq_index_matches_rebuild(&self) {
        let mut rebuilt: std::collections::BTreeSet<(u32, u32)> = std::collections::BTreeSet::new();
        for (&lit_term, &value) in &self.assigns {
            if value {
                continue;
            }
            if let Some((a, b)) = self.decode_eq(lit_term) {
                if self.terms.sort(a) != self.terms.sort(b) {
                    continue;
                }
                if (a.0 as usize) >= self.enodes.len() || (b.0 as usize) >= self.enodes.len() {
                    continue;
                }
                let (a_rep, b_rep) = (self.enode_find_const(a.0), self.enode_find_const(b.0));
                if a_rep == b_rep {
                    continue; // conflict pair — never indexed
                }
                rebuilt.insert((a_rep.min(b_rep), a_rep.max(b_rep)));
            }
        }
        let live: std::collections::BTreeSet<(u32, u32)> =
            self.diseq_pair_index.keys().copied().collect();
        debug_assert_eq!(
            live,
            rebuilt,
            "BUG(#euf-inc-diseq-undo): diseq_pair_index key set after incremental \
             pop-restore diverged from a from-scratch rebuild \
             (live={} entries, rebuilt={} entries)",
            live.len(),
            rebuilt.len()
        );
    }

    /// #euf-inc-diseq-undo: rebuild the inverse index `diseq_keys_by_rep` from
    /// the (already restored) `diseq_pair_index`. The undo-trail replay restores
    /// the forward index exactly but leaves the inverse index keyed by the
    /// pre-pop representatives; an incomplete inverse index would let a later
    /// merge miss a rekey and strand a stale forward key. Rebuilding from the
    /// forward index is O(|diseqs|) (a handful of pushes per active
    /// disequality, no `decode_eq`/`find` per assignment) — vastly cheaper than
    /// the O(|assigns|) full rebuild it replaces, and exact by construction.
    pub(crate) fn rebuild_diseq_keys_by_rep(&mut self) {
        self.diseq_keys_by_rep.clear();
        for (&key, _) in &self.diseq_pair_index {
            self.diseq_keys_by_rep.entry(key.0).or_default().push(key);
            self.diseq_keys_by_rep.entry(key.1).or_default().push(key);
        }
    }

    /// #euf-inc-diseq-undo: rebuild `diseq_keys_by_rep` from the restored
    /// forward index iff an incremental pop marked it stale. Called at every
    /// site that reads or extends the inverse index after a pop
    /// (`incremental_merge` rekey, `sync_diseq_index`, the prebuilt full-scan
    /// candidate pass) so the rebuild happens exactly once, lazily, before first
    /// use — no matter how many levels a single backtrack popped.
    #[inline]
    pub(crate) fn ensure_diseq_keys_fresh(&mut self) {
        if self.diseq_keys_dirty {
            self.rebuild_diseq_keys_by_rep();
            self.diseq_keys_dirty = false;
        }
    }

    #[inline]
    pub(crate) fn debug_assert_enode_index(&self, term: u32, context: &str) {
        debug_assert!(
            (term as usize) < self.enodes.len(),
            "BUG: {context}: out-of-bounds term id {term} (enodes len={})",
            self.enodes.len()
        );
    }

    #[inline]
    pub(crate) fn debug_assert_enode_root_fixed_point(&self, rep: u32, context: &str) {
        debug_assert!(
            (rep as usize) < self.enodes.len() && self.enodes[rep as usize].root == rep,
            "BUG: {context}: representative {rep} must be a fixed-point root (enodes len={})",
            self.enodes.len()
        );
    }

    #[inline]
    pub(crate) fn debug_assert_solver_term_index(&self, term: TermId, context: &str) {
        debug_assert!(
            (term.0 as usize) < self.terms.len(),
            "BUG: {context}: term {} out of range (term store len={})",
            term.0,
            self.terms.len()
        );
    }

    #[inline]
    pub(crate) fn debug_assert_explain_lca(&self, lca: u32, root: u32) {
        debug_assert!(
            (lca as usize) < self.enodes.len(),
            "BUG: explain LCA out of bounds: {lca} (enodes len={})",
            self.enodes.len()
        );
        debug_assert_eq!(
            self.find_proof_root(lca),
            root,
            "BUG: explain LCA must stay in the same proof tree"
        );
    }

    #[cfg(debug_assertions)]
    pub(crate) fn debug_assert_enode_class_integrity(&self, root: u32, context: &str) {
        let root_in_bounds = (root as usize) < self.enodes.len();
        debug_assert!(
            root_in_bounds,
            "BUG: {context}: root {root} out of bounds (enodes len={})",
            self.enodes.len()
        );
        if !root_in_bounds {
            return;
        }
        self.debug_assert_enode_root_fixed_point(root, context);

        let start = root;
        let mut curr = root;
        let mut count = 0u32;
        let max_nodes = self.enodes.len() as u32;

        loop {
            let curr_in_bounds = (curr as usize) < self.enodes.len();
            debug_assert!(
                curr_in_bounds,
                "BUG: {context}: class walk hit out-of-bounds node {curr} (enodes len={})",
                self.enodes.len()
            );
            if !curr_in_bounds {
                return;
            }
            debug_assert_eq!(
                self.enode_find_const(curr),
                root,
                "BUG: {context}: node {curr} in class walk does not map to root {root}"
            );
            count += 1;
            debug_assert!(
                count <= max_nodes,
                "BUG: {context}: class walk exceeded enode count while traversing root {root}"
            );
            let next = self.enodes[curr as usize].next;
            let next_in_bounds = (next as usize) < self.enodes.len();
            debug_assert!(
                next_in_bounds,
                "BUG: {context}: class walk next pointer out of bounds: {next} (enodes len={})",
                self.enodes.len()
            );
            if !next_in_bounds {
                return;
            }
            curr = next;
            if curr == start {
                break;
            }
        }

        debug_assert_eq!(
            count, self.enodes[root as usize].class_size,
            "BUG: {context}: class_size mismatch for root {root}"
        );
    }

    /// Create a new EUF solver
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        EufSolver {
            terms,
            uf: UnionFind::new(terms.len()),
            assigns: HashMap::default(),
            trail: Vec::new(),
            scopes: Vec::new(),
            dirty: true,
            equality_edges: HashMap::default(),
            func_apps: Vec::new(),
            bool_arg_app_idx: Vec::new(),
            func_app_index: HashMap::default(),
            func_apps_init: false,
            has_theory_func_apps: true, // conservative until init_func_apps computes it
            bool_uf_arg_terms: HashSet::default(),
            pending_conflict: None,
            // Incremental E-graph (Phase 1)
            enodes: Vec::new(),
            enodes_init: false,
            bool_sorted: Vec::new(),
            bool_assigns_buf: Vec::new(),
            egraph_requeue_needed: true,
            bool_merge_pending: Vec::new(),
            bool_true_anchor: None,
            bool_false_anchor: None,
            cong_table: CongruenceTable::new(),
            to_merge: VecDeque::new(),
            undo_trail: Vec::new(),
            undo_scopes: Vec::new(),
            // Nelson-Oppen
            shared_equality_reasons: HashMap::default(),
            propagated_eqs: HashSet::default(),
            propagated_eq_pairs: HashSet::default(),
            pending_propagations: Vec::new(),
            // Function application value tracking (#385)
            func_app_values: HashMap::default(),
            model_term_scope: None,
            // Pre-indexed equality terms (#2673)
            eq_terms: Vec::new(),
            eq_terms_init: false,
            // #euf-atom-filter: unfiltered until a SAT-boundary-only executor
            // installs the SAT-atom set (see set_sat_atom_terms).
            sat_atom_eq_terms: None,
            class_eqs: HashMap::default(),
            pos_dirty_reps: HashSet::default(),
            pos_full_scan_needed: true,
            // Incremental scans are always on: the former `AY_EUF_INC_POS=0`
            // / `AY_EUF_INC_NEG=0` / `AY_EUF_INC_SYNC=0` /
            // `AY_EUF_EXPLAIN_NOSORT=0` legacy-full-rescan kill-switches are
            // removed (on was the default; the legacy paths remain reachable
            // only through the full-scan flags after pop/reset).
            inc_pos_enabled: true,
            diseq_pair_index: HashMap::default(),
            diseq_keys_by_rep: HashMap::default(),
            pending_neg_eqs: Vec::new(),
            neg_dirty_reps: HashSet::default(),
            neg_full_scan_needed: true,
            neg_full_scan_la_needed: true,
            pending_diseq_conflicts: Vec::new(),
            pending_diseq_match_keys: Vec::new(),
            const_terms_cache: Vec::new(),
            distinct_terms_cache: Vec::new(),
            bool_cong_candidates_cache: Vec::new(),
            term_cache_watermark: 0,
            inc_neg_enabled: true,
            cong_neg_enabled: cong_neg_depth_from_env() > 0,
            cong_neg_depth: cong_neg_depth_from_env(),
            cong_neg_propagation_count: 0,
            cong_neg_adaptive: cong_neg_adaptive_from_env(),
            cong_neg_ever_fired: false,
            cong_neg_suspended: false,
            cong_neg_barren: 0,
            cong_neg_probe_skip: 0,
            explain_nosort_enabled: true,
            // Local-branch features merged across the f189ce3e fork: explain
            // memoization (758e1bb2) + lazy N-O propagation reasons (d5eeecc9),
            // both default-on with their original env kill-switches.
            explain_memo: crate::explain::ExplainMemo::default(),
            explain_memo_enabled: std::env::var_os("AY_EUF_EXPLAIN_MEMO").is_none_or(|v| v != "0"),
            lazy_noprop_reasons: std::env::var_os("AY_EUF_LAZY_NOPROP").is_none_or(|v| v != "0"),
            // Pre-indexed ITE terms (#5575)
            ite_terms: Vec::new(),
            ite_terms_init: false,
            ite_by_cond: HashMap::default(),
            pending_ite: Vec::new(),
            ite_sweep_full_needed: true,
            // Reusable scratch buffers (#5575)
            scratch_diseqs: Vec::new(),
            scratch_distincts: Vec::new(),
            scratch_rep_to_const: HashMap::default(),
            scratch_bool_terms: Vec::new(),
            scratch_bool_uf_args: Vec::new(),
            scratch_rep_value: HashMap::default(),
            scratch_potential_props: Vec::new(),
            scratch_neg_props: Vec::new(),
            scratch_cong_neg_props: Vec::new(),
            scratch_cong_neg_memo: ay_core::kani_compat::DetHashMap::default(),
            scratch_class_eq_idxs: Vec::new(),
            scratch_seen_eq_idxs: ay_core::kani_compat::DetHashSet::default(),
            scratch_bool_arg_cong: ay_core::kani_compat::DetHashMap::default(),
            scratch_bool_arg_pool: Vec::new(),
            scratch_cong_neg_la: crate::types::CongNegScratch::default(),
            cong_neg_emitted: HashSet::default(),
            scratch_equalities: Vec::new(),
            scratch_shared_eq_keys: Vec::new(),
            // #6359: Use process-level cached env vars (OnceLock) to avoid
            // syscalls on every DPLL(T) iteration.
            debug_euf: euf_debug_flags().debug_euf,
            // Incremental EUF (#5575): worklist-based approach processes only
            // new merges per check(). Enabled by default (#6546) — the legacy
            // full-rebuild path is O(assigns) per check() which dominates
            // storeinv benchmarks (11x slower on size 9). Set AY_LEGACY_EUF=1
            // to force the old rebuild_closure path. Read directly from env
            debug_nelson_oppen: euf_debug_flags().debug_nelson_oppen,
            bool_arg_congruence: euf_debug_flags().bool_arg_congruence,
            bool_arg_validate: euf_debug_flags().bool_arg_validate,
            bool_arg_validate_transitive: euf_debug_flags().bool_arg_validate_transitive,
            last_bool_arg_forced_edges: Vec::new(),
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            // Disequality propagation (#8469)
            merge_epoch: 0,
            diseq_scan_epoch: 0,
            // shared_interface_terms removed — see shared_arith_terms
            // Shared disequalities from other theories (#8469)
            shared_disequalities: HashMap::default(),
            pending_shared_diseq_conflict: None,
            poisoned: false,
            // Nelson-Oppen disequality propagation (#8469)
            shared_arith_terms: Vec::new(),
            propagated_diseq_pairs: HashSet::default(),
            // Persistent propagation output buffer (#8599)
            propagation_output_buf: Vec::new(),
            // Fine-grained disequality dirty tracking (#8471)
            dirty_merge_reps: HashSet::default(),
            new_negated_eqs: Vec::new(),
            dt_merge_dirty: false,
            // Incremental UF-mirror sync (dirty-node tracking)
            uf_dirty_nodes: HashSet::default(),
            uf_full_sync_needed: true,
            inc_sync_enabled: true,
            inc_cong_undo_enabled: std::env::var_os("AY_EUF_INC_CONG_UNDO")
                .is_none_or(|v| v != "0"),
            undo_latched: false,
            rebuild_work: 0,
            undo_work: 0,
            cong_undo_min_func_apps: std::env::var("AY_EUF_CONG_UNDO_MIN")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
                .unwrap_or(CONG_UNDO_MIN_FUNC_APPS),
            inc_diseq_undo_enabled: std::env::var_os("AY_EUF_INC_DISEQ_UNDO")
                .is_none_or(|v| v != "0"),
            diseq_undo_min_func_apps: std::env::var("AY_EUF_DISEQ_UNDO_MIN")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
                .unwrap_or(DISEQ_UNDO_MIN_FUNC_APPS),
            neg_index_prebuilt: false,
            diseq_index_base_depth: 0,
            diseq_keys_dirty: false,
            // Verification-only mode (#8529 perf): default OFF. Only the two
            // verification constructors flip this on via verify_only().
            verify_only: false,
            func_app_scope: None,
            // #euf-prop-gap profiling (env-gated, off by default)
            gap_stats_enabled: std::env::var_os("AY_EUF_GAP_STATS").is_some(),
            gap_stats: PropGapStats::default(),
            // Lazy propagation justifications (#8467, #euf-lazy-explain):
            // OFF until the consumer opts in via
            // set_lazy_propagation_supported (only the eager SAT extension
            // does).
            lazy_explain_enabled: false,
            lazy_emit_counter: 0,
            lazy_neg_witness: HashMap::default(),
            lazy_emitted_count: 0,
            lazy_explained_count: 0,
            lazy_explain_rejected_count: 0,
        }
    }

    /// Enable or disable the EUF-side Bool-argument truth-value class merge for
    /// this solver instance, overriding the process-wide OFF default.
    /// Used by the standalone Bool-arg congruence unit tests, which
    /// assert Bool-arg congruence directly against the theory (the formula-level
    /// lemma injection that drives this in production is not in play there).
    /// (#bool-arg-congruence)
    pub fn set_bool_arg_congruence(&mut self, enabled: bool) {
        self.bool_arg_congruence = enabled;
    }

    /// Enable/disable the SOUND post-SAT Bool-arg congruence model-validation
    /// guard for this solver instance. `solve_euf` disables it in incremental
    /// mode (where it over-fires on dense models). (#bool-arg-congruence)
    pub fn set_bool_arg_validate(&mut self, enabled: bool) {
        self.bool_arg_validate = enabled;
    }

    /// Mark this solver as a verification-only instance and return it.
    ///
    /// Used exclusively by the soundness verifier (`verify_euf_conflict` /
    /// `verify_euf_propagation`), which constructs a fresh solver, asserts a
    /// set of literals, and reads ONLY the `check()` Sat/Unsat verdict —
    /// discarding every reason vector. In this mode the congruence merges that
    /// determine the verdict run unchanged, but the propagation-reason building
    /// (recursive `explain()` into `pending_propagations`) is skipped. See the
    /// `verify_only` field docs for the verdict-preservation argument.
    #[must_use]
    pub fn verify_only(mut self) -> Self {
        self.verify_only = true;
        self
    }

    /// Verification-only solver additionally SCOPED to the subterm closure of
    /// `roots` (#A2 PEQ perf). See the `func_app_scope` field docs for the
    /// verdict-preservation argument: congruence closure over the asserted
    /// literals' subterm-closed set decides their EUF (un)satisfiability, so
    /// function applications outside it are pure per-merge churn. Callers pass
    /// every term that will be asserted (conflict/reason literals + axioms).
    #[must_use]
    pub fn verify_only_scoped(mut self, roots: impl IntoIterator<Item = TermId>) -> Self {
        self.verify_only = true;
        let mut reachable: HashSet<u32> = HashSet::default();
        let mut stack: Vec<TermId> = roots.into_iter().collect();
        while let Some(term) = stack.pop() {
            if !reachable.insert(term.0) {
                continue;
            }
            for child in self.terms.children(term) {
                stack.push(child);
            }
        }
        self.func_app_scope = Some(reachable);
        self
    }

    /// No-op: EUF has no learned cuts to replay.
    /// Required by `solve_incremental_split_loop_pipeline!` macro.
    pub fn replay_learned_cuts(&mut self) {}

    /// Set the shared arithmetic interface terms for Nelson-Oppen disequality
    /// propagation (#8469). When set, `propagate_equalities()` will collect
    /// EUF-implied disequalities and return them in the result alongside
    /// equalities, eliminating the need for a separate
    /// `collect_implied_disequalities()` call.
    pub fn set_shared_arith_terms(&mut self, terms: Vec<TermId>) {
        self.shared_arith_terms = terms;
    }

    /// Deterministic digest of the EUF solver's ASSIGNMENT-DERIVED state
    /// (LAZY-M3-PERSISTENT-COMBINER-BLUEPRINT §3.2/§3.3(b) debug oracle).
    ///
    /// Folds the sizes of every Nelson-Oppen carry / current-assignment
    /// collection that `soft_reset` clears. After a `soft_reset`/`soft_reset_warm`
    /// this MUST equal the digest of a freshly-constructed solver (all zero),
    /// proving no assignment-derived merge/propagation leaked across the reset.
    /// Structural (persistable) state — the pristine post-init e-graph node set,
    /// congruence table — is intentionally EXCLUDED: it legitimately survives a
    /// warm reset and matches a fresh solver only after snapshot import.
    ///
    /// Uses a weighted additive fold so the digest is exactly `0` iff every
    /// component is empty — a fresh solver (and any correctly reset one) hashes
    /// to `0`, making the oracle's "equals fresh" check a simple `== 0`.
    ///
    /// Compiled in all builds (not `cfg`-gated): `soft_reset_warm`'s
    /// `debug_assert_eq!` type-checks its arguments even in release, so the
    /// method must be callable there. It is only *executed* in debug builds.
    pub fn assignment_derived_digest(&self) -> u64 {
        (self.assigns.len() as u64)
            .wrapping_mul(0x9E3779B1)
            .wrapping_add((self.trail.len() as u64).wrapping_mul(0x85EBCA77))
            .wrapping_add((self.shared_equality_reasons.len() as u64).wrapping_mul(0xC2B2AE3D))
            .wrapping_add((self.propagated_eqs.len() as u64).wrapping_mul(0x27D4EB2F))
            .wrapping_add((self.propagated_eq_pairs.len() as u64).wrapping_mul(0x165667B1))
            .wrapping_add((self.propagated_diseq_pairs.len() as u64).wrapping_mul(0xD3A2646D))
            .wrapping_add((self.pending_propagations.len() as u64).wrapping_mul(0xFD7046C5))
            .wrapping_add((self.shared_arith_terms.len() as u64).wrapping_mul(0xB55A4F09))
    }

    /// Restrict the next model extraction to terms reachable from `roots`.
    pub fn scope_model_to_roots(&mut self, roots: &[TermId]) {
        #[cfg(not(kani))]
        let mut reachable =
            ay_core::kani_compat::det_hash_set_with_capacity(roots.len().saturating_mul(4));
        #[cfg(kani)]
        let mut reachable = HashSet::default();
        let mut stack = roots.to_vec();
        while let Some(term) = stack.pop() {
            if !reachable.insert(term) {
                continue;
            }
            for child in self.terms.children(term) {
                stack.push(child);
            }
        }
        self.model_term_scope = Some(reachable);
    }

    /// Clear any temporary model extraction scope.
    pub fn clear_model_scope(&mut self) {
        self.model_term_scope = None;
    }

    pub(crate) fn scoped_model_terms(&self) -> Vec<TermId> {
        match &self.model_term_scope {
            Some(scope) => {
                let mut terms: Vec<TermId> = scope.iter().copied().collect();
                terms.sort_unstable();
                terms
            }
            None => self.terms.term_ids().collect(),
        }
    }

    /// Initialize the func_apps cache if not already done
    pub(crate) fn init_func_apps(&mut self) {
        if self.func_apps_init {
            return;
        }

        self.func_apps.clear();
        self.bool_arg_app_idx.clear();
        self.func_app_index.clear();
        self.bool_uf_arg_terms.clear();
        // Recompute whether any theory-sorted (Int/Real/BV) func app exists;
        // if not, `try_track_func_app_value` can never fire and is skipped.
        let mut any_theory_func_app = false;
        for term_id in self.terms.term_ids() {
            // #A2 PEQ perf: verification-scoped instances register only apps
            // inside the asserted literals' subterm closure (see
            // `func_app_scope` docs for the verdict-preservation argument).
            if let Some(scope) = &self.func_app_scope {
                if !scope.contains(&term_id.0) {
                    continue;
                }
            }
            if let TermData::App(sym, args) = self.terms.get(term_id) {
                if !Self::is_builtin_symbol(sym) && !args.is_empty() {
                    // Seq is included (#uf-app-value-seq): a Seq-returning UF
                    // app gets no atomic model element, so without a tracked
                    // `(= (f x) t)` value the evaluator cannot resolve it at
                    // all. Keeping the QF_UF fast-out intact (pure-UF problems
                    // still have no such apps).
                    if matches!(
                        self.terms.sort(term_id),
                        Sort::Int | Sort::Real | Sort::BitVec(_) | Sort::Seq(_)
                    ) {
                        any_theory_func_app = true;
                    }
                    // Pre-compute hash of (symbol, sort)
                    use std::hash::{Hash, Hasher};
                    let mut hasher = std::collections::hash_map::DefaultHasher::new();
                    sym.hash(&mut hasher);
                    self.terms.sort(term_id).hash(&mut hasher);
                    let func_hash = hasher.finish();

                    // Store index for O(1) lookup
                    self.func_app_index.insert(term_id.0, self.func_apps.len());
                    // #bool-arg-congruence: record Bool-sorted arguments so the
                    // true/false class merge covers them even when the arg is a
                    // builtin/connective Bool term the SAT layer normally owns.
                    let mut has_bool_arg = false;
                    for &arg in args {
                        if self.terms.sort(arg) == &Sort::Bool {
                            self.bool_uf_arg_terms.insert(arg.0);
                            has_bool_arg = true;
                        }
                    }
                    // #euf-guard-index: the guard's per-check scan visits only these.
                    if has_bool_arg {
                        self.bool_arg_app_idx.push(self.func_apps.len() as u32);
                    }
                    self.func_apps.push(FuncAppMeta {
                        term_id: term_id.0,
                        func_hash,
                        args: args.iter().map(|t| t.0).collect(),
                    });
                }
            }
        }
        self.has_theory_func_apps = any_theory_func_app;
        self.func_apps_init = true;
    }

    /// Pre-compute ITE term indices (non-Bool only) for fast iteration (#5575).
    /// Avoids scanning all terms in rebuild_closure/incremental_rebuild when
    /// there are no ITE terms (common in QF_UF, QF_EUF).
    pub(crate) fn init_ite_terms(&mut self) {
        if self.ite_terms_init {
            return;
        }
        self.ite_terms.clear();
        self.ite_by_cond.clear();
        for term_id in self.terms.term_ids() {
            if matches!(self.terms.get(term_id), TermData::Ite(..))
                && !matches!(self.terms.sort(term_id), Sort::Bool)
            {
                self.ite_terms.push(term_id.0);
                // Index by the term the sweep actually consults: the condition,
                // and — because the sweep reads `Not(inner)` conditions through
                // `inner`'s assignment — the inner term as well.
                if let TermData::Ite(cond, _, _) = self.terms.get(term_id) {
                    let cond = *cond;
                    self.ite_by_cond.entry(cond.0).or_default().push(term_id.0);
                    if let TermData::Not(inner) = self.terms.get(cond) {
                        let inner = *inner;
                        self.ite_by_cond.entry(inner.0).or_default().push(term_id.0);
                    }
                }
            }
        }
        self.ite_terms_init = true;
        // A freshly built index has seen no assignments yet.
        self.ite_sweep_full_needed = true;
    }

    pub(crate) fn queue_pending_propagation(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: Vec<TheoryLit>,
        context: &'static str,
    ) {
        if lhs == rhs {
            if self.debug_euf || self.debug_nelson_oppen {
                safe_eprintln!(
                    "[EUF] Skipping trivial N-O propagation ({context}): {} = {}",
                    lhs.0,
                    rhs.0
                );
            }
            return;
        }

        self.pending_propagations.push((lhs, rhs, reason));
    }

    /// Seed Nelson-Oppen equality propagation deduplication for a replayed pair.
    ///
    /// Fresh combined-theory instances can import already-propagated equalities
    /// from the previous instance. Seeding this set prevents congruence closure
    /// from reporting the same pair as new work again.
    pub fn seed_propagated_equality_pair(&mut self, lhs: TermId, rhs: TermId) {
        if lhs == rhs {
            return;
        }
        let pair = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
        self.propagated_eq_pairs.insert(pair);
        if let Some(eq_term) = self.terms.find_eq(lhs, rhs) {
            self.propagated_eqs.insert(eq_term);
        }
    }

    /// Current number of terms managed by the solver.
    #[must_use]
    pub fn num_terms(&self) -> usize {
        self.uf.parent.len()
    }

    /// Take-and-clear the DT merge-dirty flag (`DESIGN_lazy_dt.md` stage D1).
    ///
    /// Returns `true` when at least one real e-class merge happened since the
    /// previous call. The lazy datatype propagation pass uses this as its
    /// change-feed gate so it never re-scans an unchanged e-graph.
    pub fn take_dt_merge_dirty(&mut self) -> bool {
        std::mem::take(&mut self.dt_merge_dirty)
    }

    /// Peek the DT merge-dirty flag without clearing it (stage D2).
    ///
    /// Lets the search-time D0 clash/cycle check share one change feed with
    /// the D1 propagation pass (which consumes the flag right after).
    #[must_use]
    pub fn dt_merge_dirty(&self) -> bool {
        self.dt_merge_dirty
    }
}
