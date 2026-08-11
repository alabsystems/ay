// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Type definitions for the eager DPLL(T) theory extension.
//!
//! Contains the `TheoryExtension` struct, helper types, and the debug
//! formatting utility. Extracted from `mod.rs` (#5970 code-health splits).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    BoundRefinementRequest, FarkasAnnotation, TermData, TermId, TermStore, TheorySolver,
};
use ay_sat::Literal;
use std::cell::{Cell, RefCell};

/// Sentinel for "no node" in the skip-assigned free-list (`u32::MAX`). No seed
/// position can equal this because [`build_unassigned_freelist_state`] enforces
/// that `seed_index.len()` leaves this value reserved.
pub(super) const UNASSIGNED_NIL: u32 = u32::MAX;

/// Read the `AY_LRA_UNASSIGNED_SKIP` flag once per process (default ON).
///
/// Default-ON with opt-out (`AY_LRA_UNASSIGNED_SKIP=0`), matching the
/// `AY_LRA_INC_ENGINE` convention. When on, `suggest_decision` scans only the
/// unassigned theory atoms via the order-preserving free-list (selecting the
/// same literal as the full scan, just skipping assigned atoms); when off it
/// takes the byte-identical full-scan path. Measured z3-mode @90s 2-sample:
/// +19 on the QF_LRA hybrid_networks .ind pool, 0 soundness mismatches
/// (suggest_decision returns decision HINTS only — soundness is enforced
/// downstream regardless — and no reproducible per-file regression was found).
pub(super) fn unassigned_skip_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("AY_LRA_UNASSIGNED_SKIP")
            .map(|v| v != "0")
            .unwrap_or(true)
    })
}

/// Build the initial skip-assigned free-list backing storage.
///
/// Returns `(sat_var_to_seed_pos, prev, next, linked)`. When `enabled` is
/// false every vector is empty (zero allocation on the disabled path). When
/// enabled, `sat_var_to_seed_pos` is sized to `num_var_slots` and maps each
/// SAT variable id to its seed position (`UNASSIGNED_NIL` for non-seed vars);
/// `prev`/`next`/`linked` are sized to `seed_index.len()` and are populated on
/// the first rebuild (the extension starts `unassigned_dirty = true`).
pub(super) fn build_unassigned_freelist_state(
    enabled: bool,
    seed_index: &[(u32, TermId)],
    num_var_slots: usize,
) -> (Vec<u32>, Vec<u32>, Vec<u32>, Vec<bool>) {
    if !enabled {
        return (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    }
    let n = seed_index.len();
    assert!(
        n <= UNASSIGNED_NIL as usize,
        "skip-assigned free-list exhausted its u32 seed-position space"
    );
    let mut sat_var_to_seed_pos = vec![UNASSIGNED_NIL; num_var_slots];
    for (pos, &(sat_var, _atom)) in seed_index.iter().enumerate() {
        let vi = sat_var as usize;
        if vi < sat_var_to_seed_pos.len() {
            sat_var_to_seed_pos[vi] = pos as u32;
        }
    }
    (
        sat_var_to_seed_pos,
        vec![UNASSIGNED_NIL; n],
        vec![UNASSIGNED_NIL; n],
        vec![false; n],
    )
}

use crate::diagnostic_trace::DpllDiagnosticWriter;
use crate::executor::BoundRefinementReplayKey;
use crate::proof_tracker::ProofTracker;
use crate::DpllEagerStats;

use super::NativeTheoryPropagationDispatch;

/// Recursively format a term for debugging (up to `depth` levels).
pub(super) fn format_term_recursive(terms: &TermStore, term: TermId, depth: u32) -> String {
    if depth == 0 {
        return format!("#{}", term.0);
    }
    match terms.get(term) {
        TermData::Const(c) => format!("{c:?}"),
        TermData::Var(name, _sort) => format!("{}#{}", name, term.0),
        TermData::App(sym, args) => {
            let arg_strs: Vec<String> = args
                .iter()
                .map(|&a| format_term_recursive(terms, a, depth - 1))
                .collect();
            format!("({} {})", sym.name(), arg_strs.join(" "))
        }
        TermData::Not(inner) => {
            format!("(not {})", format_term_recursive(terms, *inner, depth - 1))
        }
        other => format!("#{}:{:?}", term.0, other),
    }
}

/// Stable key for deduplicating binary bound-ordering axioms across
/// incremental eager-extension iterations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TheoryAxiomKey {
    first: (TermId, bool),
    second: (TermId, bool),
}

impl TheoryAxiomKey {
    pub(crate) fn new(t1: TermId, p1: bool, t2: TermId, p2: bool) -> Self {
        let first = (t1, p1);
        let second = (t2, p2);
        if second < first {
            Self {
                first: second,
                second: first,
            }
        } else {
            Self { first, second }
        }
    }
}

/// Cached precomputed data for `TheoryExtension` that is expensive to rebuild.
///
/// On large QF_LRA formulas (e.g., labyrinth-18 at 64MB), the
/// `TheoryExtension` constructor spends O(|terms|) scanning all terms for ITE
/// nodes and O(|vars|) building the theory_var_bitset. For persistent
/// split-loop arms that rebuild TheoryExtension every iteration, caching this
/// data eliminates the dominant per-iteration overhead (#8256).
///
/// The cache is invalidated (grown incrementally) when new split atoms add
/// new SAT variables to `var_to_term`.
pub(crate) struct CachedExtensionData {
    /// Dense bitset for O(1) theory-variable membership checks.
    pub(crate) theory_var_bitset: Vec<u64>,
    /// ITE relevancy guards indexed by SAT variable ID.
    pub(crate) ite_branch_guards: Vec<(u32, bool)>,
    /// Dense bitset for O(1) ITE-guard membership.
    pub(crate) ite_guarded_bitset: Vec<u64>,
    /// Dense bitset for O(1) ITE condition variable membership (#8003).
    pub(crate) ite_condition_bitset: Vec<u64>,
    /// #8003: Maps ITE condition SAT variable IDs to their condition TermIds.
    /// For non-theory-atom ITE conditions (e.g., `(xor x_72 x_73)` used as
    /// `(ite (xor ...) 1 0)` in arithmetic), `var_to_term` has no entry because
    /// only theory atoms are registered there. This map provides the TermId so
    /// the propagation path can forward the condition's truth value to the
    /// theory solver via `assert_literal`. Without this, LRA's
    /// `parse_linear_expr` cannot resolve ITE conditions and the atoms are
    /// permanently marked "unsupported", causing spurious Unknown results.
    pub(crate) ite_condition_var_to_term: HashMap<u32, TermId>,
    /// Number of SAT variables when this cache was last fully rebuilt.
    /// Used to detect when incremental extension is needed vs full rebuild.
    pub(crate) last_full_rebuild_num_vars: usize,
    /// Number of theory atoms that were registered with the theory solver
    /// in the previous iteration. Used to skip redundant `register_atom()`
    /// calls for atoms that are already registered (#8256).
    pub(crate) prev_registered_atom_count: usize,
    /// Cached value of `AY_DISABLE_THEORY_CHECK` env var to avoid repeated
    /// syscalls on every split-loop iteration (#8256).
    pub(crate) disable_theory_check: bool,
}

impl CachedExtensionData {
    /// Extend the cached bitsets and ITE guards to cover new SAT variables
    /// added by split encoding since the last build.
    ///
    /// Only the theory_var_bitset needs incremental extension for new
    /// variables. ITE branch guards are built from the TermStore's ITE nodes,
    /// which don't change between split iterations -- new split atoms are
    /// arithmetic comparisons, not ITEs.
    ///
    /// #8256: Fast-path -- when var count hasn't changed since the last build,
    /// skip the entire O(n) scan. This eliminates the dominant per-iteration
    /// overhead on large QF_LRA formulas where most iterations don't add
    /// new split atoms.
    pub(crate) fn extend_for_new_vars(
        &mut self,
        var_to_term: &HashMap<u32, TermId>,
        theory_atom_set: &HashSet<TermId>,
    ) {
        let current_var_count = var_to_term.len();

        // Fast path: no new variables since last build -- nothing to extend.
        if current_var_count == self.last_full_rebuild_num_vars {
            return;
        }

        let max_var_id = var_to_term.keys().copied().max().unwrap_or(0) as usize;
        let needed_words = (max_var_id + 64) / 64;

        // Extend theory_var_bitset
        if needed_words > self.theory_var_bitset.len() {
            self.theory_var_bitset.resize(needed_words, 0);
        }
        // Only scan new variables (those with var_id >= last_full_rebuild_num_vars).
        // Existing variables were already set during the initial build or prior
        // extensions. New split atoms are added with ascending var IDs, so we
        // only need to check entries that weren't present before.
        for (&var_id, &term_id) in var_to_term {
            if (var_id as usize) >= self.last_full_rebuild_num_vars
                && theory_atom_set.contains(&term_id)
            {
                let idx = var_id as usize;
                if idx / 64 < self.theory_var_bitset.len() {
                    self.theory_var_bitset[idx / 64] |= 1u64 << (idx % 64);
                }
            }
        }

        // Extend ITE guard arrays (new split atoms are not ITEs, just pad)
        if max_var_id + 1 > self.ite_branch_guards.len() {
            self.ite_branch_guards.resize(max_var_id + 1, (0, false));
        }
        if needed_words > self.ite_guarded_bitset.len() {
            self.ite_guarded_bitset.resize(needed_words, 0);
        }
        if needed_words > self.ite_condition_bitset.len() {
            self.ite_condition_bitset.resize(needed_words, 0);
        }

        self.last_full_rebuild_num_vars = current_var_count;
    }
}

pub(super) enum BoundRefinementHandoff<'a> {
    FinalCheckOnly,
    StopAndReplayInline {
        known_replays: &'a HashSet<BoundRefinementReplayKey>,
    },
}

/// Wrapper that adapts a TheorySolver to the Extension trait for eager DPLL(T)
pub(crate) struct TheoryExtension<'a, T: TheorySolver> {
    /// The theory solver
    pub(super) theory: &'a mut T,
    /// Term store (optional) for semantic verification.
    pub(super) terms: Option<&'a TermStore>,
    /// Mapping from SAT variables to term IDs
    pub(super) var_to_term: &'a HashMap<u32, TermId>,
    /// Mapping from term IDs to SAT variables
    pub(super) term_to_var: &'a HashMap<TermId, u32>,
    /// Theory atoms (terms the theory cares about, stable order + unique)
    pub(super) theory_atoms: &'a [TermId],
    /// Membership set for O(1) theory-atom checks.
    pub(super) theory_atom_set: &'a HashSet<TermId>,
    /// Last trail position we processed
    pub(super) last_trail_pos: usize,
    /// Current theory push level (incremented on each push)
    pub(super) theory_level: u32,
    /// Debug mode
    pub(super) debug: bool,
    /// Optional DPLL(T) diagnostic writer for eager interaction events.
    pub(super) diagnostic_trace: Option<&'a DpllDiagnosticWriter>,
    pub(super) proof: Option<ProofContext<'a>>,
    /// Count of theory conflicts encountered during eager solving (#4705).
    pub(super) theory_conflict_count: u64,
    /// Count of theory propagation clauses added during eager solving (#4705).
    pub(super) theory_propagation_count: u64,
    /// Count of partial clause events where `term_to_literal` dropped terms (#5000).
    pub(super) partial_clause_count: u64,
    /// Mid-search minted term -> SAT variable mappings (#6846).
    ///
    /// `term_to_var` is an immutable borrow of the encoding built before the
    /// solve, so a theory conflict naming a term that was never encoded used to
    /// map to a PARTIAL clause and fail closed to `Unknown` — the documented
    /// reason AUFLIA is pinned to the lazy pipeline. This overlay lets the
    /// extension name such a term with a fresh variable beyond the solver's
    /// current `num_vars()`; `add_theory_lemma` already grows the solver for
    /// out-of-range literals. Consulted by `var_for_term` after `term_to_var`,
    /// and it must OUTLIVE the individual check, so the mapping stays stable for
    /// later rounds (a term must never be renamed to a second variable).
    pub(super) minted_term_to_var: HashMap<TermId, u32>,
    /// Reverse of `minted_term_to_var`, for model/diagnostic lookups.
    pub(super) minted_var_to_term: HashMap<u32, TermId>,
    /// Count of variables minted mid-search (#6846), for `--stats` attribution.
    pub(super) minted_var_count: u64,
    /// Pending split/lemma request from the theory solver (#4919).
    /// Stored here instead of panicking so that eager mode can be used with
    /// theories that produce splits at full-model time (LRA, LIA, strings).
    /// The executor retrieves this via `take_pending_split()`.
    pub(super) pending_split: Option<ay_core::TheoryResult>,
    /// Pending bound-refinement requests discovered during final theory check.
    pub(super) pending_bound_refinements: Vec<BoundRefinementRequest>,
    /// Trail positions saved at each push level (#5548).
    /// On backtrack, `last_trail_pos` is restored from this stack instead of
    /// being reset to 0, avoiding O(trail × backtracks) redundant re-assertions.
    pub(super) level_trail_positions: Vec<usize>,
    /// Whether theory.check() has been called at least once (#4919).
    /// The first call must always run to detect initial-state conflicts.
    pub(super) has_checked: bool,
    /// Index into `theory_atoms` for theory-aware branching (#4919).
    /// On each `suggest_decision` call, scan from this index for the first
    /// unassigned theory atom. This ensures theory atoms are decided before
    /// Tseitin encoding variables, matching Z3's `theory_aware_branching`.
    /// Reference: Z3 smt_case_split_queue.cpp:1170-1209.
    pub(super) theory_decision_idx: Cell<usize>,
    /// #skip-assigned (`AY_LRA_UNASSIGNED_SKIP`, default ON): when true,
    /// `suggest_decision` selects theory atoms by walking an intrusive
    /// order-preserving free-list of the CURRENTLY-UNASSIGNED seed positions
    /// instead of re-scanning every seed atom (assigned or not) each decision.
    /// Read once at construction; when false, all the free-list fields below
    /// are empty and untouched and the byte-identical full-scan path runs.
    pub(super) unassigned_skip: bool,
    /// Reverse index `sat_var id -> seed position` (`UNASSIGNED_NIL` for SAT
    /// variables that are not theory-atom seeds). Sized to the max SAT var id
    /// seen at construction. Empty unless `unassigned_skip` is on. Used by the
    /// incremental trail scan to unlink a position in O(1) when its variable
    /// becomes assigned.
    pub(super) sat_var_to_seed_pos: Vec<u32>,
    /// Intrusive doubly-linked free-list over SEED POSITIONS: `prev`/`next`
    /// pointers (indexed by seed position, `UNASSIGNED_NIL` = end). Together
    /// with `unassigned_head` these thread the unassigned seed positions in
    /// ascending seed order, so the head->tail walk visits exactly the same
    /// atoms in the same order the full scan would — only skipping assigned
    /// ones. Empty unless `unassigned_skip` is on.
    pub(super) unassigned_prev: RefCell<Vec<u32>>,
    pub(super) unassigned_next: RefCell<Vec<u32>>,
    /// Per-position membership flag, guarding the incremental unlink against a
    /// double-unlink (idempotent). `linked[pos]` is true iff `pos` is currently
    /// threaded into the free-list. Empty unless `unassigned_skip` is on.
    pub(super) unassigned_linked: RefCell<Vec<bool>>,
    /// Head of the free-list (smallest-seed-position unassigned atom), or
    /// `UNASSIGNED_NIL` when empty.
    pub(super) unassigned_head: Cell<u32>,
    /// When true, the free-list is stale and must be rebuilt from `ctx.value()`
    /// (the source of truth) on the next `suggest_decision`. Set by
    /// `backtrack()` and `init()` — every path that unassigns a theory var
    /// routes through one of those — so the list is never walked stale.
    pub(super) unassigned_dirty: Cell<bool>,
    /// Trail position up to which the incremental unlink scan has consumed.
    /// Between rebuilds the trail only grows, so scanning `trail[scan_pos..]`
    /// and unlinking each newly-assigned seed position keeps the free-list in
    /// sync. Reset to `trail.len()` on each rebuild.
    pub(super) unassigned_scan_pos: Cell<usize>,
    /// Bound ordering axiom clauses to inject on the first propagate() call.
    /// Generated from Z3's mk_bound_axioms algorithm: for each pair of
    /// nearest-neighbor bounds on the same variable, add a binary SAT clause
    /// encoding their implication. This moves bound propagation from the theory
    /// solver (O(n) round-trips) to BCP (O(1) unit propagation). (#4919)
    pub(super) pending_axiom_clauses: Vec<Vec<Literal>>,
    /// Term-level representations of pending bound axioms for proof tracking (#6178).
    /// Each entry is `(term1, polarity1, term2, polarity2)` corresponding to
    /// the SAT-level clause in `pending_axiom_clauses` at the same index.
    /// When proof tracking is enabled, these are recorded as `TheoryLemma` steps
    /// before the SAT-level clauses are injected.
    pub(super) pending_axiom_terms: Vec<(TermId, bool, TermId, bool)>,
    /// Farkas certificates for pending bound axioms (#6686).
    pub(super) pending_axiom_farkas: Vec<Option<FarkasAnnotation>>,
    /// Count of times the current expression split has been seen in
    /// propagate() calls within this SAT solve (#4919). Used to detect
    /// oscillation: first occurrence continues search, subsequent ones
    /// trigger the stop signal to hand control to the split loop.
    pub(super) expr_split_seen_count: u32,
    /// Opt-in incremental eager handoff for inline bound-refinement replay.
    pub(super) bound_refinement_handoff: BoundRefinementHandoff<'a>,
    /// #4919 Approach D/G: count of consecutive check() calls that produced
    /// 0 theory propagations. When this exceeds a threshold, the extension
    /// defers subsequent check() calls until more theory atoms accumulate,
    /// batching atoms to help the bound analyzer cross the derivation
    /// threshold (where rows have enough bounded variables for all-but-one
    /// analysis to succeed).
    pub(super) zero_propagation_streak: u32,
    /// #4919: accumulated theory atoms since the last check(). When deferring
    /// checks due to zero-propagation streak, this tracks how many atoms are
    /// waiting to be processed in a batch.
    pub(super) deferred_atom_count: u32,
    /// Deterministic eager-extension counters for batching diagnostics (#6503).
    pub(super) eager_stats: DpllEagerStats,
    /// Expression-split disequality terms that the split-loop pipeline has
    /// already encoded as split clauses in the persistent SAT solver (#6662).
    /// When the theory re-fires NeedExpressionSplit for one of these terms,
    /// the extension suppresses it (treats it as Sat) instead of storing it
    /// in `pending_split` and triggering the stop signal.
    pub(super) processed_expr_splits: Option<&'a HashSet<TermId>>,
    /// Dense bitset indexed by SAT variable ID for O(1) theory-atom membership.
    /// Replaces the double hashmap lookup (var_to_term + theory_atom_set.contains)
    /// in the hot trail-scan loop of propagate_impl(). Built at construction time.
    pub(super) theory_var_bitset: Vec<u64>,
    /// Dense, precomputed `(sat_var, atom)` index for bulk phase seeding.
    ///
    /// `seed_theory_phases` re-seeds phase hints after EVERY BCP/theory-prop
    /// quiescence (many times per round). The previous seeding loop did a
    /// `term_to_var.get(atom)` HashMap lookup for every theory atom on every
    /// seed, twice (once for `phase[]`, once for `target_phase[]`) — the
    /// dominant in-solver cost on LRA/induction benchmarks per profiling. This
    /// pairs each theory atom with its SAT variable id ONCE at construction so
    /// each seed is a flat slice walk with no per-atom hashing. Atoms with no
    /// SAT var are dropped (they contributed nothing to seeding before either).
    /// Built fresh per construction (cheap O(atoms)); not cached.
    pub(super) seed_index: Vec<(u32, TermId)>,
    /// Last theory phase-hint epoch this extension seeded at, if the theory
    /// reports one (`TheorySolver::phase_hint_epoch`). When unchanged since the
    /// last seed, the suggestions are identical and the O(atoms) re-seed is
    /// skipped entirely — eliminating the dominant in-solver self-time leaf on
    /// QF_LRA induction benchmarks. `None` = not yet seeded, or theory has no
    /// epoch (seed unconditionally). `Cell` because `seed_phase_hints_dual`
    /// takes `&self`.
    pub(super) last_seed_epoch: Cell<Option<u64>>,
    /// Sticky wander latch (#euf-search-quality): set once the search is
    /// detected "wandering" (decisions >> conflicts) for a theory that opts
    /// into `TheorySolver::wander_hand_to_vsids`. While latched, the extension
    /// stops steering the SAT search entirely — `suggest_decision` returns
    /// `None`, bulk phase seeding is skipped, and `suggest_phase` only
    /// forwards theory-IMPLIED polarities (`suggest_phase_implied`). VSIDS +
    /// phase saving own the search for the rest of the solve. Heuristic-only:
    /// changes search order, never verdicts. `Cell` because the deciding
    /// callbacks take `&self`.
    pub(super) wander_latched: Cell<bool>,
    /// One-shot flag set together with `wander_latched`: the next seed call
    /// CLEARS the saved/target phase entries of all theory atoms (back to the
    /// solver default) instead of seeding them. The pre-latch steering wrote
    /// `suggest_phase` polarities into the phase arrays; leaving that residue
    /// in place measurably poisons the post-latch VSIDS search (hwbench
    /// rushhour.2: 11.5s with residue vs 5.5s without). Clearing once puts the
    /// latched search in the same phase state as a never-steered solve.
    pub(super) wander_phase_clear_pending: Cell<bool>,
    /// ITE relevancy guards (#8125): maps SAT variable ID of a theory atom to
    /// `(condition_sat_var_id, is_then_branch)`. When the condition variable is
    /// assigned and selects the OTHER branch, the theory atom is in the inactive
    /// ITE branch and can be deferred from BCP-time theory checks.
    ///
    /// Built at construction time by scanning the TermStore for
    /// `TermData::Ite(cond, then_t, else_t)` where branches are theory atoms.
    /// Only populated when `terms` is Some.
    pub(super) ite_branch_guards: Vec<(u32, bool)>,
    /// Dense bitset indexed by SAT variable ID for O(1) ITE-guard membership.
    /// Bit is set if the variable has an entry in `ite_branch_guards`.
    pub(super) ite_guarded_bitset: Vec<u64>,
    /// Dense bitset for O(1) ITE condition variable membership (#8003).
    pub(super) ite_condition_bitset: Vec<u64>,
    /// #8003: Maps ITE condition SAT variable IDs to their condition TermIds
    /// for non-theory-atom conditions. See `CachedExtensionData` doc for details.
    pub(super) ite_condition_var_to_term: HashMap<u32, TermId>,
    /// Theory atoms deferred by the ITE relevancy filter during BCP.
    /// Flushed to the theory before final check in `check_impl()`.
    /// Each entry is `(term_id, value, sat_assignment_level, flushed)`.
    ///
    /// #uflia-deferred-atom-loss: the level field records the SAT decision
    /// level of the deferred assignment so `backtrack(new_level)` can RETAIN
    /// entries whose assignment survives the backjump (level <= new_level).
    /// The former wholesale `clear()` permanently lost such atoms: SAT keeps
    /// the assignment (so `propagate()` never re-forwards it) while the
    /// theory never received it — the combined final check then accepted
    /// models violating the invisible atom (mathsat EufLaArithmetic hard*
    /// live-branch disequalities), which only the strict ite_uf_definition
    /// model gate caught, degrading provable UNSAT to unknown.
    ///
    /// The `flushed` flag dedups re-asserts: an entry is asserted at most
    /// once per backtrack epoch (backtrack resets the flag on survivors, as
    /// the theory scope holding the assert may have been popped).
    pub(super) ite_deferred_atoms: Vec<(TermId, bool, u32, bool)>,
    /// Trail position up to which `can_propagate()` has scanned without finding
    /// theory atoms. Avoids re-scanning the same boolean-only trail entries on
    /// repeated calls. Reset on backtrack. Uses `Cell` for interior mutability
    /// since `can_propagate()` takes `&self`.
    pub(super) can_propagate_scan_pos: Cell<usize>,
    /// #4535 memoized verifier, eager-path wiring (#uflia-verify-memo):
    /// Executor-owned memo of fail-closed semantic conflict-verification
    /// verdicts, keyed by the sorted conflict literal set. The SAT solver
    /// re-derives IDENTICAL theory conflicts after learned-clause deletion
    /// and across split-loop iterations; each re-derivation re-paid the full
    /// fresh-combiner re-solve. The verdict is a pure function of the literal
    /// set + term content (append-only in-session) + support-axiom set; the
    /// Executor clears the memo at `check_sat_internal` entry and on every
    /// support-set rebuild, so no verdict outlives its inputs.
    ///
    /// TRUST-TRUE-ONLY policy: a memoized `true` skips the re-solve (the set
    /// was already proven jointly UNSAT under identical inputs). A memoized
    /// `false` is IGNORED here and the full verification re-runs, so the
    /// exact `VerificationError` kind (e.g. `ConflictIsSat`, which the
    /// check-path array-context carve-out pattern-matches) is preserved
    /// byte-identically on every failure path.
    pub(super) verify_memo: Option<&'a mut crate::verification::ConflictSemanticVerifyMemo>,
    /// Cached `AY_DISABLE_THEORY_CHECK` env var (read once at construction).
    pub(super) disable_theory_check: bool,
    /// #8008: Total BCP theory checks performed (independent of propagation
    /// streak). Used to detect when eager theory checking is unproductive and
    /// switch to deferred mode.
    pub(super) total_bcp_checks: u64,
    /// #8008: Total BCP theory conflicts detected. Together with
    /// `total_bcp_checks`, this gives the conflict yield ratio which controls
    /// the transition to deferred mode.
    pub(super) total_bcp_conflicts: u64,
    /// #8013: Total BCP theory propagations generated. Used alongside
    /// `total_bcp_conflicts` to gate full deferral: if the theory is producing
    /// propagations (even without conflicts), deferral skips the propagations
    /// that guide SAT search, causing search thrashing on QF_LRA formulas.
    pub(super) total_bcp_propagations: u64,
    /// #8255: Count of BCP theory checks that produced at least one propagation.
    pub(super) total_bcp_productive_prop_calls: u64,
    /// #8008: When true, BCP-time theory checks are skipped entirely.
    /// Theory consistency is checked only at complete assignment via
    /// `check_impl()`. This mimics Z3's `final_check_eh()`-only approach
    /// and is activated when the conflict yield ratio (conflicts/checks)
    /// falls below a threshold after enough total checks.
    #[allow(dead_code)]
    pub(super) deferred_theory_mode: bool,
    /// #8256: Cumulative count of BCP theory conflicts with clause length <= 3.
    /// Tiny conflicts (2-3 literal contradictory_variable_bounds) are correct
    /// but often useless for guiding search on SAT-satisfiable formulas with
    /// many ITE branches (simple_startup, sc-*, uart-*). Z3 doesn't run
    /// simplex during BCP at all, so it never generates these. The ratio
    /// `consecutive_tiny_conflicts / total_bcp_conflicts` is a diagnostic
    /// metric for identifying BCP overhead on ITE-heavy formulas.
    /// Note: field name kept for backward compat (was once consecutive).
    pub(super) consecutive_tiny_conflicts: u64,
    /// #8008: When true, propagate_impl() skips ALL work (push, trail, assert)
    /// and returns immediately. Atoms are bulk-replayed in check_impl() via
    /// flush_deferred_trail(). This eliminates O(trail) per-call overhead
    /// for theory-heavy formulas.
    pub(super) full_trail_deferral_active: bool,
    /// #8008: Counter for fractional theory-aware branching.
    pub(super) theory_decision_call_count: Cell<u64>,
    /// #8260: BCP atom batching counter for can_propagate() threshold.
    pub(super) pending_theory_atoms_for_batch: Cell<u32>,
    /// #8255: Count of theory atoms asserted since last check_during_propagate()
    /// call. Unlike zero_propagation_streak (which never triggers when the theory
    /// is productive), this tracks atoms-since-check and gates the check phase
    /// independently of propagation productivity. Reset on check, backtrack, init.
    pub(super) atoms_since_last_check: u32,
    /// #8254: Count of level-0 BCP conflicts rejected by the full-state
    /// soundness guard. Tracks how often the guard fires to prevent false UNSAT.
    pub(super) full_state_guard_rejections: u64,
    /// #8254: Total level-0 full-state soundness checks performed. Budget-capped
    /// per solve to limit O(atoms) cost in CHC sub-queries.
    pub(super) full_state_guard_checks: u64,
    /// #8177: JIT-compiled theory atom dispatch table for O(1) array-indexed
    /// theory atom lookups in the propagation hot loop. Replaces the multi-step
    /// `is_theory_atom()` + `var_to_term.get()` + ITE bitset check sequence
    /// with a single array access via `dispatch_assignment()`.
    ///
    /// Built at construction time from `var_to_term`, `theory_atom_set`, and
    /// ITE guard data. Only available when the `jit` feature is enabled.
    #[cfg(feature = "jit")]
    pub(super) jit_dispatch_table: Option<ay_jit::TheoryDispatchTable>,
    /// Fail-closed DPLL eligibility decision for native theory-bound propagation.
    #[allow(dead_code)]
    pub(super) native_theory_propagation_dispatch: NativeTheoryPropagationDispatch,
    /// Monotonic counter for sampling-based verification on large formulas (#8558).
    pub(super) semantic_verify_sample_counter: u64,
    /// Whether the large-formula sampling warning has been emitted (#8558).
    #[allow(dead_code)]
    pub(super) semantic_verify_warned: bool,
    /// Cached sampling interval for semantic verification (#8256).
    /// 0 = not yet computed, 1 = verify every propagation, >1 = sample every N.
    pub(super) semantic_verify_interval: u32,
    /// Reusable verify-only EUF solver for semantic propagation verification
    /// (#qfuflia-a2-verifier-reuse; converged with the local task #13
    /// solver-reuse — both sides independently implemented push/assert/check/
    /// pop verifier reuse; this version is kept as the superset, adding the
    /// mixed-domain cache below). Constructing a fresh
    /// `EufSolver::new(terms).verify_only()` per verified propagation scans
    /// the whole term store each time — 85% of solve time on the SMT-COMP
    /// QF_UFLIA `xs` family. The cached solver is built once and reused via
    /// push/assert/check/pop; pop fully restores the incremental e-graph
    /// (stress-tested by the ay-euf differential suite). Lazily initialized on
    /// first EUF verification.
    pub(super) verify_euf_cache: Option<ay_euf::EufSolver<'a>>,
    /// Reusable combined verifier for MIXED-domain semantic propagation
    /// verification (#qfuflia-a2-verifier-reuse): the Unknown-domain path
    /// built a fresh Nelson-Oppen combiner per verified propagation —
    /// measured 290k full e-graph inits in 15s on the SMT-COMP xs family.
    /// Reused via push/assert/check/pop; flavor fixed by the first
    /// propagation's term domains (a later propagation needing a theory the
    /// cached flavor lacks verifies to Unknown = allow, exactly like the
    /// fresh path's optimistic arm).
    pub(super) verify_mixed_cache: Option<crate::combined_solvers::TheoryCombiner<'a>>,
    /// Memoized verdicts for ARRAY-domain semantic propagation verification
    /// (#qfax-swap-verifier-memo). Key: (sorted reason literals, propagated
    /// literal) as (term id, value) pairs; value: whether the FRESH verifier
    /// (`verify_propagation_semantic` → `verify_array_propagation`) allowed
    /// the propagation. The fresh path re-inits the full e-graph per verified
    /// propagation (~34% of solve time on the SMT-COMP QF_AX swap family)
    /// while CDCL re-derives the same theory propagations across
    /// backtracking/restarts; the verifier is a pure function of
    /// (terms, propagation) and TermIds are stable, so replaying a cached
    /// verdict is byte-identical to re-running the check. Gate strength
    /// unchanged: every DISTINCT query still runs the full fresh check.
    pub(super) verify_array_memo: HashMap<Vec<(u32, bool)>, bool>,
    /// Count of ARRAY-domain semantic verification queries that MISSED the
    /// memo — drives the warmup-then-sample policy (#12-restore mirror for
    /// arrays; see the Array arm in `propagate_impl`).
    pub(super) verify_array_sem_counter: u64,
    /// #verify-memo (`AY_VERIFY_MEMO=1`, default off = byte-identical):
    /// memoized ACCEPT verdicts for the remaining sampled semantic
    /// propagation-verification arms — the cached mixed-domain Nelson-Oppen
    /// verifier (Unknown domain) and the fresh-solver dispatch
    /// (Arithmetic/BitVec/String). Same key discipline as
    /// `verify_array_memo`: (sorted reason literals, propagated literal) as
    /// (term id, value) pairs — the canonical signature of the exact
    /// verified obligation `reason ∧ ¬propagated`. Trust-TRUE-only (the
    /// `verify_conflict_semantic_memo` discipline): a hit replays a verdict
    /// recorded from a FULL verification of the byte-identical obligation;
    /// rejections are never memoized, so every failure re-runs the complete
    /// fail-closed check. Executor-owned (wired like `verify_memo` above) so
    /// verdicts survive per-iteration extension rebuilds — an extension-owned
    /// memo measured only a 31% hit rate on hash_sat_08_04 because CDCL
    /// re-derives the same propagations across split-loop iterations.
    /// Probed/populated only when the env flag is armed; inert otherwise.
    pub(super) verify_prop_memo: Option<&'a mut crate::verification::PropSemanticVerifyMemo>,
    /// Wall-clock deadline for the whole DPLL(T) solve, forwarded from the
    /// `DpllT`/`Executor` `solve_deadline` at construction (see
    /// [`TheoryExtension::with_solve_deadline`]).
    ///
    /// Polled at the top of `propagate_impl()` — the BCP hot loop the SAT
    /// solver drives once per round. A diverging theory-propagation churn
    /// (the "asserting theory atom at level 0" spin) makes neither conflicts
    /// nor decisions, so the CDCL loop's coarse `should_stop` poll (every 100
    /// conflicts / 1000 decisions) never fires and an installed deadline is
    /// silently shed — the T3 CHC/PDR divergence
    /// (the development design notes). Polling
    /// here is the one point guaranteed to execute every iteration of that
    /// spin. A deadline hit only ever degrades the solve to `Unknown`
    /// (fail-closed: never a wrong Sat/Unsat verdict).
    pub(super) solve_deadline: Option<ay_core::time::Instant>,
    /// Conflict-verification support literals (`DpllT`'s combined
    /// `dt_verification_axioms ++ ematching_support_axioms`), forwarded at
    /// construction via [`TheoryExtension::with_support_axioms`]. Each is true in
    /// every model of the problem (datatype tautology OR ground instance of an
    /// unconditionally-asserted Forall), so asserting them in the eager
    /// `check()`/`propagate()` fresh conflict verifiers can only CONFIRM a
    /// genuine conflict, never launder a spurious one. Empty (`&[]`, the default)
    /// for quantifier-free / non-datatype problems, so the eager verification
    /// path is byte-identical to before.
    pub(super) support_axioms: Vec<ay_core::TheoryLit>,
}

pub(super) struct ProofContext<'a> {
    pub(super) tracker: &'a mut ProofTracker,
    pub(super) negations: &'a HashMap<TermId, TermId>,
}
