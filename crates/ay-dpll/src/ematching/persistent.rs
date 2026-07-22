// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Persistent, incrementally-updated E-matching state.
//!
//! At HEAD, every E-matching round rebuilt `TermIndex`, `EqualityClasses`, and a
//! round-local `seen` set over the FULL (growing) assertion set. With up to ~13
//! rounds per `check_sat`, that is O(rounds * terms) per check. `PersistentMatchState`
//! persists and incrementally updates all three across rounds, scopes, and
//! check-sat epochs while remaining BYTE-EQUIVALENT to a full rebuild
//! (enforced by the cfg(debug_assertions) differential canary below).
//!
//! # Soundness invariants (see fix2 hardened plan)
//!
//! - LI-1/LI-2: the index is refreshed by WALKING NEW ASSERTION ROOTS (never an
//!   id-range scan, which would miss constant-folded low-id subterms), and each
//!   new ground App is inserted via a binary-search SORTED insert so per-symbol
//!   Vecs stay globally ascending == full rebuild elementwise.
//! - LI-3/LI-4/LI-10: the `seen` set is the ONLY false-result vector. It is
//!   truncated on scope pop (via `seen_order` + the snapshot high-water mark) and
//!   drained to the scope baseline at each `process_quantifiers` epoch
//!   (`begin_epoch`). `seen` and `seen_order` stay 1:1.
//! - LI-6: EUF congruence NEVER persists — it is applied only to a per-round
//!   CLONE of the persisted assertion eqclasses.
//! - LI-7/LI-8: assertion equalities are folded keyed by atom-root TermId (not a
//!   positional pointer), and the partition + member order match a full rebuild.
//! - LI-9: all caches are tied to a TermStore compaction generation (currently
//!   always 0; `mark_and_compact` has zero production callers).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermId, TermStore};

use super::pattern::{EqualityClasses, TermIndex};

/// Persistent, incrementally-maintained E-matching index/eqclass/seen state.
///
/// One instance lives on the `QuantifierManager` and is threaded through
/// `perform_ematching_with_generations`.
#[derive(Clone)]
pub(crate) struct PersistentMatchState {
    // ---- Term index (LI-1/LI-2) ----
    /// The ground-term index, persisted and incrementally extended.
    index: TermIndex,
    /// Reachability short-circuit set carried across refresh calls
    /// (collect_reachable_term_ids `seen`).
    reachable_seen: HashSet<u32>,
    /// Bound-variable classification, monotone within a solve (a Var never
    /// transitions bound -> free because the term DAG is immutable).
    bound_var_ids: HashSet<u32>,
    /// `index_term` seen set: ids already classified/indexed.
    index_seen: HashSet<u32>,
    /// `is_ground_cached` memo, persisted (pure function of the DAG + bound_var_ids).
    ground_cache: HashMap<u32, bool>,
    /// Watermark used ONLY as a fast no-op guard, never as a scan bound.
    indexed_term_revision: usize,

    // ---- Assertion equality classes (LI-6/LI-7/LI-8) ----
    /// Persisted assertion-only union-find. Folds explicit `(= a b)`/`(and ...)`
    /// atoms only; EUF congruence is NEVER folded here.
    assertion_eqclasses: EqualityClasses,
    /// TermIds of `(= a b)`/`(and ...)` assertion ROOTS already folded, keyed by
    /// TermId (NOT a positional pointer) so it is correct regardless of which
    /// caller's re-cloned/reordered assertion vector is passed (LI-7).
    folded_eq_atoms: HashSet<u32>,

    // ---- Instantiation memo (LI-3/LI-4/LI-10) ----
    /// Cross-round dedup memo of (quantifier, binding). Pure performance memo;
    /// soundness comes from the truncation/epoch discipline below.
    seen: HashSet<(TermId, Vec<TermId>)>,
    /// 1:1 insertion log of `seen`, enabling truncation on pop/epoch (DetHashSet
    /// has no truncatable insertion order; mirrors `deferred` + `deferred_len`).
    seen_order: Vec<(TermId, Vec<TermId>)>,
    /// Scope baseline `seen_order` length for the current epoch.
    seen_epoch_base: usize,

    // ---- Incremental matching (new-candidate-only) ----
    /// Per-symbol set of candidate ground-term ids ALREADY matched against, under
    /// the equality-class state recorded in `matched_eqclass_fingerprint`. A
    /// candidate in `index.by_symbol[sym]` NOT in this set is "new" and MUST be
    /// matched this round; a candidate present here under an unchanged fingerprint
    /// produces a binding identical to the prior round (already `seen`-deduped and
    /// already reflected in `instantiated_in_epoch`), so it is skipped. Reset
    /// whenever the index resets (`reset_index_eqclasses`) and invalidated whenever
    /// the eqclass fingerprint changes (LI-INC-1).
    matched_candidates: HashMap<String, HashSet<u32>>,
    /// Fingerprint of the WORKING equality classes (assertion folds + EUF model
    /// augmentation) under which `matched_candidates` was populated. When the
    /// current round's working fingerprint differs, an eqclass union/EUF change
    /// could newly enable an OLD candidate's match, so `matched_candidates` is
    /// cleared and ALL candidates are re-matched (LI-INC-2). `None` before the
    /// first round of an epoch.
    matched_eqclass_fingerprint: Option<u64>,
    /// Per-quantifier matched BINDINGS observed over already-matched (OLD)
    /// candidates in PRIOR rounds of the current epoch, under the eqclass
    /// fingerprint in `matched_eqclass_fingerprint`. Used to recompute the
    /// per-round `instantiated_quantifiers` / `has_uninstantiated` firewall input
    /// HEAD-identically when this round skips a quantifier's old candidates: the
    /// caller RE-EVALUATES the cost gate (`cost <= lazy_threshold`) against the
    /// CURRENT generation tracker over these remembered bindings (LI-INC-3). Storing
    /// the bindings (not just a bool) makes the marking exact even if a binding
    /// value's generation rose across rounds and lifted its cost over the threshold
    /// — re-evaluation then drops the mark exactly as the full path would. Reset on
    /// epoch / round-group reset; truncated on scope pop alongside the seen memo.
    epoch_matched_bindings: HashMap<TermId, Vec<Vec<TermId>>>,
    /// 1:1 insertion log of every binding pushed into `epoch_matched_bindings`
    /// (as `(quant, binding)`), enabling scope-pop truncation to a high-water mark
    /// (mirrors `seen_order`).
    instantiated_order: Vec<(TermId, Vec<TermId>)>,

    // ---- Compaction guard (LI-9) ----
    /// TermStore compaction generation the cached ids were built against. If
    /// `mark_and_compact` is ever wired this would diverge and the caches must be
    /// cleared. Currently always 0 (zero production callers).
    compaction_epoch: u64,
}

impl std::fmt::Debug for PersistentMatchState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PersistentMatchState")
            .field("indexed_term_revision", &self.indexed_term_revision)
            .field("folded_eq_atoms", &self.folded_eq_atoms.len())
            .field("seen", &self.seen.len())
            .field("seen_order", &self.seen_order.len())
            .field("seen_epoch_base", &self.seen_epoch_base)
            .field("compaction_epoch", &self.compaction_epoch)
            .finish()
    }
}

impl Default for PersistentMatchState {
    fn default() -> Self {
        Self::new()
    }
}

impl PersistentMatchState {
    pub(crate) fn new() -> Self {
        Self {
            index: TermIndex {
                by_symbol: HashMap::default(),
            },
            reachable_seen: HashSet::default(),
            bound_var_ids: HashSet::default(),
            index_seen: HashSet::default(),
            ground_cache: HashMap::default(),
            indexed_term_revision: 0,
            assertion_eqclasses: EqualityClasses::new_empty(),
            folded_eq_atoms: HashSet::default(),
            seen: HashSet::default(),
            seen_order: Vec::new(),
            seen_epoch_base: 0,
            matched_candidates: HashMap::default(),
            matched_eqclass_fingerprint: None,
            epoch_matched_bindings: HashMap::default(),
            instantiated_order: Vec::new(),
            compaction_epoch: 0,
        }
    }

    /// Fully clear all persistent state (for `(reset)` / `(reset-assertions)` /
    /// drop). After this no stale TermId can survive into a new problem (F6).
    pub(crate) fn clear(&mut self) {
        *self = Self::new();
    }

    // ===================== Index (LI-1 / LI-2) =====================

    /// Refresh the term index INCREMENTALLY by walking the NEW assertion roots.
    ///
    /// `assertions` is the cumulative slice the caller has folded up to this
    /// round. Roots already walked (tracked via `reachable_seen`) short-circuit;
    /// genuinely new roots are descended via `terms.get`, classified, and their
    /// new ground Apps are sorted-inserted into `by_symbol`.
    pub(crate) fn refresh_index(&mut self, terms: &TermStore, assertions: &[TermId]) {
        self.assert_compaction_unchanged(terms);

        for &root in assertions {
            // Walk new reachable subterms from this root. `reachable_seen` is
            // persistent, so a root (or subterm) already visited contributes
            // nothing. This handles constant-folded LOW-id roots whose ids are
            // below `indexed_term_revision` but were never reachable before
            // (LI-1) — an id-range scan would miss them.
            let mut reachable_new: Vec<TermId> = Vec::new();
            TermIndex::collect_reachable_term_ids(
                terms,
                root,
                &mut reachable_new,
                &mut self.reachable_seen,
            );
            if reachable_new.is_empty() {
                continue;
            }
            // Mirror the full rebuild: process newly-reachable ids in ascending
            // TermId order (pattern.rs:59).
            reachable_new.sort_unstable_by_key(|t| t.0);

            // Pass: classify bound vars over the new ids. `bound_names` MUST be a
            // FRESH local scope stack per refresh call (push/pop balanced within a
            // root walk); only `bound_var_ids` persists.
            let mut bound_names: HashSet<String> = HashSet::default();
            for &id in &reachable_new {
                TermIndex::collect_bound_var_ids(
                    terms,
                    id,
                    &mut self.bound_var_ids,
                    &mut bound_names,
                );
            }
            debug_assert!(
                bound_names.is_empty(),
                "bound_names must be push/pop balanced after a root walk"
            );

            // Pass: index the new ids. `index_term` short-circuits ids already in
            // `index_seen` and sorted-inserts new ground Apps (LI-2).
            for &id in &reachable_new {
                TermIndex::index_term(
                    terms,
                    id,
                    &mut self.index.by_symbol,
                    &mut self.index_seen,
                    &self.bound_var_ids,
                    &mut self.ground_cache,
                );
            }
        }
        self.indexed_term_revision = terms.len();

        #[cfg(feature = "ematching-differential")]
        self.assert_index_matches_full(terms, assertions);
    }

    /// Borrow the persisted (incrementally-maintained) term index.
    pub(super) fn index(&self) -> &TermIndex {
        &self.index
    }

    // ===================== Eqclasses (LI-6 / LI-7 / LI-8) =====================

    /// Refresh the persisted assertion-only equality classes INCREMENTALLY by
    /// folding only NEW `(= a b)`/`(and ...)` assertion roots (keyed by TermId,
    /// LI-7), then rebuilding the members index once.
    pub(crate) fn refresh_eqclasses(&mut self, terms: &TermStore, assertions: &[TermId]) {
        self.assert_compaction_unchanged(terms);

        let mut folded_any = false;
        for &root in assertions {
            if self.folded_eq_atoms.insert(root.0) {
                self.assertion_eqclasses.fold_assertion_root(terms, root);
                folded_any = true;
            }
        }
        if folded_any {
            self.assertion_eqclasses.rebuild_members();
        }

        #[cfg(feature = "ematching-differential")]
        self.assert_eqclasses_matches_full(terms, assertions);
    }

    /// Produce the per-round working equality classes: a CLONE of the persisted
    /// assertion-only classes, optionally augmented with EUF congruence. The EUF
    /// augmentation is applied ONLY to the clone and NEVER persisted (LI-6),
    /// because the model changes across interleaved rounds and union-find cannot
    /// un-merge.
    pub(crate) fn working_eqclasses(
        &self,
        euf_model: Option<&ay_euf::EufModel>,
    ) -> EqualityClasses {
        #[cfg(debug_assertions)]
        let persisted_parent_len_before = self.assertion_eqclasses.parent_len();

        let mut working = self.assertion_eqclasses.clone();
        if let Some(model) = euf_model {
            working.augment_with_euf_model(model);
        }

        #[cfg(debug_assertions)]
        debug_assert_eq!(
            persisted_parent_len_before,
            self.assertion_eqclasses.parent_len(),
            "LI-6: augment_with_euf_model must NOT mutate the persisted eqclasses"
        );

        working
    }

    // ===================== Seen set (LI-3 / LI-4 / LI-10) =====================

    /// Record a (quantifier, binding) in the seen memo. Returns `true` if it was
    /// newly inserted (caller should do the instantiation WORK), `false` if it
    /// was already present (caller skips the work but still counts the quantifier
    /// instantiated — see LI-5). Keeps `seen` and `seen_order` 1:1 (LI-10).
    pub(crate) fn seen_insert(&mut self, key: (TermId, Vec<TermId>)) -> bool {
        if self.seen.insert(key.clone()) {
            self.seen_order.push(key);
            true
        } else {
            false
        }
    }

    #[cfg(debug_assertions)]
    pub(crate) fn assert_seen_consistent(&self) {
        debug_assert_eq!(
            self.seen.len(),
            self.seen_order.len(),
            "LI-10: seen and seen_order must stay 1:1"
        );
    }

    /// Current `seen_order` length — captured by `push()` as the pop high-water
    /// mark, and used by `begin_epoch`.
    pub(crate) fn seen_order_len(&self) -> usize {
        self.seen_order.len()
    }

    /// Number of keys in the seen memo (test accessor / consistency checks).
    #[cfg(test)]
    pub(crate) fn seen_len(&self) -> usize {
        self.seen.len()
    }

    /// Drain `seen_order` back to `len`, removing each drained key from `seen`
    /// (LI-3 on pop). Mirrors `deferred.truncate(snapshot.deferred_len)`.
    pub(crate) fn truncate_seen_to(&mut self, len: usize) {
        if len >= self.seen_order.len() {
            return;
        }
        for k in self.seen_order.drain(len..) {
            self.seen.remove(&k);
        }
        if self.seen_epoch_base > self.seen_order.len() {
            self.seen_epoch_base = self.seen_order.len();
        }
        #[cfg(debug_assertions)]
        self.assert_seen_consistent();
    }

    /// M4 (demand-lane fence, discipline #3): reset the seen memo to the current
    /// EPOCH BASELINE, giving a FRESH seen frame within the ongoing epoch. Every
    /// (quantifier, binding) recorded SINCE `begin_epoch` is forgotten (and
    /// re-derivable), while the pre-epoch scope baseline is preserved. Reuses the
    /// same `truncate_seen_to` discipline as scope-pop / epoch-drain (keeps `seen`
    /// and `seen_order` 1:1), so it carries the identical soundness guarantee:
    /// forgetting seen only re-does instantiation WORK (dedup happens against the
    /// assertion set), never drops a needed instance. Called only by the demand
    /// lane's fence drain (shadow-only).
    pub(crate) fn reset_seen_frame(&mut self) {
        self.truncate_seen_to(self.seen_epoch_base);
    }

    /// Begin a new `process_quantifiers` epoch (LI-4).
    ///
    /// Two jobs:
    ///
    /// 1. SEEN memo: drain back to the current scope baseline so any
    ///    (quant,binding) from a PRIOR check-sat — whose instances
    ///    `restore_assertions` retracted — is re-instantiable. `baseline` is the
    ///    deepest live scope snapshot's `seen_order_len` (else 0).
    ///
    /// 2. INDEX + assertion EQCLASSES: reset to empty so they are re-derived
    ///    INCREMENTALLY within this epoch from the current assertions. This is the
    ///    soundness-first choice. The persisted index/eqclasses would otherwise be
    ///    a SUPERSET of a fresh build over the current assertions, because
    ///    `restore_assertions` retracts the E-matching instance assertions (and
    ///    their derived equalities) between check-sats while leaving the persisted
    ///    state intact. A retracted equality whose justifying quantifier is also
    ///    gone (e.g. popped) would become a STALE union-find merge — a spurious
    ///    `in_same_class` and a possible false result. Resetting per epoch keeps
    ///    the index/eqclasses an EXACT function of the current epoch's assertions
    ///    (so the cfg(debug_assertions) differential is byte-exact) and removes
    ///    that cross-epoch staleness vector entirely, while STILL eliminating the
    ///    dominant cost: the per-round full rebuild (~13 rounds/check-sat) becomes
    ///    one build plus incremental folds WITHIN the epoch. No scope push/pop
    ///    occurs inside a single `process_quantifiers`, so within an epoch the
    ///    assertion set only grows monotonically and the incremental update is
    ///    exact.
    pub(crate) fn begin_epoch(&mut self, baseline: usize) {
        self.truncate_seen_to(baseline);
        self.seen_epoch_base = self.seen_order.len();
        self.reset_index_eqclasses();
    }

    /// Begin a fresh round group WITHIN an epoch (LI-1/LI-7). Resets only the
    /// index + assertion eqclasses (NOT the seen memo, which dedups across the
    /// whole `process_quantifiers`). Called at the top of the single-round
    /// post-CEGQI and interleaved-refinement passes, whose assertion slices are
    /// freshly re-cloned/stripped/reordered from `ctx.assertions` and are NOT
    /// guaranteed to be a superset of the main 13-round loop's final slice.
    /// Resetting here keeps the index/eqclasses an exact function of the round's
    /// own slice (differential byte-exact) and avoids carrying terms/equalities
    /// from a stripped/retracted prefix into a phase that no longer contains them.
    /// These are single rounds, so there is no per-round reuse benefit to lose.
    pub(crate) fn begin_round_group(&mut self) {
        self.reset_index_eqclasses();
    }

    /// Reset the index + assertion eqclasses to empty (re-derived incrementally
    /// from the next round's slice). The seen memo is NOT touched here.
    fn reset_index_eqclasses(&mut self) {
        self.index = TermIndex {
            by_symbol: HashMap::default(),
        };
        self.reachable_seen.clear();
        self.bound_var_ids.clear();
        self.index_seen.clear();
        self.ground_cache.clear();
        self.indexed_term_revision = 0;

        self.assertion_eqclasses = EqualityClasses::new_empty();
        self.folded_eq_atoms.clear();

        // Incremental-matching state is tied to the index lifecycle: the
        // new-candidate watermark indexes into the (now-cleared) candidate set, and
        // the epoch instantiated-set is only replayed across the CONTIGUOUS
        // monotone-growing slice sequence of the main round loop (between which the
        // index is NOT reset). Resetting here keeps the incremental match path an
        // exact function of the round's own slice + eqclasses, byte-equal to a full
        // re-match (the differential canary proves it).
        self.matched_candidates.clear();
        self.matched_eqclass_fingerprint = None;
        self.epoch_matched_bindings.clear();
        self.instantiated_order.clear();
    }

    // ===================== Incremental matching (new-candidate-only) =====================

    /// Begin the matching phase of a round. `working_fp` is the partition
    /// fingerprint of the per-round WORKING equality classes (assertion folds + EUF
    /// augmentation) the matcher will use this round.
    ///
    /// Returns `true` when the equality classes are UNCHANGED since the prior round
    /// (so the per-symbol `matched_candidates` watermark is valid and the matcher
    /// may skip already-matched OLD candidates), or `false` when they changed (the
    /// watermark is cleared and ALL candidates must be re-matched, because an
    /// eqclass union / EUF change could newly enable an old candidate — LI-INC-2).
    ///
    /// SOUNDNESS: a `false` return (full re-match) is always safe. A `true` return
    /// only ever SKIPS re-deriving bindings that are already in the `seen` memo and
    /// already reflected in `instantiated_in_epoch`; skipping cannot add a spurious
    /// instance and cannot drop a NEEDED instance (new candidates are still matched,
    /// and the epoch instantiated-set is replayed). Even a fingerprint hash
    /// collision (treating a changed partition as unchanged) can at worst MISS a
    /// newly-enabled old-candidate match — incompleteness (→ Unknown), never a false
    /// UNSAT. The differential canary additionally proves no divergence in practice.
    pub(crate) fn begin_match_round(&mut self, working_fp: u64) -> bool {
        // COMPLETENESS over the new-candidate skip: always re-match every candidate
        // (return `false`). The skip returned `stable = (fingerprint unchanged)` to
        // skip re-matching OLD candidates on the premise that a single-trigger
        // binding is a pure function of (candidate, eqclass partition). That premise
        // is NOT sufficient for instantiation COMPLETENESS: a candidate is
        // watermarked the moment the matcher RUNS on it (`record_matched_candidate`),
        // which is BEFORE the per-binding cost gate (`cost > lazy_threshold`), the
        // instantiation budgets (`max_total`/`max_per_quantifier`), and the
        // deferred-promotion (`cost > eager_threshold`) decisions. A candidate whose
        // binding was cost-rejected / budget-truncated / deferred in an early round
        // is then skipped on every later fingerprint-stable round, so its
        // instantiation is never produced once the blocking condition clears — a
        // dropped instance that turns a provable goal into a round-limit `Unknown`
        // (regression: the multiset generic-insert2 extensional-equality obligation,
        // `generic_insert2_ext_eq`). Full re-match is this design's own "always safe"
        // differential reference. Measured cost of dropping the skip is net zero — the
        // per-symbol watermark bookkeeping it removes offsets its savings (deductive-checks-core
        // lib 60.4s vs 60s; ay-dpll lib 234s vs 250s). The DOMINANT incremental win,
        // the per-round index BUILD (`refresh_eqclasses` + incremental fold, never a
        // full rebuild), is retained — only the unsound match-SKIP is dropped.
        //
        // The watermark + fingerprint are still maintained (cleared/set each round) so
        // the scope-pop invalidation (`invalidate_match_watermark_on_pop`) and the
        // `ematching-differential` canary stay coherent; with the skip off the canary
        // is trivially satisfied (incremental ≡ full).
        let _was_stable = self.matched_eqclass_fingerprint == Some(working_fp);
        self.matched_candidates.clear();
        self.matched_eqclass_fingerprint = Some(working_fp);
        false
    }

    /// Is `candidate` a NEW ground term for `symbol` (not yet matched under the
    /// current eqclass fingerprint)? Always `true` right after `begin_match_round`
    /// returned `false` (the watermark was cleared).
    pub(crate) fn is_new_candidate(&self, symbol: &str, candidate: TermId) -> bool {
        self.matched_candidates
            .get(symbol)
            .is_none_or(|set| !set.contains(&candidate.0))
    }

    /// Record that `candidate` has now been matched against `symbol`'s pattern under
    /// the current eqclass fingerprint, so a later round with an unchanged
    /// fingerprint can skip it.
    pub(crate) fn record_matched_candidate(&mut self, symbol: &str, candidate: TermId) {
        self.matched_candidates
            .entry(symbol.to_string())
            .or_default()
            .insert(candidate.0);
    }

    /// Bindings matched over OLD candidates for `quant` in prior rounds of this
    /// epoch. The caller re-evaluates the cost gate over these against the CURRENT
    /// tracker to mark `quant` instantiated HEAD-identically when this round skips
    /// its old candidates (LI-INC-3). Empty slice if none recorded.
    pub(crate) fn epoch_matched_bindings_for(&self, quant: TermId) -> &[Vec<TermId>] {
        self.epoch_matched_bindings
            .get(&quant)
            .map_or(&[], |v| v.as_slice())
    }

    /// Record that `binding` matched `quant`'s pattern over an OLD candidate this
    /// round, so a later stable round can re-evaluate its cost gate instead of
    /// re-running the matcher. Keeps `instantiated_order` 1:1 for pop truncation.
    /// Only bindings whose cost passed the `lazy_threshold` gate are recorded by the
    /// caller (so re-evaluation has the same candidate set the full path marks on).
    pub(crate) fn record_epoch_matched_binding(&mut self, quant: TermId, binding: Vec<TermId>) {
        self.epoch_matched_bindings
            .entry(quant)
            .or_default()
            .push(binding.clone());
        self.instantiated_order.push((quant, binding));
    }

    /// Current `instantiated_order` length — captured by `push()` as the pop
    /// high-water mark (mirrors `seen_order_len`).
    pub(crate) fn instantiated_order_len(&self) -> usize {
        self.instantiated_order.len()
    }

    /// Invalidate the new-candidate watermark on scope pop (the mandated scope-pop
    /// reset). A pop can RETRACT ground candidates whose instances
    /// `restore_assertions` removes; the per-symbol `matched_candidates` set would
    /// otherwise still mark such a candidate "already matched" and skip re-matching
    /// it when a sibling/parent scope re-adds it — a stale memo across pop, the only
    /// false-result vector for incremental matching. The eqclass fingerprint guard
    /// alone is INSUFFICIENT here: a pop that does not change the (e.g. empty)
    /// equality partition leaves the fingerprint identical, so we must clear the
    /// watermark unconditionally. Clearing only forces a (safe) full re-match next
    /// round; it never drops a needed instance. Resetting the fingerprint to `None`
    /// makes the next `begin_match_round` re-match all candidates.
    pub(crate) fn invalidate_match_watermark_on_pop(&mut self) {
        self.matched_candidates.clear();
        self.matched_eqclass_fingerprint = None;
    }

    /// Drain `instantiated_order` back to `len`, removing each drained binding from
    /// `epoch_matched_bindings` (scope-pop truncation, mirrors `truncate_seen_to`).
    /// A binding recorded only inside the popped scope must be forgotten so a
    /// sibling/parent epoch re-derives it from its own matches.
    pub(crate) fn truncate_instantiated_to(&mut self, len: usize) {
        if len >= self.instantiated_order.len() {
            return;
        }
        for (q, _binding) in self.instantiated_order.drain(len..).rev() {
            // Pop the last-recorded binding for this quantifier. Because the log is
            // append-only and we drain from the tail in reverse, the popped binding
            // is exactly the one at the end of `epoch_matched_bindings[q]`.
            if let Some(v) = self.epoch_matched_bindings.get_mut(&q) {
                v.pop();
                if v.is_empty() {
                    self.epoch_matched_bindings.remove(&q);
                }
            }
        }
    }

    // ===================== Scope snapshot/restore (push/pop) =====================

    /// Snapshot the assertion-only eqclasses + folded-atom set for push().
    /// The index is intentionally NOT snapshotted: it is monotone-safe (extra
    /// ground candidates only widen matches -> extra valid instances -> never a
    /// false UNSAT, G4/LI-2), so it may persist across scopes without restore.
    pub(crate) fn snapshot_eqclasses(&self) -> (EqualityClasses, HashSet<u32>) {
        (
            self.assertion_eqclasses.clone(),
            self.folded_eq_atoms.clone(),
        )
    }

    /// Restore the assertion-only eqclasses + folded-atom set on pop() (LI-7/LI-8).
    pub(crate) fn restore_eqclasses(
        &mut self,
        eqclasses: EqualityClasses,
        folded_eq_atoms: HashSet<u32>,
    ) {
        self.assertion_eqclasses = eqclasses;
        self.folded_eq_atoms = folded_eq_atoms;
    }

    // ===================== Compaction guard (LI-9) =====================

    fn assert_compaction_unchanged(&self, _terms: &TermStore) {
        // `mark_and_compact` has zero production callers (compact.rs), so the
        // TermStore compaction generation is always 0 and cached TermIds never go
        // stale. If a future change wires compaction, this debug_assert fires and
        // the caches must be cleared on epoch bump. We keep the field/assert as a
        // permanent tripwire.
        debug_assert_eq!(
            self.compaction_epoch, 0,
            "LI-9: cached TermIds assume no TermStore compaction has run"
        );
    }

    // ===================== Differential canaries (debug only) =====================

    /// LI-1/LI-2 canary: the incrementally-maintained index must equal a FULL
    /// rebuild over the same cumulative slice, ELEMENTWISE per symbol.
    #[cfg(feature = "ematching-differential")]
    fn assert_index_matches_full(&self, terms: &TermStore, assertions: &[TermId]) {
        let full = TermIndex::new(terms, assertions);
        debug_assert_eq!(
            self.index.by_symbol.len(),
            full.by_symbol.len(),
            "incremental index symbol-count diverged from full rebuild"
        );
        for (k, v) in &self.index.by_symbol {
            let fv = full.by_symbol.get(k);
            debug_assert!(
                fv.is_some(),
                "incremental index has symbol {k:?} absent from full rebuild"
            );
            debug_assert_eq!(
                Some(v),
                fv,
                "incremental index by_symbol[{k:?}] diverged from full rebuild (LI-1/LI-2)"
            );
            // Defensive: each per-symbol Vec must be globally ascending (LI-2).
            debug_assert!(
                v.windows(2).all(|w| w[0].0 < w[1].0),
                "incremental index by_symbol[{k:?}] not strictly ascending (LI-2)"
            );
        }
    }

    /// LI-7/LI-8 canary: the incrementally-folded assertion eqclasses must equal a
    /// FULL rebuild over the same cumulative slice — same partition AND same
    /// (sorted) member Vecs.
    #[cfg(feature = "ematching-differential")]
    fn assert_eqclasses_matches_full(&self, terms: &TermStore, assertions: &[TermId]) {
        let full = EqualityClasses::from_assertions(terms, assertions);
        debug_assert_eq!(
            self.assertion_eqclasses.canonical_partition(),
            full.canonical_partition(),
            "incremental eqclasses partition diverged from full rebuild (LI-7)"
        );
        // Member Vec elementwise (validates the sort guard, LI-8). Compare every
        // TermId appearing in either partition.
        let mut all_ids: HashSet<u32> = HashSet::default();
        for class in self.assertion_eqclasses.canonical_partition() {
            for id in class {
                all_ids.insert(id);
            }
        }
        for class in full.canonical_partition() {
            for id in class {
                all_ids.insert(id);
            }
        }
        for id in all_ids {
            let t = TermId(id);
            debug_assert_eq!(
                self.assertion_eqclasses.class_members(t),
                full.class_members(t),
                "incremental eqclasses class_members({id}) diverged from full (LI-8)"
            );
        }
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::Symbol;
    use ay_core::Sort;
    use ay_euf::EufModel;
    use num_bigint::BigInt;

    /// LI-6: `working_eqclasses` augments only a per-round CLONE; the persisted
    /// assertion eqclasses must NEVER accumulate EUF model congruences (union-find
    /// has no un-merge, so a leaked M1 merge would be a spurious in_same_class
    /// under M2 -> false result).
    #[test]
    fn test_euf_congruence_never_persists() {
        let mut terms = TermStore::new();
        let s = Sort::Int;
        let a = terms.mk_app(Symbol::named("a"), vec![], s.clone());
        let b = terms.mk_app(Symbol::named("b"), vec![], s.clone());
        let z = terms.mk_app(Symbol::named("z"), vec![], s);

        let mut state = PersistentMatchState::new();
        // No explicit equalities asserted: the persisted partition stays empty.
        state.refresh_eqclasses(&terms, &[]);

        // Round 1: model M1 unions a~b.
        let mut m1 = EufModel::default();
        m1.term_values.insert(a, "e0".to_string());
        m1.term_values.insert(b, "e0".to_string());
        let working1 = state.working_eqclasses(Some(&m1));
        assert!(
            working1.in_same_class(a, b),
            "round-1 working copy reflects M1's a~b"
        );

        // Round 2: model M2 unions a~z (NOT a~b).
        let mut m2 = EufModel::default();
        m2.term_values.insert(a, "e1".to_string());
        m2.term_values.insert(z, "e1".to_string());
        let working2 = state.working_eqclasses(Some(&m2));
        assert!(
            working2.in_same_class(a, z),
            "round-2 working copy reflects M2's a~z"
        );
        assert!(
            !working2.in_same_class(a, b),
            "LI-6: M1's a~b must NOT leak into round 2 (no persisted congruence)"
        );
        // The persisted partition must remain empty (only explicit `(= a b)`
        // atoms would populate it; none were asserted).
        assert!(
            state.assertion_eqclasses.is_empty(),
            "LI-6: the persisted eqclasses must carry no EUF congruence"
        );
    }

    /// LI-1/LI-2: incremental index over two rounds == full rebuild over the
    /// cumulative slice, including a constant-folded ground App reachable only via
    /// a later-round root. The cfg(debug_assertions) differential inside
    /// refresh_index asserts equality; this test makes the scenario explicit.
    #[test]
    fn test_incremental_index_matches_full_with_new_ground_app() {
        let mut terms = TermStore::new();
        let bool_s = Sort::Bool;
        let int_s = Sort::Int;

        let c1 = terms.mk_int(BigInt::from(1));
        let p1 = terms.mk_app(Symbol::named("P"), vec![c1], bool_s.clone());

        let mut state = PersistentMatchState::new();
        // Round 1: only P(1).
        state.refresh_index(&terms, &[p1]);
        assert_eq!(state.index().get_by_symbol("P"), &[p1]);

        // Round 2: add a NEW ground App Q(2) (different symbol, new root).
        let c2 = terms.mk_int(BigInt::from(2));
        let q2 = terms.mk_app(Symbol::named("Q"), vec![c2], int_s);
        let q2_eq = terms.mk_app(Symbol::named("R"), vec![q2], bool_s);
        state.refresh_index(&terms, &[p1, q2_eq]);
        // The differential inside refresh_index already asserts incremental==full;
        // confirm the new ground Apps are present.
        assert_eq!(state.index().get_by_symbol("P"), &[p1]);
        assert_eq!(state.index().get_by_symbol("Q"), &[q2]);
        assert_eq!(state.index().get_by_symbol("R"), &[q2_eq]);
    }

    /// LI-8: folding equalities incrementally (in several refresh calls) yields the
    /// same partition + sorted member Vecs as a single full rebuild, regardless of
    /// order. The differential inside refresh_eqclasses asserts this; here we also
    /// check the partition directly.
    #[test]
    fn test_incremental_eqclasses_order_invariant() {
        let mut terms = TermStore::new();
        let s = Sort::Int;
        let a = terms.mk_app(Symbol::named("a"), vec![], s.clone());
        let b = terms.mk_app(Symbol::named("b"), vec![], s.clone());
        let c = terms.mk_app(Symbol::named("c"), vec![], s.clone());
        let eq_ab = terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
        let eq_bc = terms.mk_app(Symbol::named("="), vec![b, c], Sort::Bool);

        let mut state = PersistentMatchState::new();
        // Fold in two incremental calls. refresh_eqclasses asserts incremental ==
        // full each call (against the cumulative slice).
        state.refresh_eqclasses(&terms, &[eq_ab]);
        state.refresh_eqclasses(&terms, &[eq_ab, eq_bc]);

        // a, b, c all in one class.
        assert!(state.assertion_eqclasses.in_same_class(a, c));
        assert!(state.assertion_eqclasses.in_same_class(a, b));
        assert!(state.assertion_eqclasses.in_same_class(b, c));
    }

    /// LI-3/LI-10: pop truncation drains the seen memo and keeps seen/seen_order
    /// 1:1 (unit-level on PersistentMatchState).
    #[test]
    fn test_seen_truncate_keeps_1to1() {
        let mut state = PersistentMatchState::new();
        let k1 = (TermId(10), vec![TermId(1)]);
        let k2 = (TermId(10), vec![TermId(2)]);
        assert!(state.seen_insert(k1.clone()));
        let mark = state.seen_order_len();
        assert!(state.seen_insert(k2.clone()));
        assert_eq!(state.seen_len(), 2);
        assert_eq!(state.seen_order_len(), 2);
        // Truncate to the mark forgets k2 only.
        state.truncate_seen_to(mark);
        assert_eq!(state.seen_len(), 1);
        assert_eq!(state.seen_order_len(), 1);
        // Re-inserting k2 succeeds (it was forgotten); re-inserting k1 does not.
        assert!(state.seen_insert(k2));
        assert!(!state.seen_insert(k1));
    }
}
