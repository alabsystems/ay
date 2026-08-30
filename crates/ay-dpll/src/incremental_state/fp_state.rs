// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental FP solving state with persistent SAT reuse.
//!
//! The fifth incremental subsystem, modelled directly on
//! [`IncrementalBvState`](super::IncrementalBvState). Read that type's `pop`
//! doc comment first: the two-bucket clause rule and the Bitwuzla provenance
//! are stated there once and are not repeated here.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermId, TermStore, TseitinState};
use ay_fp::FpEncodingCache;
use ay_sat::Solver as SatSolver;

use super::IncrementalSubsystem;

/// Result of observing the current authored assertion set for persistence.
pub(crate) enum FpIncrementalAdmission {
    /// Every current FP-relevant root has an exact reusable identity.
    Admit,
    /// The full current set has not been observed; answer statelessly.
    Defer,
}

/// Persistent state for the incremental FP lane.
///
/// Before this existed, `solve_fp` built `Tseitin::new`, `FpSolver::new_with_tseitin`
/// and `SatSolver::new` function-locally on EVERY check-sat, so push/pop never
/// reached the FP lane and each solve handed a brand-new SAT solver the same
/// CNF — re-arming the whole preprocessing suite (`preprocess_enabled` defaults
/// to true and `finish_initial_preprocessing` disarms it exactly once per
/// solver lifetime). Surviving is the entire fix.
///
/// The single hard invariant is [`Self::fp_var_offset`]: FP bit-blaster
/// variable `v` occupies SAT variable `v + fp_var_offset` FOREVER. Four
/// consumers must agree on it — circuit clauses, Tseitin↔FP links, the
/// congruence/ITE links, and model extraction. `solve_fp` used to recompute it
/// as `tseitin_result.num_vars` on every call, a value that moves with the
/// assertion set; freezing it is what makes any persistence safe at all.
pub(crate) struct IncrementalFpState {
    /// Current scope depth (0 = global, 1+ = inside a push).
    pub(crate) scope_depth: usize,
    /// Pushes that arrived before the SAT solver existed.
    pub(crate) pending_pushes: usize,

    /// Persistent SAT solver, reused for the whole session.
    pub(crate) persistent_sat: Option<SatSolver>,
    /// Persistent Tseitin state (variable numbering + term maps).
    pub(crate) tseitin_state: TseitinState,
    /// Persistent `FpSolver` caches. `FpSolver<'a>` borrows the `TermStore` and
    /// so cannot itself be a field here; the cache is what persists.
    pub(crate) fp_cache: FpEncodingCache,

    /// Assertion → its Tseitin root literal (#1452). Definitional clauses are
    /// global; only the activation unit is scoped, so survivors of a pop must
    /// be re-activated from this map.
    pub(crate) encoded_assertions: HashMap<TermId, i32>,
    /// Shallowest scope at which each assertion currently has a live activation
    /// unit. Entries deeper than `scope_depth` are dropped on pop (#2822).
    pub(crate) assertion_activation_scope: HashMap<TermId, usize>,

    /// Stable FP variable offset. SET ONCE; never re-derived (#1453 for BV).
    pub(crate) fp_var_offset: Option<i32>,
    /// Next FP bit-blaster variable. Monotone; mirrors `fp_cache.next_var` and
    /// is the value handed back to the `FpSolver` each call.
    pub(crate) next_fp_var: u32,

    /// Tseitin variables already tied to their FP bit-blast counterpart.
    ///
    /// With a persistent Tseitin state the `var_to_term` walk sees the WHOLE
    /// accumulated map, so without this guard every FP predicate would be
    /// re-blasted (and re-linked) on every check-sat. Re-blasting is sound —
    /// both literals are definitionally the same Boolean function of the same
    /// cached bits — but it grows the variable count without bound.
    pub(crate) linked_predicate_vars: HashSet<u32>,
    /// Free Bool inputs already named at the Tseitin level and tied to their FP
    /// proxy literal. See the Bool-input link pass in `fp/incremental.rs` for
    /// why an unlinked literal must never survive a check-sat, and why
    /// refreshing `term_to_cnf` alone does not fix it.
    pub(crate) linked_bool_inputs: HashSet<TermId>,

    /// Assertions observed at incremental entry or on the last deferred query.
    ///
    /// An entry probe is captured before a `TermStore` borrow is available and
    /// may temporarily include Bool-only roots; only current FP-relevant roots
    /// are ever looked up in it. Later probes contain only roots whose DAG
    /// mentions FP. This metadata retains no SAT state or encoding.
    reuse_probe: Option<HashSet<TermId>>,
    /// Memoized "this term's DAG mentions an FP-sorted term" predicate.
    /// Term data is immutable, so both positive and negative entries are stable.
    fp_relevance_cache: Vec<Option<bool>>,

    /// Number of check-sats this lane has served in the current session.
    ///
    /// Published as `fp_incremental.solves`. Diagnostic, but load-bearing for
    /// measurement: a differential sweep that never actually ENGAGED the lane
    /// is a clean result about nothing.
    pub(crate) solves: u64,

    /// Sticky opt-out. Once set the session never uses this lane again and
    /// every `solve_fp` falls back to the untouched stateless pipeline.
    ///
    /// Set when the lane meets something it does not model incrementally
    /// (uninterpreted structure needing congruence, an encoding gap, an
    /// unsupported predicate). Always paired with a full teardown, so
    /// "disabled" means "behaves exactly as before this subsystem existed".
    pub(crate) disabled: bool,
}

impl IncrementalFpState {
    pub(crate) fn new() -> Self {
        Self {
            scope_depth: 0,
            pending_pushes: 0,
            persistent_sat: None,
            tseitin_state: TseitinState::new(),
            fp_cache: FpEncodingCache::default(),
            encoded_assertions: HashMap::default(),
            assertion_activation_scope: HashMap::default(),
            fp_var_offset: None,
            next_fp_var: 1,
            linked_predicate_vars: HashSet::default(),
            linked_bool_inputs: HashSet::default(),
            reuse_probe: None,
            fp_relevance_cache: Vec::new(),
            solves: 0,
            disabled: false,
        }
    }

    /// Keep Tseitin allocation clear of BOTH the scope selectors and the frozen
    /// FP range. Run FIRST, before [`Self::sync_next_fp_var`] (#7031).
    ///
    /// Clause (a) must use `total_num_vars`, not `user_num_vars`: `Solver::push`
    /// allocates a scope SELECTOR variable, and a Tseitin variable that collides
    /// with a live selector is assumed `¬selector` and silently forced — a wrong
    /// answer with no symptom.
    ///
    /// Clause (b) is the non-obvious one. Freezing `fp_var_offset` means the
    /// Tseitin space stops being a contiguous prefix: variables allocated on a
    /// later check-sat would land INSIDE the FP range. Afterwards the Tseitin
    /// space is `[1 .. offset] ∪ [offset + next_fp_var .. )` (#7015 for BV).
    pub(crate) fn sync_tseitin_next_var(&mut self) {
        if let Some(ref sat) = self.persistent_sat {
            let sat_total = sat.total_num_vars() as u32;
            self.tseitin_state.next_var = self.tseitin_state.next_var.max(sat_total + 1);
        }
        if let Some(offset) = self.fp_var_offset {
            let max_fp_sat_pos = (self.next_fp_var as i64 - 1) + offset as i64;
            if max_fp_sat_pos >= 0 {
                self.tseitin_state.next_var =
                    self.tseitin_state.next_var.max(max_fp_sat_pos as u32 + 1);
            }
        }
    }

    /// Keep FP allocation clear of Tseitin variables and scope selectors. Run
    /// SECOND — it reads the frontier the call above just advanced.
    ///
    /// BOTH bounds are the TIGHT form, not BV's looser `max(tseitin_next)` /
    /// `max(sat_total + 1)`. Under `offset_cnf_lit(v, off) = v + off` an FP
    /// variable `v` occupies SAT position `v + off`, so avoiding a collision
    /// needs `v + off >= bound`, i.e. `v >= bound - off` — not `v >= bound`.
    ///
    /// The loose form is safe but not merely wasteful: it feeds back. It pushes
    /// `next_fp_var` up to the Tseitin frontier, which the sync above then
    /// pushes up to `offset + next_fp_var`, which pushes `next_fp_var` up
    /// again — the SAT variable space grows by `offset` on EVERY check-sat, for
    /// the whole session. With the tight form the pair reaches its fixed point
    /// after one round (`tseitin_next == offset + next_fp_var`) and the space
    /// grows only when the encoding actually grows.
    pub(crate) fn sync_next_fp_var(&mut self) {
        let offset = self.fp_var_offset.unwrap_or(0) as i64;
        let above_tseitin = (self.tseitin_state.next_var as i64 - offset).max(1);
        self.next_fp_var = self.next_fp_var.max(above_tseitin as u32);
        if let Some(ref sat) = self.persistent_sat {
            let sat_total = sat.total_num_vars() as i64;
            let above_selectors = (sat_total - offset + 1).max(1);
            self.next_fp_var = self.next_fp_var.max(above_selectors as u32);
        }
        self.fp_cache.next_var = self.fp_cache.next_var.max(self.next_fp_var);
    }

    /// Capture the assertions outside the first incremental scope.
    ///
    /// They are guaranteed to remain live after the corresponding push. FP
    /// relevance is filtered lazily at check-sat, avoiding a DAG walk on push.
    pub(crate) fn record_incremental_entry(&mut self, assertions: &[TermId]) {
        if !self.disabled && self.scope_depth == 0 && self.solves == 0 && self.reuse_probe.is_none()
        {
            self.reuse_probe = Some(assertions.iter().copied().collect());
        }
    }

    /// Whether `root` transitively mentions an FP-sorted term.
    ///
    /// Iterative post-order keeps this safe for deep authored DAGs. The cache
    /// makes a disjoint batch linear in newly seen terms across the session,
    /// rather than re-walking shared prefixes at every check-sat.
    fn term_mentions_fp(&mut self, terms: &TermStore, root: TermId) -> bool {
        if let Some(relevant) = self.cached_fp_relevance(root) {
            return relevant;
        }

        let mut stack = vec![(root, false)];
        while let Some((term, expanded)) = stack.pop() {
            if self.cached_fp_relevance(term).is_some() {
                continue;
            }
            if matches!(terms.sort(term), Sort::FloatingPoint(..)) {
                self.cache_fp_relevance(term, true);
                continue;
            }
            let children = terms.children(term);
            if expanded {
                let relevant = children
                    .iter()
                    .any(|&child| self.cached_fp_relevance(child) == Some(true));
                self.cache_fp_relevance(term, relevant);
            } else {
                stack.push((term, true));
                stack.extend(children.into_iter().map(|child| (child, false)));
            }
        }
        self.cached_fp_relevance(root) == Some(true)
    }

    fn cached_fp_relevance(&self, term: TermId) -> Option<bool> {
        self.fp_relevance_cache
            .get(term.0 as usize)
            .copied()
            .flatten()
    }

    fn cache_fp_relevance(&mut self, term: TermId, relevant: bool) {
        let index = term.0 as usize;
        if self.fp_relevance_cache.len() <= index {
            self.fp_relevance_cache.resize(index + 1, None);
        }
        self.fp_relevance_cache[index] = Some(relevant);
    }

    fn fp_relevant_assertions(
        &mut self,
        terms: &TermStore,
        assertions: &[TermId],
    ) -> HashSet<TermId> {
        assertions
            .iter()
            .copied()
            .filter(|&term| self.term_mentions_fp(terms, term))
            .collect()
    }

    /// Admit only when every current FP-relevant root was already observed.
    ///
    /// Roots may survive continuously or be popped and reasserted: immutable
    /// `TermId` identity makes either reusable. Subsets/removals are therefore
    /// admitted immediately. Any novel root tears an active SAT state down but
    /// does not disable the lane: this query is the new full-set observation,
    /// and an identical repeat may rebuild persistence on the next check.
    pub(crate) fn observe_live_assertion_reuse(
        &mut self,
        terms: &TermStore,
        assertions: &[TermId],
    ) -> FpIncrementalAdmission {
        let relevant = self.fp_relevant_assertions(terms, assertions);
        if self.solves > 0 {
            if !relevant.is_empty()
                && relevant
                    .iter()
                    .all(|term| self.encoded_assertions.contains_key(term))
            {
                return FpIncrementalAdmission::Admit;
            }
            self.reset_sat_encoding_for_rebuild();
            self.reuse_probe = Some(relevant);
            return FpIncrementalAdmission::Defer;
        }

        let fully_observed = !relevant.is_empty()
            && self
                .reuse_probe
                .as_ref()
                .is_some_and(|previous| relevant.iter().all(|term| previous.contains(term)));
        self.reuse_probe = Some(relevant);
        if fully_observed {
            self.reuse_probe = None;
            FpIncrementalAdmission::Admit
        } else {
            FpIncrementalAdmission::Defer
        }
    }

    /// FULL teardown: drop the solver and every cache, keeping only the
    /// frontend scope depth so the next check-sat can rebuild the scope stack.
    ///
    /// Used by `reset()` / `(reset-assertions)`, the sticky [`Self::disabled`]
    /// opt-out, and a non-sticky restart when admission sees a novel FP root.
    /// Deliberately NOT the ordinary `pop()` path — see
    /// `IncrementalBvState::pop` for why scope retraction needs no teardown.
    ///
    /// `FpSolver::reset` (`ay-fp`'s `TheorySolver` impl) is NOT usable here: it
    /// restarts `next_var` at 1 while leaving `bool_input_lits`,
    /// `to_bv_unspec_sites`, `ieee_nan_encodings` and `term_to_cnf` populated
    /// with literals from the OLD numbering, aliasing every survivor onto a
    /// fresh variable.
    pub(crate) fn reset_sat_encoding_for_rebuild(&mut self) {
        // Exhaustive destructure (no `..`): a newly added field that needs
        // clearing on reset is a COMPILE ERROR here rather than a stale literal
        // over a restarted variable space (R9).
        let Self {
            scope_depth,
            pending_pushes,
            persistent_sat,
            tseitin_state,
            fp_cache,
            encoded_assertions,
            assertion_activation_scope,
            fp_var_offset,
            next_fp_var,
            linked_predicate_vars,
            linked_bool_inputs,
            reuse_probe,
            fp_relevance_cache,
            solves,
            disabled: _,
        } = self;
        *pending_pushes = *scope_depth;
        *persistent_sat = None;
        *tseitin_state = TseitinState::new();
        *fp_cache = FpEncodingCache::default();
        encoded_assertions.clear();
        assertion_activation_scope.clear();
        *fp_var_offset = None;
        *next_fp_var = 1;
        linked_predicate_vars.clear();
        linked_bool_inputs.clear();
        *reuse_probe = None;
        fp_relevance_cache.clear();
        *solves = 0;
    }

    /// Permanently opt this session out of the incremental FP lane and drop
    /// everything it built. Subsequent check-sats run the untouched stateless
    /// pipeline, i.e. exactly the pre-existing behaviour.
    pub(crate) fn disable_and_teardown(&mut self) {
        self.reset_sat_encoding_for_rebuild();
        self.disabled = true;
    }
}

impl IncrementalSubsystem for IncrementalFpState {
    fn push(&mut self) {
        self.scope_depth += 1;
        if let Some(ref mut sat) = self.persistent_sat {
            sat.push();
        } else {
            self.pending_pushes += 1;
        }
    }

    /// Retract one assertion scope without destroying any encoding.
    ///
    /// Safe by construction, exactly as for BV: every clause this lane installs
    /// is either scope-INDEPENDENT (Tseitin definitions, FP circuit clauses,
    /// Tseitin↔FP equivalence links, ITE condition links, and the Bool-input
    /// repair links — each a definitional extension over fresh variables, so
    /// model-preserving on the user's vocabulary) and goes in through
    /// `add_clause_global`, or it is the single scoped object: the activation
    /// unit on an assertion's Tseitin root.
    ///
    /// The one thing that must be retracted is the bookkeeping. `Solver::pop`
    /// satisfies the activation units installed deeper than the new depth, so
    /// the survivors have to be re-added on the next check-sat (#2822).
    fn pop(&mut self) -> bool {
        if self.scope_depth > 0 {
            self.scope_depth -= 1;
            if let Some(ref mut sat) = self.persistent_sat {
                let _ = sat.pop();
            } else if self.pending_pushes > 0 {
                self.pending_pushes -= 1;
            }
            self.assertion_activation_scope
                .retain(|_, depth| *depth <= self.scope_depth);
            true
        } else {
            false
        }
    }

    fn reset(&mut self) {
        self.scope_depth = 0;
        self.reset_sat_encoding_for_rebuild();
        // `(reset)` starts a new problem, so a sticky opt-out earned by the
        // PREVIOUS problem's shape must not disable the lane for it. (The
        // `drop` arm of `for_each_incremental_subsystem!` handles
        // `(reset-assertions)` by discarding the state entirely.)
        self.disabled = false;
    }
}
