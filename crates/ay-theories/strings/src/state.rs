// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver state for the string theory.
//!
//! Tracks asserted equalities/disequalities, equivalence classes, and
//! per-class metadata (constant values, concat terms). Uses a union-find
//! with trail-based backtracking for incremental push/pop.
//!
//! Query methods (explain, length checks, nonempty detection), scope
//! management (push/pop/reset), and string helpers are in `state_query`.
//!
//! Reference: `reference/cvc5/src/theory/strings/solver_state.h`
//! Reference: `reference/cvc5/src/theory/strings/solver_state.cpp`

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::safe_eprintln;
use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::{Sort, TheoryLit};
use std::cell::RefCell;

/// Metadata for a single equivalence class of string terms.
#[derive(Debug, Clone, Default)]
pub(crate) struct EqcInfo {
    /// If this equivalence class contains a string constant, store its value.
    pub constant: Option<String>,
    /// Representative concat terms in this equivalence class.
    pub concat_terms: Vec<TermId>,
    /// All terms in this equivalence class.
    pub members: Vec<TermId>,
    /// The `str.len(x)` term for this EQC's representative, if registered.
    ///
    /// CVC5 reference: `d_lengthTerm` in `eqc_info.h`.
    /// Set during `register_term` when a `str.len(x)` application is seen,
    /// with `x` mapped to its EQC representative. Propagated on `merge`.
    pub length_term: Option<TermId>,
}

/// Trail entry for undo on pop.
#[derive(Debug, Clone)]
pub(crate) enum TrailEntry {
    /// An assertion was added.
    Assertion,
    /// A disequality was added.
    Disequality,
    /// Two EQCs were merged:
    /// (loser, old_parent, saved_loser_eqc_info, old_merge_reasons).
    /// The loser's EQC info is saved so it can be restored on pop (F1 fix).
    /// The old merge reasons are saved so explain() remains correct across pop.
    Merge(TermId, TermId, Option<EqcInfo>, Option<Vec<TheoryLit>>),
    /// An EQC was created for this term.
    EqcCreated(TermId),
    /// A constant was set on an EQC.
    EqcConstantSet(TermId),
    /// A concat term was added to an EQC.
    EqcConcatAdded(TermId),
    /// A member was added to an EQC.
    EqcMemberAdded(TermId),
    /// A length term was set on an EQC.
    EqcLengthSet(TermId),
    /// A pending conflict was set.
    PendingConflictSet,
    /// A proof edge was added to the proof forest.
    ProofEdge,
    /// An integer constant cache entry was set/updated.
    /// Stores (rep, old_value) for rollback. The cached value carries the
    /// concrete integer constant `TermId` alongside the value so derived
    /// facts can be EXPLAINED through the proof forest (NF-engine closure 2).
    IntConstCache(TermId, Option<(i64, TermId)>),
}

/// Central state shared by all string sub-solvers.
///
/// Mirrors CVC5's `SolverState`: wraps union-find-based equivalence class
/// tracking, disequality lists, and per-class metadata with trail-based
/// backtracking.
#[derive(Debug, Default)]
pub(crate) struct SolverState {
    /// Asserted string-related literals from the SAT solver.
    pub(crate) assertions: Vec<TheoryLit>,
    /// Union-find parent map. Each term maps to its parent (itself if root).
    pub(crate) parent: HashMap<TermId, TermId>,
    /// Equivalence class representative → class info.
    pub(crate) eqc_info: HashMap<TermId, EqcInfo>,
    /// Disequalities: pairs of (rep1, rep2, original_literal).
    pub(crate) disequalities: Vec<(TermId, TermId, TheoryLit)>,
    /// Pending conflict from merge: two constants with different values
    /// were placed in the same EQC. Stores the EQC representative TermIds
    /// of the conflicting constants so `explain()` can produce a targeted
    /// conflict explanation.
    pub(crate) pending_conflict: Option<(TermId, TermId)>,
    /// Trail for undo on pop.
    pub(crate) trail: Vec<TrailEntry>,
    /// Scope stack: trail length at each push.
    pub(crate) scope_stack: Vec<usize>,
    /// Cached TermId for the empty string constant `""`.
    /// Set on first registration of a `""` constant via `register_term`.
    pub(crate) empty_string_id: Option<TermId>,
    /// Merge reasons: for each non-root term, the explanation literals that
    /// merged it into its parent. Used by `explain()` for targeted explanations.
    pub(crate) merge_reasons: HashMap<TermId, Vec<TheoryLit>>,
    /// Proof forest: records original merge endpoints for explain().
    ///
    /// Each entry is (a, b, reasons) where merge(a, b, reasons) was called
    /// with the original term IDs (before find()). This is needed because
    /// the union-find parent tree collapses transitive chains: merge(b,c)
    /// with find(b)=a stores parent[c]=a, losing the b=c provenance.
    /// explain() traverses this graph to find the full path.
    pub(crate) proof_edges: Vec<(TermId, TermId, Vec<TheoryLit>)>,
    /// Version counter for `proof_edges`, incremented on every push/pop/clear.
    /// Used to invalidate `cached_adj`.
    pub(crate) proof_edges_version: usize,
    /// Cached adjacency map for `explain()` BFS.
    ///
    /// Maps each TermId to its neighbors as `(neighbor, edge_index)` pairs
    /// where `edge_index` is an index into `proof_edges`. Rebuilt lazily
    /// when `proof_edges_version` changes.
    ///
    /// Uses `RefCell` for interior mutability since `explain()` takes `&self`.
    /// The `usize` is the version at which the cache was built.
    #[allow(clippy::type_complexity)]
    pub(crate) cached_adj: RefCell<(usize, HashMap<TermId, Vec<(TermId, usize)>>)>,
    /// Version counter for `eqc_info` key set, incremented on every
    /// insert/remove/clear. Used to invalidate `cached_reps`.
    pub(crate) eqc_version: usize,
    /// Cached sorted representative list for `eqc_representatives()`.
    ///
    /// Rebuilt lazily when `eqc_version` changes. Called 10+ times per
    /// `check()` cycle; caching avoids redundant collect+sort.
    pub(crate) cached_reps: RefCell<(usize, Vec<TermId>)>,
    // ========================================================================
    // Soundness: poisoned flag (#8454)
    // ========================================================================
    /// Set when an internal invariant violation is detected (e.g., trail
    /// underflow in pop()). When true, the owning StringSolver's next check()
    /// returns TheoryResult::Unknown to prevent incorrect results based on
    /// corrupted union-find / EQC state.
    pub(crate) poisoned: bool,
    /// Cache: EQC representative → (integer constant value, constant TermId).
    ///
    /// Populated when an integer constant is registered or merged into an EQC.
    /// Avoids O(N) scan over all parent keys in `resolve_int_constant()`.
    /// The constant `TermId` records WHICH concrete literal justified the
    /// value, so length-driven inferences can build proof-forest explanations
    /// (`explain(len_term, const_tid)`) instead of unexplained facts
    /// (NF-engine closure 2). Trail-based: changes recorded via
    /// `TrailEntry::IntConstCache`.
    pub(crate) int_const_cache: HashMap<TermId, (i64, TermId)>,
}

impl SolverState {
    /// Create a new, empty solver state.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Pre-register the empty string term ID.
    ///
    /// Called by the executor to ensure the empty string is always available
    /// for endpoint-empty inferences. Without this, formulas that don't
    /// contain an explicit `""` literal can't emit `x = ""` inferences
    /// (the solver can't create terms because it holds `&TermStore`, not
    /// `&mut TermStore`).
    pub(crate) fn set_empty_string_id(&mut self, terms: &TermStore, id: TermId) {
        if self.empty_string_id.is_none() {
            self.register_term(terms, id);
            self.empty_string_id = Some(id);
        }
    }

    /// Find the representative of a term's equivalence class.
    ///
    /// No path compression: with trail-based backtracking, path compression
    /// writes to `parent` without trail entries, causing stale pointers after
    /// pop. The performance cost is negligible for string EQC chains.
    pub(crate) fn find(&self, mut t: TermId) -> TermId {
        while let Some(&p) = self.parent.get(&t) {
            if p == t {
                break;
            }
            t = p;
        }
        t
    }

    /// Register a term in the union-find (make it its own root if not present).
    fn ensure_registered(&mut self, t: TermId) {
        if !self.parent.contains_key(&t) {
            self.parent.insert(t, t);
        }
    }

    /// Populate the integer constant cache for a term if it's an int constant.
    ///
    /// Called after `ensure_registered` for integer-sorted terms so that
    /// `resolve_int_constant` can do O(1) lookup instead of O(N) scan.
    fn maybe_cache_int_constant(&mut self, terms: &TermStore, t: TermId) {
        if let TermData::Const(Constant::Int(n)) = terms.get(t) {
            if let Ok(val) = n.try_into() {
                let val: i64 = val;
                let rep = self.find(t);
                let old = self.int_const_cache.insert(rep, (val, t));
                self.trail.push(TrailEntry::IntConstCache(rep, old));
            }
        }
    }

    /// Register a string term, creating its EQC and populating metadata.
    ///
    /// Recursively registers children of concat terms. Also detects
    /// `str.len(x)` applications and records the length term on `x`'s EQC.
    pub(crate) fn register_term(&mut self, terms: &TermStore, t: TermId) {
        if self.parent.contains_key(&t) {
            return;
        }
        self.ensure_registered(t);

        // Detect str.len(x) — has Sort::Int, but needs to record length_term
        // on the argument's EQC (CVC5: eqNotifyNewClass for STRING_LENGTH).
        if let TermData::App(sym, args) = terms.get(t) {
            if sym.name() == "str.len" && args.len() == 1 {
                let arg = args[0];
                self.register_term(terms, arg);
                let arg_rep = self.find(arg);
                if let Some(eqc) = self.eqc_info.get_mut(&arg_rep) {
                    if eqc.length_term.is_none() {
                        eqc.length_term = Some(t);
                        self.trail.push(TrailEntry::EqcLengthSet(arg_rep));
                    }
                }
                return;
            }
        }

        if *terms.sort(t) != Sort::String {
            return;
        }

        let eqc = self.eqc_info.entry(t).or_default();
        eqc.members.push(t);
        self.eqc_version += 1;
        self.trail.push(TrailEntry::EqcCreated(t));
        self.trail.push(TrailEntry::EqcMemberAdded(t));

        match terms.get(t) {
            TermData::Const(Constant::String(s)) => {
                if s.is_empty() && self.empty_string_id.is_none() {
                    self.empty_string_id = Some(t);
                }
                eqc.constant = Some(s.clone());
                self.trail.push(TrailEntry::EqcConstantSet(t));
            }
            TermData::App(sym, args) if sym.name() == "str.++" => {
                let args = args.clone();
                for &child in &args {
                    self.register_term(terms, child);
                }
                let Some(eqc) = self.eqc_info.get_mut(&t) else {
                    // Production soundness gate: eqc_info was just inserted at
                    // entry().or_default() above, so this should be unreachable.
                    // If recursive register_term somehow removed it, skip concat
                    // registration (sound but incomplete).
                    safe_eprintln!(
                        "BUG: strings eqc_info missing for registered term {t:?} — skipping concat registration"
                    );
                    return;
                };
                eqc.concat_terms.push(t);
                self.trail.push(TrailEntry::EqcConcatAdded(t));
            }
            _ => {}
        }

        // Closure 4 (`AY_STR_NF=1`, sub-flag 4): eager length-fact
        // registration. A `str.len(t)` application that already EXISTS in the
        // term store (every reduction axiom builds them: `len(sk_pre) = n`,
        // `len(skt) <= m`, ...) is linked to `t`'s EQC right now, instead of
        // only when the SAT solver happens to decide a literal mentioning it.
        // Without this the guarded length couplings of a reduction skolem web
        // stay invisible to `are_lengths_equal_with_entail` / `has_length_info`
        // until N-O bridging propagates an integer equality, so the deq pass
        // cannot triage and the NF pass cannot unify.
        //
        // Purely a VISIBILITY change: it records which `str.len` term measures
        // this EQC. It asserts no value and merges nothing, so no fact enters
        // the proof forest unexplained.
        if crate::str_nf_closure_enabled(4) {
            if let Some(len_t) = terms.find_app_named("str.len", &[t]) {
                if !self.parent.contains_key(&len_t) {
                    self.register_term(terms, len_t);
                }
            }
        }
    }

    /// Merge two equivalence classes with a single explanation literal.
    pub(crate) fn merge(&mut self, a: TermId, b: TermId, reason: TheoryLit) -> TermId {
        self.merge_with_explanation(a, b, std::slice::from_ref(&reason))
    }

    /// Merge two equivalence classes. Returns the new representative.
    ///
    /// If the merge would create a constant conflict (two distinct string
    /// constants in the same EQC), the merge still proceeds but a pending
    /// conflict is recorded. The base solver's `check_init()` picks this up.
    pub(crate) fn merge_with_explanation(
        &mut self,
        a: TermId,
        b: TermId,
        explanation: &[TheoryLit],
    ) -> TermId {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return ra;
        }

        let size_a = self.eqc_info.get(&ra).map_or(0, |e| e.members.len());
        let size_b = self.eqc_info.get(&rb).map_or(0, |e| e.members.len());
        let (winner, loser) = if size_a >= size_b { (ra, rb) } else { (rb, ra) };

        // Check for constant conflict before merging.
        let winner_const = self
            .eqc_info
            .get(&winner)
            .and_then(|e| e.constant.as_ref())
            .cloned();
        let loser_const = self
            .eqc_info
            .get(&loser)
            .and_then(|e| e.constant.as_ref())
            .cloned();
        if let (Some(ref wc), Some(ref lc)) = (&winner_const, &loser_const) {
            if wc != lc && self.pending_conflict.is_none() {
                self.pending_conflict = Some((winner, loser));
                self.trail.push(TrailEntry::PendingConflictSet);
            }
        }

        // Save loser's old parent before overwriting (always `loser` itself for
        // a root, but captured explicitly for robustness).
        let old_parent = *self.parent.get(&loser).unwrap_or(&loser);
        self.parent.insert(loser, winner);
        let reasons = explanation.to_vec();
        let old_merge_reason = self.merge_reasons.insert(loser, reasons.clone());

        // Record original merge endpoints for proof-forest explain().
        self.proof_edges.push((a, b, reasons));
        self.proof_edges_version += 1;
        self.trail.push(TrailEntry::ProofEdge);

        // Save the loser's EQC info before removing it, so pop can restore it (F1 fix).
        let saved_loser_info = self.eqc_info.remove(&loser);
        self.eqc_version += 1;
        self.trail.push(TrailEntry::Merge(
            loser,
            old_parent,
            saved_loser_info.clone(),
            old_merge_reason,
        ));

        if let Some(loser_info) = saved_loser_info {
            let winner_info = self.eqc_info.entry(winner).or_default();

            if winner_info.constant.is_none() && loser_info.constant.is_some() {
                winner_info.constant.clone_from(&loser_info.constant);
                self.trail.push(TrailEntry::EqcConstantSet(winner));
            }

            for ct in loser_info.concat_terms {
                winner_info.concat_terms.push(ct);
                self.trail.push(TrailEntry::EqcConcatAdded(winner));
            }

            for m in loser_info.members {
                winner_info.members.push(m);
                self.trail.push(TrailEntry::EqcMemberAdded(winner));
            }

            // Propagate length_term from loser to winner (CVC5: eqNotifyMerge).
            if winner_info.length_term.is_none() && loser_info.length_term.is_some() {
                winner_info.length_term = loser_info.length_term;
                self.trail.push(TrailEntry::EqcLengthSet(winner));
            }
        }

        // Propagate int constant cache from loser to winner (#4061).
        // When merging two EQCs, if the loser has a cached int constant,
        // propagate it to the winner (unless the winner already has one).
        if let Some(loser_val) = self.int_const_cache.remove(&loser) {
            self.trail
                .push(TrailEntry::IntConstCache(loser, Some(loser_val)));
            if !self.int_const_cache.contains_key(&winner) {
                let old_winner = self.int_const_cache.insert(winner, loser_val);
                self.trail
                    .push(TrailEntry::IntConstCache(winner, old_winner));
            }
        }

        winner
    }

    /// Process a literal assertion from the DPLL(T) framework.
    ///
    /// Parses the term structure to determine if it's an equality or
    /// disequality, registers the terms, and updates the union-find.
    ///
    /// Handles both `Sort::String` equalities (merge/disequality on string terms)
    /// and `Sort::Int` equalities on `str.len` terms (merge/disequality on length
    /// terms for `are_lengths_equal`/`are_lengths_disequal` queries).
    pub(crate) fn assert_literal(&mut self, terms: &TermStore, literal: TermId, value: bool) {
        let (atom, positive) = match terms.get(literal) {
            TermData::Not(inner) => (*inner, !value),
            _ => (literal, value),
        };

        let lit = TheoryLit::new(literal, value);
        self.assertions.push(lit);
        self.trail.push(TrailEntry::Assertion);

        if let TermData::App(sym, args) = terms.get(atom) {
            if sym.name() == "=" && args.len() == 2 {
                let lhs = args[0];
                let rhs = args[1];
                let sort = terms.sort(lhs).clone();

                if sort == Sort::String {
                    self.register_term(terms, lhs);
                    self.register_term(terms, rhs);

                    if positive {
                        let _ = self.merge(lhs, rhs, lit);
                    } else {
                        // Store original terms, not representatives (#3875).
                        // Using find(lhs)/find(rhs) here loses the proof-forest
                        // path between the original equality arguments. When a
                        // DisequalityViolation fires later (find(t1)==find(t2)),
                        // build_deq_explanation(t1,t2) needs explain(t1,t2) to
                        // traverse the full proof path. If t1/t2 are already
                        // resolved to representatives, explain may skip
                        // intermediate merges, producing an incomplete
                        // explanation → overly-strong blocking clause → false
                        // UNSAT.
                        self.disequalities.push((lhs, rhs, lit));
                        self.trail.push(TrailEntry::Disequality);
                    }
                } else if sort == Sort::Int
                    && (Self::is_str_len(terms, lhs) || Self::is_str_len(terms, rhs))
                {
                    // Track str.len equalities/disequalities in the union-find.
                    // This enables both len(x) = len(y) and len(x) = k facts to
                    // drive `are_lengths_equal`, `are_lengths_disequal`, and
                    // `known_length_full`.
                    //
                    // Bug #3375 fix: use register_term (not ensure_registered) so
                    // that the str.len(x) → x length_term link is established in
                    // the EQC info. Without this link, are_lengths_equal cannot
                    // detect that the SAT solver decided len(x) = len(y), causing
                    // the same LengthSplit to be re-emitted indefinitely.
                    self.register_term(terms, lhs);
                    self.register_term(terms, rhs);
                    // Populate int constant cache for O(1) resolve_int_constant (#4061).
                    self.maybe_cache_int_constant(terms, lhs);
                    self.maybe_cache_int_constant(terms, rhs);

                    if positive {
                        let _ = self.merge(lhs, rhs, lit);
                    } else {
                        // Store original terms (#3875), same as String path.
                        self.disequalities.push((lhs, rhs, lit));
                        self.trail.push(TrailEntry::Disequality);
                    }
                }
            }
        }
    }

    /// Check if a term is a `str.len(...)` application.
    fn is_str_len(terms: &TermStore, t: TermId) -> bool {
        matches!(terms.get(t), TermData::App(sym, args) if sym.name() == "str.len" && args.len() == 1)
    }
}

mod accessors;

#[cfg(test)]
#[path = "state_tests.rs"]
mod tests;
