// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query, explanation, length analysis, and scope management for string solver state.
//!
//! Explanation via proof-forest BFS, equivalence class queries,
//! length equality/disequality checks, push/pop/reset, and string
//! helper predicates. Core mutation (merge, assert, register) is in `state`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::safe_eprintln;
use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::TheoryLit;

use crate::arith_entail::ArithEntail;
use crate::state::{SolverState, TrailEntry};

impl SolverState {
    /// Rebuild the cached adjacency map if `proof_edges` has changed.
    fn ensure_adj_cache(&self) {
        let mut cache = self.cached_adj.borrow_mut();
        if cache.0 == self.proof_edges_version {
            return;
        }
        cache.1.clear();
        for (idx, (x, y, _)) in self.proof_edges.iter().enumerate() {
            cache.1.entry(*x).or_default().push((*y, idx));
            cache.1.entry(*y).or_default().push((*x, idx));
        }
        cache.0 = self.proof_edges_version;
    }

    /// Explain why two terms are in the same EQC by BFS over the proof forest.
    ///
    /// Returns the merge reasons on the path between `a` and `b`.
    /// Returns empty when `a` and `b` are not in the same EQC.
    ///
    /// The proof forest is an undirected graph where each merge(x, y, reasons)
    /// adds an edge x--y with labels `reasons`. explain(a, b) finds the shortest
    /// path from a to b in this graph and collects all edge labels.
    pub(crate) fn explain(&self, a: TermId, b: TermId) -> Vec<TheoryLit> {
        if a == b {
            return Vec::new();
        }

        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            // Terms in different EQCs — no proof path exists.
            // Return empty and let callers defer/skip the inference.
            // Previously returned `assertions().clone()` but this
            // over-approximation creates blocking clauses that are too strong,
            // causing false UNSAT in CEGAR loops (#3826).
            return Vec::new();
        }

        // Ensure the cached adjacency map is up-to-date.
        self.ensure_adj_cache();
        let cache = self.cached_adj.borrow();
        let adj = &cache.1;

        // BFS from a to b using parent pointers (no path cloning).
        // Store (parent_node, proof_edge_index) for path reconstruction.
        let mut parent: HashMap<TermId, (TermId, usize)> = HashMap::default();
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(a);
        parent.insert(a, (a, usize::MAX)); // sentinel for start node

        let found = loop {
            let Some(node) = queue.pop_front() else {
                break false;
            };
            if node == b {
                break true;
            }
            if let Some(neighbors) = adj.get(&node) {
                for &(next, edge_idx) in neighbors {
                    if !parent.contains_key(&next) {
                        parent.insert(next, (node, edge_idx));
                        queue.push_back(next);
                    }
                }
            }
        };

        if found {
            // Reconstruct path: walk parent pointers from b to a,
            // collecting edge reasons with O(1) dedup via HashSet.
            let mut result = Vec::new();
            let mut seen = HashSet::default();
            let mut cur = b;
            while cur != a {
                let &(prev, edge_idx) = parent
                    .get(&cur)
                    .expect("invariant: BFS parent exists for all reachable nodes");
                for reason in &self.proof_edges[edge_idx].2 {
                    if seen.insert(*reason) {
                        result.push(*reason);
                    }
                }
                cur = prev;
            }
            return result;
        }

        // BFS didn't find path (shouldn't happen if find(a)==find(b)).
        // Production soundness gate (#8454): log for diagnostics and return
        // empty rather than the over-approximate assertions fallback.
        safe_eprintln!(
            "BUG: strings explain({a:?}, {b:?}): BFS failed despite same EQC (rep {ra:?})"
        );
        Vec::new()
    }

    /// Legacy wrapper for [`explain`].
    ///
    /// **IMPORTANT (#3826):** The `assertions().clone()` fallback was the root
    /// cause of false UNSAT. When all assertions are original-formula atoms
    /// forced true by unit propagation, a blocking clause negating ALL of them
    /// is unsatisfiable under the original formula — equivalent to an empty
    /// clause. This turns every missed explanation into unconditional UNSAT.
    ///
    /// Now returns empty when explain() returns empty. Callers must handle
    /// the empty case by returning Incomplete or skipping the inference.
    pub(crate) fn explain_or_all(&self, a: TermId, b: TermId) -> Vec<TheoryLit> {
        self.explain(a, b)
    }

    /// Return all equivalence class representatives in deterministic
    /// (sorted by TermId) order. This prevents non-reproducible solver
    /// behavior across runs.
    ///
    /// The sorted list is cached and rebuilt lazily when the EQC key set
    /// changes (via `eqc_version`). Called 10+ times per `check()` cycle;
    /// caching avoids redundant collect+sort on each call. Returns a
    /// cloned `Vec` (TermId is Copy/4 bytes, typically <100 elements).
    pub(crate) fn eqc_representatives(&self) -> Vec<TermId> {
        let mut cache = self.cached_reps.borrow_mut();
        if cache.0 != self.eqc_version {
            cache.1.clear();
            cache.1.extend(self.eqc_info.keys().copied());
            cache.1.sort();
            cache.0 = self.eqc_version;
        }
        cache.1.clone()
    }

    /// Get the length term for an EQC representative.
    ///
    /// Returns `Some(len_term)` if a `str.len(x)` application has been
    /// registered where `x` is in this EQC.
    pub(crate) fn get_length_term(&self, rep: &TermId) -> Option<TermId> {
        self.eqc_info.get(rep).and_then(|e| e.length_term)
    }

    /// Check if two string terms have equal lengths according to EQC metadata.
    ///
    /// Returns `true` if:
    /// 1. Both are in the same EQC (trivially equal length).
    /// 2. Both EQCs have known constant values with equal char counts.
    /// 3. Both have registered length terms that share the same parent
    ///    in the union-find (integer equality propagated from DPLL layer).
    ///
    /// This is the key predicate for Case 3b (N_UNIFY): when two NF components
    /// have equal-length representatives but are not themselves equal, we can
    /// infer their equality.
    ///
    /// CVC5 reference: `areEqual(len(x), len(y))` in `core_solver.cpp:1331`.
    pub(crate) fn are_lengths_equal(&self, terms: &TermStore, a: TermId, b: TermId) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return true;
        }

        // Check via known constant lengths.
        let len_a = self.known_length(terms, ra);
        let len_b = self.known_length(terms, rb);
        if let (Some(la), Some(lb)) = (len_a, len_b) {
            return la == lb;
        }

        // Check via length term EQC (if the DPLL layer propagated length equalities).
        let lt_a = self.get_length_term(&ra);
        let lt_b = self.get_length_term(&rb);
        if let (Some(len_term_a), Some(len_term_b)) = (lt_a, lt_b) {
            return self.find(len_term_a) == self.find(len_term_b);
        }

        false
    }

    /// Check if two string terms have provably *different* lengths.
    ///
    /// Returns `true` if:
    /// 1. Both EQCs have known constant values with different char counts.
    /// 2. Both have registered length terms that are in a recorded disequality.
    ///
    /// This is the key predicate for Case 9 (VarSplit): when two NF variable
    /// components have disequal lengths, we can emit `(x = y ++ k) OR (y = x ++ k)`
    /// instead of re-emitting a redundant LengthSplit.
    ///
    /// CVC5 reference: `areDisequal(len(x), len(y))` in `core_solver.cpp:1640`.
    pub(crate) fn are_lengths_disequal(&self, terms: &TermStore, a: TermId, b: TermId) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }

        // Check 1: known constant lengths that differ.
        let len_a = self.known_length(terms, ra);
        let len_b = self.known_length(terms, rb);
        if let (Some(la), Some(lb)) = (len_a, len_b) {
            return la != lb;
        }

        // Check 2: length terms with a recorded disequality.
        let lt_a = self.get_length_term(&ra);
        let lt_b = self.get_length_term(&rb);
        if let (Some(len_term_a), Some(len_term_b)) = (lt_a, lt_b) {
            let lr_a = self.find(len_term_a);
            let lr_b = self.find(len_term_b);
            for &(r1, r2, _) in &self.disequalities {
                let cr1 = self.find(r1);
                let cr2 = self.find(r2);
                if (cr1 == lr_a && cr2 == lr_b) || (cr2 == lr_a && cr1 == lr_b) {
                    return true;
                }
            }
        }

        false
    }

    /// Check if a string term is known to be non-empty.
    ///
    /// Returns `true` if any of these hold:
    /// 1. The term's EQC has a constant value with length > 0.
    /// 2. The term has a disequality with the empty string (`x != ""`).
    ///
    /// CVC5 reference: `core_solver.cpp:1440-1480` (`explainNonEmpty`).
    pub(crate) fn is_known_nonempty(&self, terms: &TermStore, t: TermId) -> bool {
        let rep = self.find(t);
        // Soundness guard (#4094): a term in the empty-string EQC cannot be
        // non-empty. Without this, stale disequalities (where both sides have
        // been merged into the empty EQC) make Check 3 report empty terms as
        // non-empty, causing false cycle conflicts in check_cycles.
        if self.is_empty_string(terms, t) {
            return false;
        }
        // Check 1: EQC has a non-empty constant.
        if self.known_length(terms, rep).is_some_and(|n| n > 0) {
            return true;
        }
        // Check 2: Length term merged with a positive integer constant.
        // After N-O propagation, str.len(x) may be merged with a concrete
        // integer (e.g., 1). If that integer is positive, x is nonempty.
        if let Some(len_term) = self.get_length_term(&rep) {
            if let Some(n) = self.resolve_int_constant(terms, len_term) {
                if n > 0 {
                    return true;
                }
            }
        }
        // Check 3: arithmetic lower bound certifies positive length.
        //
        // This is stronger than direct length-term constant resolution:
        // ArithEntail can infer non-emptiness for structured terms like
        // str.++(x, "a") where len >= 1 is entailed without a concrete
        // integer assignment for str.len.
        let arith = ArithEntail::new(terms, self);
        if arith.get_length_bound(rep, true).is_some_and(|lb| lb >= 1) {
            return true;
        }

        // Check 4: disequality with the empty string.
        if let Some(empty_id) = self.empty_string_id {
            let empty_rep = self.find(empty_id);
            for &(r1, r2, _) in &self.disequalities {
                let cr1 = self.find(r1);
                let cr2 = self.find(r2);
                // Skip stale disequalities where both sides have been merged
                // into the same EQC (pending conflict in EQC machinery).
                if cr1 == cr2 {
                    continue;
                }
                if (cr1 == rep && cr2 == empty_rep) || (cr2 == rep && cr1 == empty_rep) {
                    return true;
                }
            }
        }
        false
    }

    /// Get the known character length of a string EQC.
    ///
    /// Returns `Some(n)` if the EQC has a constant value with `n` characters.
    pub(crate) fn known_length(&self, terms: &TermStore, rep: TermId) -> Option<usize> {
        if let Some(s) = self.eqc_info.get(&rep).and_then(|e| e.constant.as_deref()) {
            return Some(s.chars().count());
        }
        match terms.get(rep) {
            TermData::Const(Constant::String(s)) => Some(s.chars().count()),
            _ => None,
        }
    }

    /// Get the known length of a string term, considering both EQC constants
    /// and N-O bridge propagation (str.len(x) merged with an integer constant).
    ///
    /// Unlike `known_length` which only checks EQC string constants, this also
    /// checks if the length term has been merged with a concrete integer via
    /// the N-O bridge. Returns `None` if the length is unknown.
    pub(crate) fn known_length_full(&self, terms: &TermStore, t: TermId) -> Option<usize> {
        let rep = self.find(t);
        // Check 1: EQC has a constant string value.
        if let Some(n) = self.known_length(terms, rep) {
            return Some(n);
        }
        // Check 2: N-O bridge — str.len(t) merged with a concrete integer.
        if let Some(len_term) = self.get_length_term(&rep) {
            if let Some(n) = self.resolve_int_constant(terms, len_term) {
                if n >= 0 {
                    return Some(n as usize);
                }
            }
        }
        None
    }

    /// Resolve an integer term to a concrete non-negative value via the EQC.
    ///
    /// If `t` (or its representative) is a concrete integer constant,
    /// return its value as `i64`. Used by `is_known_nonempty` to detect
    /// length terms merged with positive integer constants via N-O
    /// propagation (e.g., `str.len(x)` merged with `1`).
    ///
    /// O(1) via `int_const_cache` (#4061). Previously scanned all parent
    /// keys in O(N).
    pub(crate) fn resolve_int_constant(&self, terms: &TermStore, t: TermId) -> Option<i64> {
        self.resolve_int_constant_with_term(terms, t)
            .map(|(v, _)| v)
    }

    /// Like [`Self::resolve_int_constant`], but also returns the `TermId` of
    /// the concrete integer constant that justifies the value. Used by
    /// NF-engine closure 2 to explain length-driven inferences through the
    /// proof forest (`explain(len_term, const_tid)`).
    pub(crate) fn resolve_int_constant_with_term(
        &self,
        terms: &TermStore,
        t: TermId,
    ) -> Option<(i64, TermId)> {
        // Fast path 1: direct syntactic check on term itself.
        if let TermData::Const(Constant::Int(n)) = terms.get(t) {
            return n.try_into().ok().map(|v: i64| (v, t));
        }
        // Fast path 2: direct syntactic check on representative.
        let rep = self.find(t);
        if let TermData::Const(Constant::Int(n)) = terms.get(rep) {
            return n.try_into().ok().map(|v: i64| (v, rep));
        }
        // O(1) cache lookup: covers the case where an int constant was
        // merged into the EQC via assert_literal.
        self.int_const_cache.get(&rep).copied()
    }

    /// Push a new scope for backtracking.
    pub(crate) fn push(&mut self) {
        self.scope_stack.push(self.trail.len());
    }

    /// Pop to the previous scope, undoing all changes since the last push.
    pub(crate) fn pop(&mut self) {
        let target = match self.scope_stack.pop() {
            Some(n) => n,
            None => return,
        };

        // Production soundness gate (#8454): if scope target exceeds trail
        // length, the string solver state is corrupted. Clamp to prevent
        // further damage and poison the solver so next check() returns Unknown.
        let target = if target > self.trail.len() {
            safe_eprintln!(
                "BUG: strings pop: scope target {} exceeds trail length {} — clamping and poisoning solver",
                target,
                self.trail.len()
            );
            self.poisoned = true;
            self.trail.len()
        } else {
            target
        };

        while self.trail.len() > target {
            // SAFETY: while-loop guard guarantees trail is non-empty.
            let entry = self
                .trail
                .pop()
                .expect("invariant: trail.len() > target guarantees non-empty trail");
            match entry {
                TrailEntry::Assertion => {
                    self.assertions.pop();
                }
                TrailEntry::Disequality => {
                    self.disequalities.pop();
                }
                TrailEntry::Merge(child, old_parent, saved_loser_info, old_merge_reason) => {
                    self.parent.insert(child, old_parent);
                    // Restore loser's EQC info if it was saved (F1 fix).
                    if let Some(info) = saved_loser_info {
                        self.eqc_info.insert(child, info);
                        self.eqc_version += 1;
                    }
                    // Restore merge reason (or remove if none existed before).
                    match old_merge_reason {
                        Some(reason) => {
                            self.merge_reasons.insert(child, reason);
                        }
                        None => {
                            self.merge_reasons.remove(&child);
                        }
                    }
                }
                TrailEntry::EqcCreated(t) => {
                    self.eqc_info.remove(&t);
                    self.eqc_version += 1;
                    // Also remove parent entry so register_term can re-register
                    // this term after pop (R237 Finding 2).
                    self.parent.remove(&t);
                }
                TrailEntry::EqcConstantSet(t) => {
                    if let Some(eqc) = self.eqc_info.get_mut(&t) {
                        eqc.constant = None;
                    }
                }
                TrailEntry::EqcConcatAdded(t) => {
                    if let Some(eqc) = self.eqc_info.get_mut(&t) {
                        eqc.concat_terms.pop();
                    }
                }
                TrailEntry::EqcMemberAdded(t) => {
                    if let Some(eqc) = self.eqc_info.get_mut(&t) {
                        eqc.members.pop();
                    }
                }
                TrailEntry::EqcLengthSet(t) => {
                    if let Some(eqc) = self.eqc_info.get_mut(&t) {
                        eqc.length_term = None;
                    }
                }
                TrailEntry::PendingConflictSet => {
                    self.pending_conflict = None;
                }
                TrailEntry::ProofEdge => {
                    self.proof_edges.pop();
                    self.proof_edges_version += 1;
                }
                TrailEntry::IntConstCache(rep, old_val) => match old_val {
                    Some(val) => {
                        self.int_const_cache.insert(rep, val);
                    }
                    None => {
                        self.int_const_cache.remove(&rep);
                    }
                },
            }
        }
    }

    /// Reset all state.
    pub(crate) fn reset(&mut self) {
        self.assertions.clear();
        self.parent.clear();
        self.eqc_info.clear();
        self.disequalities.clear();
        self.pending_conflict = None;
        self.trail.clear();
        self.scope_stack.clear();
        self.merge_reasons.clear();
        self.proof_edges.clear();
        self.proof_edges_version += 1;
        self.eqc_version += 1;
        self.empty_string_id = None;
        self.cached_adj.borrow_mut().1.clear();
        self.cached_reps.borrow_mut().1.clear();
        self.int_const_cache.clear();
        self.poisoned = false;
    }

    /// Get the children of a concat term from the TermStore.
    pub(crate) fn get_concat_children<'a>(
        &self,
        terms: &'a TermStore,
        t: TermId,
    ) -> Option<&'a [TermId]> {
        match terms.get(t) {
            TermData::App(sym, args) if sym.name() == "str.++" => Some(args),
            _ => None,
        }
    }

    /// Get the cached TermId for the empty string `""`, if registered.
    pub(crate) fn empty_string_id(&self) -> Option<TermId> {
        self.empty_string_id
    }

    /// Check if a term is equivalent to the empty string.
    ///
    /// Returns true if:
    /// 1. The term is syntactically the empty string constant `""`, OR
    /// 2. The term's EQC representative has a constant value of `""`.
    ///
    /// This EQC-aware check is critical for cycle detection (F2): when
    /// `y = ""` is asserted, `is_empty_string(y)` must return true even
    /// though `y` is a variable, not a constant.
    pub(crate) fn is_empty_string(&self, terms: &TermStore, t: TermId) -> bool {
        // Fast path: syntactic check.
        if matches!(terms.get(t), TermData::Const(Constant::String(s)) if s.is_empty()) {
            return true;
        }
        if let Some(empty_id) = self.empty_string_id {
            if self.find(t) == self.find(empty_id) {
                return true;
            }
        }
        // Slow path: check EQC constant.
        let rep = self.find(t);
        self.eqc_info
            .get(&rep)
            .and_then(|info| info.constant.as_deref())
            .is_some_and(str::is_empty)
    }

    /// Find the TermId of the actual string constant within an EQC.
    ///
    /// When a variable or concat term is merged with a string constant, the
    /// EQC representative may not be the constant term itself. This method
    /// searches the EQC members to find the TermId that IS the string constant.
    ///
    /// Returns `None` if the EQC has no constant.
    pub(crate) fn find_constant_term_id(&self, terms: &TermStore, t: TermId) -> Option<TermId> {
        let rep = self.find(t);
        self.find_constant_term_id_for_rep(terms, &rep)
    }
}
