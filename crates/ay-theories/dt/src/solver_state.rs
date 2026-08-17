// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver construction, registration, union-find state, and equality explanation.

use std::collections::VecDeque;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData, TermId, TermStore};

use super::{ConstructorInfo, DtModel, DtScope, DtSolver};

impl<'a> DtSolver<'a> {
    /// Create a new DT solver with access to the term store
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        DtSolver {
            terms,
            term_constructors: HashMap::default(),
            parent: HashMap::default(),
            union_trail: Vec::new(),
            pending: Vec::new(),
            scopes: Vec::new(),
            current_scope: DtScope::default(),
            datatype_defs: HashMap::default(),
            ctor_to_dt: HashMap::default(),
            tester_map: HashMap::default(),
            ctor_selectors: HashMap::default(),
            tester_results: HashMap::default(),
            asserted_eq_lits: Vec::new(),
            pending_injectivity_eqs: Vec::new(),
            propagated_eq_pairs: HashSet::default(),
            asserted_diseqs: Vec::new(),
            merge_reasons: Vec::new(),
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            split_count: 0,
            debug: ay_core::debug_channel_active(ay_core::DebugChannel::Dt),
            internalized_testers: HashMap::default(),
            asserted_tester_atoms: HashSet::default(),
            dt_terms: HashMap::default(),
            pending_split_atom: None,
            buf_sorted_ctor_keys: Vec::new(),
            buf_class_groups: HashMap::default(),
            buf_sorted_reps: Vec::new(),
            buf_oc_color: HashMap::default(),
            buf_oc_parent_edge: HashMap::default(),
            buf_oc_rep_to_args: HashMap::default(),
            buf_oc_stack: Vec::new(),
            buf_explain_adj: HashMap::default(),
            buf_explain_visited: HashSet::default(),
            buf_explain_queue: VecDeque::new(),
            buf_unconstrained: Vec::new(),
            buf_oc_tester_edges: HashMap::default(),
        }
    }

    /// Register a datatype definition.
    ///
    /// This is called when `declare-datatype` is processed.
    pub fn register_datatype(&mut self, dt_name: &str, constructors: &[String]) {
        self.datatype_defs
            .insert(dt_name.to_string(), constructors.to_vec());
        for ctor in constructors {
            let tester_name = format!("is-{ctor}");
            self.tester_map
                .insert(tester_name, (dt_name.to_string(), ctor.clone()));
            // Track constructor -> datatype mapping
            self.ctor_to_dt.insert(ctor.clone(), dt_name.to_string());
        }
    }

    /// Register the ordered selector (field-accessor) names for a constructor.
    ///
    /// Used by the acyclicity occurs-check to expand a true tester `is-C(v)` into
    /// the implicit recursive structure `v = C(sel_1(v), ..., sel_n(v))` using the
    /// *existing* selector-application terms in the store (no term is created). See
    /// `occurs_check` for how these edges are added.
    pub fn register_ctor_selectors(&mut self, ctor_name: &str, selectors: &[String]) {
        self.ctor_selectors
            .insert(ctor_name.to_string(), selectors.to_vec());
    }

    /// Get the datatype name for a constructor
    fn get_datatype_for_ctor(&self, name: &str) -> Option<&str> {
        self.ctor_to_dt.get(name).map(String::as_str)
    }

    /// Export the final e-graph state as a [`DtModel`] (#mv-dt-single-source).
    ///
    /// Called from the DPLL(T) pipeline's `extract_models` hook exactly when the
    /// theory reported `Sat`, i.e. the snapshot is the committed structure of the
    /// accepted model. Read-only; deterministic (all iterations are over
    /// TermId-sorted keys, and per-class winners are the smallest TermId).
    #[must_use]
    pub fn export_model(&self) -> DtModel {
        let mut model = DtModel::default();

        // Every term the solver tracked, TermId-sorted for determinism.
        let mut keys: Vec<TermId> = self.parent.keys().copied().collect();
        keys.extend(self.term_constructors.keys().copied());
        keys.extend(self.tester_results.keys().copied());
        keys.extend(self.dt_terms.keys().copied());
        for &(lhs, rhs, _) in &self.asserted_diseqs {
            keys.push(lhs);
            keys.push(rhs);
        }
        keys.sort_by_key(|t| t.0);
        keys.dedup();
        for term in keys {
            model.rep_of.insert(term, self.find(term));
        }

        // Constructor application per class: smallest TermId wins. At Sat all
        // applications in one class share a constructor (clash check), so the
        // choice only affects WHICH argument terms supply the field values —
        // and same-constructor applications in one class have pairwise-merged
        // arguments (injectivity), so any choice is value-equivalent.
        let mut ctor_terms: Vec<TermId> = self.term_constructors.keys().copied().collect();
        ctor_terms.sort_by_key(|t| t.0);
        for term in ctor_terms {
            let info = &self.term_constructors[&term];
            let rep = self.find(term);
            model
                .ctor_app_of
                .entry(rep)
                .or_insert_with(|| (info.ctor_name.clone(), info.args.clone()));
        }

        // Tester commitments per class.
        let mut tester_args: Vec<TermId> = self.tester_results.keys().copied().collect();
        tester_args.sort_by_key(|t| t.0);
        for arg in tester_args {
            let (ctor, value, _lit) = &self.tester_results[&arg];
            let rep = self.find(arg);
            if *value {
                model
                    .pos_tester_of
                    .entry(rep)
                    .or_insert_with(|| ctor.clone());
            } else {
                let ruled_out = model.neg_testers_of.entry(rep).or_default();
                if !ruled_out.contains(ctor) {
                    ruled_out.push(ctor.clone());
                }
            }
        }

        model.diseqs = self
            .asserted_diseqs
            .iter()
            .map(|&(lhs, rhs, _)| (lhs, rhs))
            .collect();
        model
    }

    /// Try to extract constructor info from a term
    pub(super) fn try_extract_constructor(
        &self,
        term_id: TermId,
    ) -> Option<(String, String, Vec<TermId>)> {
        match self.terms.get(term_id) {
            TermData::App(Symbol::Named(name), args) => {
                if let Some(dt_name) = self.get_datatype_for_ctor(name) {
                    return Some((dt_name.to_string(), name.clone(), args.clone()));
                }
                None
            }
            TermData::Var(name, _) => {
                // Nullary constructors are stored as variables
                if let Some(dt_name) = self.get_datatype_for_ctor(name) {
                    return Some((dt_name.to_string(), name.clone(), vec![]));
                }
                None
            }
            _ => None,
        }
    }

    /// Process an equality, potentially involving constructor terms
    pub(super) fn process_equality(
        &mut self,
        eq_term: TermId,
        lhs: TermId,
        rhs: TermId,
        positive: bool,
    ) {
        // Register any constructor applications on either side, regardless of
        // polarity. Constructors inside a *disequality* (e.g. `succ(a) != succ(zero)`)
        // must be registered so upward congruence can fire on them (#dt-congruence).
        for &side in &[lhs, rhs] {
            if let Some((dt_name, ctor_name, args)) = self.try_extract_constructor(side) {
                if !self.term_constructors.contains_key(&side) {
                    self.register_constructor(side, &dt_name, &ctor_name, &args);
                }
            }
        }

        if !positive {
            // Track disequalities for injectivity-conflict checking.
            self.asserted_diseqs.push((lhs, rhs, eq_term));
            self.current_scope.asserted_diseqs_len = self
                .current_scope
                .asserted_diseqs_len
                .max(self.asserted_diseqs.len());
            return;
        }

        // Track the equality literal for conflict explanation
        self.asserted_eq_lits.push(eq_term);

        // Union the terms with reason tracking (#5108)
        self.union_with_reason(lhs, rhs, eq_term);
    }

    /// Decode a NOT wrapper: `(not inner)` → Some(inner)
    pub(super) fn decode_not(&self, term: TermId) -> Option<TermId> {
        match self.terms.get(term) {
            TermData::Not(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Decode an equality: `(= lhs rhs)` → Some((lhs, rhs))
    pub(super) fn decode_eq(&self, term: TermId) -> Option<(TermId, TermId)> {
        match self.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Register a constructor application for a term
    pub fn register_constructor(
        &mut self,
        term_id: TermId,
        _dt_name: &str,
        ctor_name: &str,
        args: &[TermId],
    ) {
        let dt_name = self
            .get_datatype_for_ctor(ctor_name)
            .unwrap_or(_dt_name)
            .to_string();
        self.term_constructors.insert(
            term_id,
            ConstructorInfo {
                dt_name,
                ctor_name: ctor_name.to_string(),
                args: args.to_vec(),
            },
        );
        self.current_scope.registered_ctors.push(term_id);
        // Ensure term is in union-find
        self.parent.entry(term_id).or_insert(term_id);

        // Recursively register NESTED constructor arguments so the acyclicity
        // occurs-check sees the full constructor-term DAG (#dt-acyclic-nested).
        // Otherwise the inner `succ(v)` of `succ(succ(v))` (registered only as a
        // sub-term of the top-level constructor) is missing from term_constructors,
        // its cycle edge `succ(v) ⊳ v` is never added, and a self-cycle like
        // `v = succ(succ(v))` is reported SAT instead of UNSAT. Sound: every added
        // term is a genuine constructor application whose args are real structural
        // children, so the occurs-check can only find a REAL well-foundedness
        // cycle — never a spurious one. Bounded by term depth; the `contains_key`
        // guard prevents re-registration and terminates the recursion.
        let nested: Vec<TermId> = args.to_vec();
        for arg in nested {
            if self.term_constructors.contains_key(&arg) {
                continue;
            }
            // Guard: only inspect args that are real interned terms. The combined
            // solver always passes valid TermIds, but direct DtSolver unit tests
            // register constructors with synthetic out-of-store arg ids, so a
            // bounds check keeps `try_extract_constructor` (which reads the store)
            // from panicking.
            if (arg.0 as usize) >= self.terms.len() {
                continue;
            }
            if let Some((dt, ctor, arg_args)) = self.try_extract_constructor(arg) {
                self.register_constructor(arg, &dt, &ctor, &arg_args);
            }
        }
    }

    /// Assert an equality between two terms
    pub fn assert_equality(&mut self, a: TermId, b: TermId) {
        self.union(a, b);
    }

    /// Find the representative of a term in the union-find.
    ///
    /// No path compression: mutations must be undoable on pop().
    /// DT equivalence classes are small enough that O(depth) traversal is fine.
    pub(super) fn find(&self, term: TermId) -> TermId {
        let mut curr = term;
        loop {
            let parent = *self.parent.get(&curr).unwrap_or(&curr);
            if parent == curr {
                return curr;
            }
            curr = parent;
        }
    }

    /// Union two terms in the union-find.
    ///
    /// Records `ra` on the union trail for efficient pop (#8627).
    pub(super) fn union(&mut self, a: TermId, b: TermId) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.union_trail.push(ra);
            self.parent.insert(ra, rb);
        }
    }

    /// Union two terms in the union-find with reason tracking (#5108).
    ///
    /// Records the original terms (before find()) and the equality literal
    /// that caused this merge. This builds a reason graph that can be
    /// traversed by BFS to produce minimal conflict explanations.
    /// Also records `ra` on the union trail for efficient pop (#8627).
    fn union_with_reason(&mut self, a: TermId, b: TermId, reason: TermId) {
        self.union_with_reasons(a, b, vec![reason]);
    }

    /// Union two terms in the union-find with a *set* of reason literals.
    ///
    /// Used by upward constructor congruence (`C(a) = C(b)` implied by all
    /// `a_i = b_i`): the merge of the two constructor terms is justified by the
    /// full collection of argument-equality reason literals, so the whole set is
    /// recorded on the reason-graph edge for explanation (#dt-congruence).
    pub(super) fn union_with_reasons(&mut self, a: TermId, b: TermId, reasons: Vec<TermId>) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.union_trail.push(ra);
            self.parent.insert(ra, rb);
            // Record the original terms for the reason graph, not the
            // representatives. This is essential because representatives
            // change as more unions are performed (#5108).
            self.merge_reasons.push((a, b, reasons));
        }
    }

    /// Explain why two terms are in the same equivalence class (#5108).
    ///
    /// Uses BFS on the reason graph (merge_reasons) to find a path from
    /// `a` to `b` and collects the equality literals along that path.
    /// This produces a minimal(ish) conflict explanation instead of
    /// returning ALL asserted equality literals.
    ///
    /// Uses `buf_explain_adj`, `buf_explain_visited`, `buf_explain_queue` as
    /// persistent buffers to avoid per-call allocation (#8599).
    pub(super) fn explain_equality(&mut self, a: TermId, b: TermId) -> Vec<TermId> {
        // Build adjacency list from merge_reasons (undirected graph)
        // using persistent buffer. Each edge carries a *set* of reason literals
        // (one for ordinary equality merges, several for congruence merges).
        self.buf_explain_adj.clear();
        for (lhs, rhs, reasons) in &self.merge_reasons {
            let (lhs, rhs, reasons) = (*lhs, *rhs, reasons.clone());
            self.buf_explain_adj
                .entry(lhs)
                .or_default()
                .push((rhs, reasons.clone()));
            self.buf_explain_adj
                .entry(rhs)
                .or_default()
                .push((lhs, reasons));
        }

        // BFS from `a` to `b` in the reason graph using persistent buffers.
        self.buf_explain_visited.clear();
        self.buf_explain_queue.clear();
        self.buf_explain_visited.insert(a);
        self.buf_explain_queue.push_back((a, Vec::new()));

        while let Some((curr, reasons)) = self.buf_explain_queue.pop_front() {
            if self.find(curr) == self.find(b) && curr == b {
                return reasons;
            }

            if let Some(neighbors) = self.buf_explain_adj.get(&curr) {
                let neighbors: Vec<(TermId, Vec<TermId>)> = neighbors.clone();
                for (neighbor, edge_reasons) in neighbors {
                    if self.buf_explain_visited.insert(neighbor) {
                        let mut new_reasons = reasons.clone();
                        new_reasons.extend(edge_reasons.iter().copied());
                        if neighbor == b {
                            return new_reasons;
                        }
                        self.buf_explain_queue.push_back((neighbor, new_reasons));
                    }
                }
            }
        }

        // If BFS didn't find a path, fall back to all asserted equality literals.
        // This can happen if the terms were merged via assert_equality() (N-O)
        // which doesn't record reasons.
        Vec::new()
    }
}
