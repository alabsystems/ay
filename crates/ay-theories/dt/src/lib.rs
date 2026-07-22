// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY DT - Algebraic Datatypes theory solver
//!
//! Implements reasoning about algebraic datatypes (constructors, selectors, testers).
//!
//! ## Algorithm
//!
//! Based on Barrett, Shikanian, and Tinelli's 2007 algorithm:
//! - **Constructor clash**: C1(a) = C2(b) where C1 != C2 → CONFLICT
//! - **Injectivity**: C(a1, ..., an) = C(b1, ..., bn) → a1 = b1 AND ... AND an = bn
//!
//! ## References
//!
//! - Barrett et al. "An Abstract Decision Procedure for a Theory of Inductive Data Types" (2007)
//! - Z3: reference/z3/src/smt/theory_datatype.cpp (MIT)
//! - Design: the development design notes

#![warn(missing_docs)]
#![warn(clippy::all)]

mod conflicts;
mod d1_propagate;
mod d2_split;
mod egraph_pass;
mod theory_impl;

pub use d1_propagate::DtLazyPropagator;
pub use d2_split::{occurrence_relevant_dt_terms, DtSplitOnDemand};
pub use egraph_pass::{DtEgraphPass, DtPassOutcome};
// `DtModel` (the e-graph model export) is defined below in this module.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::{
    DiscoveredEquality, EqualityPropagationResult, TheoryLit, TheoryPropagation, TheoryResult,
    TheorySolver,
};
use std::collections::VecDeque;

/// Information about a constructor application term.
#[derive(Debug, Clone)]
struct ConstructorInfo {
    /// Name of the datatype (e.g., "Option")
    dt_name: String,
    /// Name of the constructor (e.g., "Some", "None")
    ctor_name: String,
    /// Argument term IDs (parallel to constructor fields)
    args: Vec<TermId>,
}

/// Final-state e-graph model exported by the DT theory at a `Sat` verdict
/// (#mv-dt-single-source).
///
/// A read-only snapshot of the solver's committed structure at the moment the
/// DPLL(T) loop accepted the assignment: the union-find classes, the per-class
/// constructor commitments (registered constructor applications and asserted
/// tester results), and the asserted disequalities. The executor's model
/// printer derives ONE value assignment per class from this export, so that
/// `(get-model)`, `(get-value)` and the total selector definitions all read
/// the same values — the previous print-time per-term re-derivation fabricated
/// values for constrained selector chains (M3 root cause / M4 F1).
///
/// All maps are keyed by TermId only (no term-store borrow), so the export
/// outlives the solver.
#[derive(Debug, Clone, Default)]
pub struct DtModel {
    /// Term -> fully-resolved class representative, for every term the solver
    /// tracked (union-find nodes, constructor applications, tester arguments,
    /// internalized DT terms, disequality endpoints). Terms absent from this
    /// map were never constrained by the theory (their class is themselves).
    pub rep_of: HashMap<TermId, TermId>,
    /// Class representative -> (constructor name, argument term ids) for every
    /// class containing a registered constructor application. Deterministic:
    /// the smallest constructor-application TermId in the class wins (at Sat
    /// all constructor applications of one class carry the same constructor,
    /// or the clash check would have fired).
    pub ctor_app_of: HashMap<TermId, (String, Vec<TermId>)>,
    /// Class representative -> constructor name committed by a POSITIVE
    /// tester assignment (`is-C(t)` asserted true for a `t` in the class).
    pub pos_tester_of: HashMap<TermId, String>,
    /// Class representative -> constructor names ruled OUT by NEGATIVE tester
    /// assignments (`is-C(t)` asserted false for a `t` in the class).
    pub neg_testers_of: HashMap<TermId, Vec<String>>,
    /// Asserted disequalities `(lhs, rhs)`, as asserted (unresolved term ids).
    pub diseqs: Vec<(TermId, TermId)>,
}

impl DtModel {
    /// Fully-resolved class representative of `term` (itself when untracked).
    #[must_use]
    pub fn rep(&self, term: TermId) -> TermId {
        self.rep_of.get(&term).copied().unwrap_or(term)
    }
}

/// An undo record for rolling back mutations on pop().
///
/// Scope state for push/pop support.
#[derive(Debug, Clone, Default)]
struct DtScope {
    /// Constructor registrations added in this scope
    registered_ctors: Vec<TermId>,
    /// Length of `asserted_eq_lits` before this scope (for rollback).
    asserted_eq_lits_len: usize,
    /// Length of `asserted_diseqs` before this scope was pushed.
    asserted_diseqs_len: usize,
    /// Tester result keys added in this scope (for undo on pop).
    tester_keys: Vec<TermId>,
    /// Length of union_trail at push time (#8627).
    /// Used with trail-based undo to restore union-find state on pop.
    union_trail_mark: usize,
    /// Length of merge_reasons at push time (#5108).
    merge_reasons_len: usize,
}

/// Datatype theory solver
///
/// Tracks constructor applications and detects:
/// 1. **Constructor clash**: Two different constructors in the same equivalence class
/// 2. **Injectivity**: Same constructor applications should have equal fields
pub struct DtSolver<'a> {
    /// Reference to the term store for looking up term structure
    terms: &'a TermStore,
    /// Map from term IDs to their constructor info (if they are constructor applications)
    term_constructors: HashMap<TermId, ConstructorInfo>,
    /// Union-find for equivalence classes. Maps term -> representative.
    parent: HashMap<TermId, TermId>,
    /// Trail of union-find merges for efficient push/pop (#8627).
    /// Each entry records the representative whose parent was changed.
    /// On pop, we restore `parent[ra] = ra` to undo the merge.
    union_trail: Vec<TermId>,
    /// Pending propagations (injectivity equalities)
    pending: Vec<TheoryPropagation>,
    /// Scope stack for push/pop
    scopes: Vec<DtScope>,
    /// Current scope
    current_scope: DtScope,
    /// Registered datatype definitions: dt_name -> list of constructor names
    datatype_defs: HashMap<String, Vec<String>>,
    /// Constructor name -> datatype name mapping
    ctor_to_dt: HashMap<String, String>,
    /// Registered tester predicates: is-CtorName -> (dt_name, ctor_name)
    tester_map: HashMap<String, (String, String)>,
    /// Constructor name -> ordered list of its selector (field-accessor) names.
    /// Populated via [`register_ctor_selectors`] so the acyclicity occurs-check
    /// can derive the implicit `v = C(sel_1(v), ...)` edges from a true tester
    /// `is-C(v)` without materializing a constructor term (#dt-acyclic-tester).
    ctor_selectors: HashMap<String, Vec<String>>,
    /// Asserted tester results: arg_term -> (ctor_name, value, tester_literal).
    /// The tester_literal is the original `is-C(arg)` term for conflict explanation.
    tester_results: HashMap<TermId, (String, bool, TermId)>,
    /// Equality literals asserted true (used for conflict explanation).
    asserted_eq_lits: Vec<TermId>,
    /// Pending injectivity equalities to propagate via Nelson-Oppen.
    /// These are discovered when same-constructor terms are in the same equivalence class.
    pending_injectivity_eqs: Vec<DiscoveredEquality>,
    /// Track which (lhs, rhs) pairs we've already propagated to avoid duplicates.
    propagated_eq_pairs: HashSet<(TermId, TermId)>,
    /// Asserted disequalities: (lhs, rhs, reason_lit). Used to detect injectivity conflicts.
    asserted_diseqs: Vec<(TermId, TermId, TermId)>,
    /// Reason graph for equality explanations (#5108).
    /// Each entry `(a, b, reasons)` records that the equality literals `reasons`
    /// caused terms `a` and `b` to be merged. Used to compute minimal conflict
    /// explanations for constructor clashes via BFS on the reason graph.
    ///
    /// Most merges have a single reason literal (an asserted equality). Upward
    /// constructor congruence merges (`C(a) = C(b)` because every `a_i = b_i`)
    /// carry the full set of argument-equality reasons on the edge, so the BFS
    /// explanation collects all of them.
    merge_reasons: Vec<(TermId, TermId, Vec<TermId>)>,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
    split_count: u64,
    /// Cached `AY_DEBUG_DT` / `AY_DEBUG_THEORY` env-var flag (#4706).
    debug: bool,
    /// Internalized tester atoms: tester_term -> (argument_term, ctor_name).
    /// Populated by `internalize_atom()` when the DPLL layer registers tester
    /// atoms. Used by `suggest_decision_atom()` to find unconstrained DT terms
    /// and propose case splits (#8539).
    internalized_testers: HashMap<TermId, (TermId, String)>,
    /// Set of tester atoms that have been asserted (decided or propagated).
    /// Used to determine which tester atoms are still unassigned for case splitting.
    asserted_tester_atoms: HashSet<TermId>,
    /// DT-sorted terms known to the solver (registered via `internalize_atom`).
    /// Maps term -> datatype name.
    dt_terms: HashMap<TermId, String>,
    /// Pending case split: the tester atom the theory wants the SAT solver to
    /// decide next. Set by `check()` when an unconstrained DT variable is found.
    pending_split_atom: Option<(TermId, bool)>,

    // --- Persistent buffers for per-check() temporary data (#8599) ---
    // Avoids heap allocation on every check() call for conflict detection.
    /// Reusable buffer: sorted constructor term keys for clash/injectivity grouping.
    buf_sorted_ctor_keys: Vec<TermId>,
    /// Reusable buffer: class grouping for check_clash / check_injectivity.
    /// Maps equivalence class representative -> list of (term, ctor_name index).
    buf_class_groups: HashMap<TermId, Vec<(TermId, usize)>>,
    /// Reusable buffer: sorted class representatives for deterministic iteration.
    buf_sorted_reps: Vec<TermId>,
    /// Reusable buffer: occurs check DFS color map.
    buf_oc_color: HashMap<TermId, u8>,
    /// Reusable buffer: occurs check parent edge map for cycle reconstruction.
    buf_oc_parent_edge: HashMap<TermId, (TermId, TermId)>,
    /// Reusable buffer: occurs check representative-to-args adjacency.
    buf_oc_rep_to_args: HashMap<TermId, Vec<TermId>>,
    /// Reusable buffer: occurs check DFS stack.
    buf_oc_stack: Vec<(u8, TermId, TermId)>,
    /// Reusable buffer: explain_equality BFS adjacency list.
    /// Each edge carries the set of reason literals that justified the merge.
    buf_explain_adj: HashMap<TermId, Vec<(TermId, Vec<TermId>)>>,
    /// Reusable buffer: explain_equality BFS visited set.
    buf_explain_visited: HashSet<TermId>,
    /// Reusable buffer: explain_equality BFS queue.
    buf_explain_queue: VecDeque<(TermId, Vec<TermId>)>,
    /// Reusable buffer: find_case_split unconstrained terms.
    buf_unconstrained: Vec<(TermId, usize)>,
    /// Reusable buffer: tester-induced occurs-check edges keyed by
    /// `(parent_rep, child_rep)` -> tester literal, so a cycle that traverses an
    /// implicit `is-C(v) ⟹ v = C(.. sel_i(v) ..)` edge includes the tester
    /// literal in its conflict explanation (#dt-acyclic-tester).
    buf_oc_tester_edges: HashMap<(TermId, TermId), TermId>,
}

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
    fn try_extract_constructor(&self, term_id: TermId) -> Option<(String, String, Vec<TermId>)> {
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
    fn process_equality(&mut self, eq_term: TermId, lhs: TermId, rhs: TermId, positive: bool) {
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
    fn decode_not(&self, term: TermId) -> Option<TermId> {
        match self.terms.get(term) {
            TermData::Not(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Decode an equality: `(= lhs rhs)` → Some((lhs, rhs))
    fn decode_eq(&self, term: TermId) -> Option<(TermId, TermId)> {
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
    fn find(&self, term: TermId) -> TermId {
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
    fn union(&mut self, a: TermId, b: TermId) {
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
    fn union_with_reasons(&mut self, a: TermId, b: TermId, reasons: Vec<TermId>) {
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
    fn explain_equality(&mut self, a: TermId, b: TermId) -> Vec<TermId> {
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

    /// Find an unconstrained DT term and suggest a case-split tester atom (#8539).
    ///
    /// Scans DT-sorted terms for equivalence classes that have:
    /// 1. No constructor term in the class
    /// 2. No tester result decided for the term
    ///
    /// For each such term, finds an unassigned tester atom and returns it as the
    /// suggested decision. Prefers the non-recursive constructor (like Z3's
    /// `get_non_rec_constructor`) to avoid infinite unfolding.
    ///
    /// Uses `buf_unconstrained` as persistent buffer (#8599).
    ///
    /// Reference: Z3 `theory_datatype::mk_split()` and `final_check_eh()`.
    fn find_case_split(&mut self) -> Option<(TermId, bool)> {
        // Collect DT terms whose equivalence class has no constructor.
        // Uses persistent buffer to avoid per-call allocation.
        // Stores (term_id, index_into_dt_terms_values) — we look up dt_name later.
        self.buf_unconstrained.clear();
        let dt_term_entries: Vec<(TermId, String)> =
            self.dt_terms.iter().map(|(&t, s)| (t, s.clone())).collect();
        for (term, _dt_name) in &dt_term_entries {
            let rep = self.find(*term);
            let has_ctor = self
                .term_constructors
                .keys()
                .any(|ct| self.find(*ct) == rep);
            if has_ctor {
                continue;
            }
            if self.tester_results.get(term).is_some() {
                continue;
            }
            // Store index into dt_term_entries for later dt_name lookup.
            let idx = dt_term_entries
                .iter()
                .position(|(t, _)| t == term)
                .unwrap_or(0);
            self.buf_unconstrained.push((*term, idx));
        }
        self.buf_unconstrained.sort_by_key(|(t, _)| t.0);

        // Clone to avoid borrow conflict with self.
        let unconstrained: Vec<(TermId, usize)> = self.buf_unconstrained.clone();
        for &(term, idx) in &unconstrained {
            let dt_name = &dt_term_entries[idx].1;
            let Some(constructors) = self.datatype_defs.get(dt_name) else {
                continue;
            };
            if constructors.is_empty() {
                continue;
            }

            // Prefer the non-recursive constructor (nullary or one whose arguments
            // don't include this datatype). This matches Z3's `get_non_rec_constructor`.
            let preferred_ctor = constructors
                .iter()
                .find(|ctor| {
                    // Nullary constructors are always non-recursive.
                    self.ctor_to_dt.get(*ctor).is_some_and(|dt| {
                        // A constructor is non-recursive if none of its selector
                        // sorts match the datatype. Since we don't have selector
                        // sort info here, use the heuristic: prefer constructors
                        // with no arguments (nullary) first.
                        //
                        // For a more precise check, we'd need the selector info.
                        // The fallback is to just use the first constructor.
                        dt == dt_name
                    })
                })
                .or(constructors.first());

            let Some(ctor_name) = preferred_ctor else {
                continue;
            };

            // Find the tester atom for this constructor and term.
            let tester_name = format!("is-{ctor_name}");
            let tester_atom = self
                .internalized_testers
                .iter()
                .find(|(_, (arg, cn))| *arg == term && *cn == *ctor_name);

            if let Some((tester_id, _)) = tester_atom {
                // Check if this tester is already assigned.
                if !self.asserted_tester_atoms.contains(tester_id) {
                    tracing::debug!(
                        ?term,
                        ?tester_id,
                        tester = %tester_name,
                        "DT case split: suggesting decision"
                    );
                    return Some((*tester_id, true));
                }
            }

            // If the preferred tester isn't available, try other constructors.
            for ctor in constructors {
                if ctor == ctor_name {
                    continue;
                }
                let other_atom = self
                    .internalized_testers
                    .iter()
                    .find(|(_, (arg, cn))| *arg == term && cn == ctor);
                if let Some((tester_id, _)) = other_atom {
                    if !self.asserted_tester_atoms.contains(tester_id) {
                        tracing::debug!(
                            ?term,
                            ?tester_id,
                            tester = %format!("is-{ctor}"),
                            "DT case split: suggesting decision (alternate ctor)"
                        );
                        return Some((*tester_id, true));
                    }
                }
            }
        }

        None
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
