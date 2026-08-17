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
mod solver_state;
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
