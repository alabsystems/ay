// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cycle detection in string equality chains.
//!
//! Detects containment cycles (multi-hop DFS) where concat equalities
//! create infinite-length contradictions (e.g., x = "a" . y, y = "b" . x).
//!
//! Reference: `reference/cvc5/src/theory/strings/core_solver.cpp:442-549`

use super::*;

impl CoreSolver {
    /// Check for containment cycles (multi-hop DFS).
    ///
    /// A cycle exists when a chain of concat equalities creates a containment
    /// loop: x = "a" · y, y = "b" · x implies both are infinite (conflict).
    /// Single-hop (x = "a" · x) is the simplest case.
    ///
    /// When a cycle is found at EQC `e`, all non-cycle siblings in the concat
    /// term that closes the cycle must be empty (otherwise `e` would be strictly
    /// longer than itself). If any sibling is provably non-empty, that is a
    /// conflict.
    ///
    /// Reference: `reference/cvc5/src/theory/strings/core_solver.cpp:442-549`
    pub(super) fn check_cycles(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        let reps = state.eqc_representatives();
        let mut visited = HashSet::default();
        let mut path = Vec::new();
        let mut path_set = HashSet::default();
        let mut exp = Vec::new();
        let mut exp_seen = HashSet::default();
        for &rep in &reps {
            path.clear();
            path_set.clear();
            exp.clear();
            exp_seen.clear();
            Self::check_cycles_dfs(
                terms,
                state,
                infer,
                rep,
                &mut path,
                &mut path_set,
                &mut visited,
                &mut exp,
                &mut exp_seen,
            );
            if infer.has_conflict() {
                return true;
            }
        }
        false
    }

    /// Recursive DFS for multi-hop containment cycle detection.
    ///
    /// Returns `Some(cycle_origin)` if a cycle was detected (child_rep is on
    /// the DFS path). Each stack frame adds its hop explanation to `exp` as
    /// the recursion unwinds, matching CVC5's approach where all hops in the
    /// cycle contribute to the conflict explanation.
    ///
    /// `path`: current DFS path (stack of EQC representatives).
    /// `path_set`: companion HashSet for O(1) path membership checks.
    /// `visited`: fully-processed EQC representatives (HashSet for O(1) lookup).
    /// `exp`: shared explanation vector accumulated across the entire DFS.
    /// `exp_seen`: companion HashSet for O(1) explanation dedup.
    ///
    /// Reference: `reference/cvc5/src/theory/strings/core_solver.cpp:442-549`
    #[allow(clippy::too_many_arguments)]
    pub(super) fn check_cycles_dfs(
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
        eqc: TermId,
        path: &mut Vec<TermId>,
        path_set: &mut HashSet<TermId>,
        visited: &mut HashSet<TermId>,
        exp: &mut Vec<TheoryLit>,
        exp_seen: &mut HashSet<TheoryLit>,
    ) -> Option<TermId> {
        if path_set.contains(&eqc) {
            // Cycle detected: this EQC is already on the path.
            return Some(eqc);
        }
        if visited.contains(&eqc) {
            return None;
        }

        path.push(eqc);
        path_set.insert(eqc);

        if let Some(eqc_info) = state.get_eqc(&eqc) {
            for &concat_term in &eqc_info.concat_terms {
                if let Some(children) = state.get_concat_children(terms, concat_term) {
                    let children: Vec<_> = children.to_vec();
                    for (i, &child) in children.iter().enumerate() {
                        let child_rep = state.find(child);

                        if state.is_empty_string(terms, child_rep) {
                            continue;
                        }

                        // Recurse into child's EQC (or detect direct cycle).
                        let ncy = if path_set.contains(&child_rep) {
                            Some(child_rep)
                        } else {
                            Self::check_cycles_dfs(
                                terms, state, infer, child_rep, path, path_set, visited, exp,
                                exp_seen,
                            )
                        };

                        if let Some(cycle_origin) = ncy {
                            // Add this hop's explanation (CVC5 lines 503-504):
                            // why concat_term is in this EQC + why child maps
                            // to child_rep.
                            Self::extend_dedup(exp, exp_seen, state.explain(concat_term, eqc));
                            Self::extend_dedup(exp, exp_seen, state.explain(child, child_rep));

                            if cycle_origin == eqc {
                                // CVC5 STRINGS_I_CYCLE: infer non-cycle siblings
                                // = "". Do not raise conflict directly here: a
                                // sibling disequality with "" must conflict via
                                // the equality engine with full explanation.
                                if let Some(empty_id) = state.empty_string_id() {
                                    for (j, &sib) in children.iter().enumerate() {
                                        if j != i && !state.is_empty_string(terms, sib) {
                                            if *DEBUG_STRING_CORE {
                                                eprintln!("[STRING_CORE] I_CYCLE_EMPTY: {:?} = empty (expl_len={})", sib, exp.len());
                                            }
                                            infer.add_internal_equality(
                                                InferenceKind::CycleEmpty,
                                                sib,
                                                empty_id,
                                                exp.clone(),
                                            );
                                        }
                                    }
                                }
                                path.pop();
                                path_set.remove(&eqc);
                                return None;
                            }
                            // Propagate cycle indicator upward.
                            path.pop();
                            path_set.remove(&eqc);
                            return Some(cycle_origin);
                        }

                        if infer.has_conflict() {
                            path.pop();
                            path_set.remove(&eqc);
                            return None;
                        }
                    }
                }
            }
        }

        path.pop();
        path_set.remove(&eqc);
        visited.insert(eqc);
        None
    }
}
