// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpolating Unsat Core (IUC) solver wrapper.
//!
//! This module provides a wrapper around [`SmtContext`] that uses Z3-style proxy
//! literals for accurate A/B partition tracking during DPLL(T) solving.
//!
//! # Problem
//!
//! When computing Craig interpolants from `A ∧ B` being UNSAT, we need to know which
//! partition each conflict literal originated from. During the DPLL(T) loop, the solver
//! may introduce fresh theory atoms (case splits and disequality/expression decomposition)
//! that are not syntactically present in the original A/B formulas.
//!
//! This wrapper uses Z3-style proxy literals so UNSAT cores can be expanded back to the
//! original assumptions with stable A/B partition information (and solver-introduced case
//! split atoms can be excluded via `Partition::Split`).
//!
//! # Solution: Proxy Literals
//!
//! Instead of asserting `A ∧ B` directly:
//! 1. For each assumption `b_i` in B, create a fresh proxy variable `p_i`
//! 2. Assert background: `p_i → b_i` (proxy implies original)
//! 3. Assert assumptions: `p_1 ∧ p_2 ∧ ... ∧ p_n`
//! 4. On UNSAT, the core contains proxies `{p_1, p_3, ...}`
//! 5. Expand proxies to recover original assumptions with known partition
//!
//! Proxy variables are pure boolean and never appear in theory conflicts.
//! This preserves partition information through split atoms.
//!
//! # Reference
//!
//! Z3 Spacer's `spacer_iuc_solver.cpp` uses this pattern.
//!
//! Part of #816.

mod result;
pub(crate) use result::IucResult;
use result::{collect_term_var_names, collect_theory_atoms_from_root};

use crate::proof_interpolation::iuc_trace_enabled;
use crate::smt::{FarkasConflict, Partition, SmtContext, SmtResult};
use crate::ChcExpr;
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Trace macro for IUC solver debugging.
/// Uses the shared `iuc_trace_enabled()` from proof_interpolation.
macro_rules! iuc_trace {
    ($($arg:tt)*) => {
        if iuc_trace_enabled() {
            safe_eprintln!("[IUC-SOLVER] {}", format!($($arg)*));
        }
    };
}

/// Interpolating Unsat Core solver wrapper.
///
/// Wraps [`SmtContext`] to track A/B partition information for assumptions
/// using proxy literals.
pub(crate) struct IucSolver {
    /// The underlying SMT context.
    smt: SmtContext,
    /// Mapping from proxy variable name to original expression and partition.
    proxies: FxHashMap<String, (ChcExpr, Partition)>,
    /// Counter for generating unique proxy variable names.
    proxy_counter: usize,
    /// Variable names appearing in A-partition (background) expressions.
    /// Populated during `check_sat_with_partitions` for Farkas conflict re-tagging (#816 Phase 2).
    a_vars: FxHashSet<String>,
    /// Variable names appearing in B-partition (assumption) expressions.
    /// Populated during `check_sat_with_partitions` for Farkas conflict re-tagging (#816 Phase 2).
    b_vars: FxHashSet<String>,
    /// Theory atoms from original A-partition background expressions.
    ///
    /// These are collected before proxy implications are introduced, so they preserve
    /// source partition even when variables are shared across A/B.
    a_atom_terms: FxHashSet<ay_core::TermId>,
    /// Theory atoms from original B-partition assumptions.
    ///
    /// Used to re-tag AB-origin conflicts to B when the exact atom came from assumptions.
    b_atom_terms: FxHashSet<ay_core::TermId>,
}

impl IucSolver {
    /// Create a new IUC solver.
    pub(crate) fn new() -> Self {
        Self {
            smt: SmtContext::new(),
            proxies: FxHashMap::default(),
            proxy_counter: 0,
            a_vars: FxHashSet::default(),
            b_vars: FxHashSet::default(),
            a_atom_terms: FxHashSet::default(),
            b_atom_terms: FxHashSet::default(),
        }
    }

    /// Create a new IUC solver with an existing SmtContext.
    ///
    /// This is useful when you want to share variable mappings with other queries.
    pub(crate) fn with_context(smt: SmtContext) -> Self {
        Self {
            smt,
            proxies: FxHashMap::default(),
            proxy_counter: 0,
            a_vars: FxHashSet::default(),
            b_vars: FxHashSet::default(),
            a_atom_terms: FxHashSet::default(),
            b_atom_terms: FxHashSet::default(),
        }
    }

    /// Get mutable access to the underlying SMT context.
    pub(crate) fn smt_mut(&mut self) -> &mut SmtContext {
        &mut self.smt
    }

    /// Create a fresh proxy variable for an expression.
    ///
    /// Returns a ChcExpr representing the proxy boolean variable.
    fn mk_proxy(&mut self, expr: &ChcExpr, partition: Partition) -> ChcExpr {
        self.proxy_counter += 1;
        let proxy_name = format!("__iuc_proxy_{}", self.proxy_counter);

        // Store mapping for later expansion
        self.proxies
            .insert(proxy_name.clone(), (expr.clone(), partition));

        iuc_trace!(
            "mk_proxy: {} -> {} (partition: {:?})",
            proxy_name,
            expr,
            partition
        );

        // Create boolean variable for the proxy
        use crate::{ChcSort, ChcVar};
        ChcExpr::var(ChcVar::new(&proxy_name, ChcSort::Bool))
    }

    /// Check satisfiability with explicit A/B partition tracking.
    ///
    /// - `background` constraints form the A partition (transition relation)
    /// - `assumptions` constraints form the B partition (bad states)
    ///
    /// On UNSAT, returns an `IucResult` with Farkas conflicts that have accurate
    /// partition information from the proxy expansion.
    ///
    /// # Contracts
    ///
    /// REQUIRES: All expressions in `background` and `assumptions` are well-formed
    ///           CHC expressions over the same variable universe.
    ///
    /// ENSURES: If `IucResult::Sat(model)` is returned, `model` satisfies
    ///          `∧background ∧ ∧assumptions`.
    ///
    /// ENSURES: If `IucResult::Unsat { core, .. }` is returned:
    ///          - Elements of `core` with `Partition::B` originated from `assumptions`
    ///          - Elements of `core` with `Partition::A` originated from `background`
    ///          - Elements of `core` with `Partition::AB` may have mixed origin
    ///
    /// ENSURES: `IucResult::Unknown` is returned only when the underlying solver
    ///          cannot determine satisfiability (timeout, incompleteness, etc.).
    ///
    /// # Known Limitations
    ///
    /// - Partition leakage may occur due to proxy implications in background (#1030)
    ///
    /// Note: Negated proxy handling was fixed in #1029 - they are now correctly skipped
    /// per Z3 semantics (spacer_iuc_solver.cpp:175-186).
    pub(crate) fn check_sat_with_partitions(
        &mut self,
        background: &[ChcExpr],
        assumptions: &[ChcExpr],
    ) -> IucResult {
        // Clear proxy mappings from previous queries to avoid stale partition info
        self.proxies.clear();
        self.a_vars.clear();
        self.b_vars.clear();
        self.a_atom_terms.clear();
        self.b_atom_terms.clear();

        // Collect variable names from A-partition (background) and B-partition (assumptions)
        // for Farkas conflict re-tagging (#816 Phase 2). This allows us to upgrade AB-tagged
        // conflict terms to A or B when their variables belong exclusively to one partition.
        for bg in background {
            for v in bg.vars() {
                self.a_vars.insert(v.name.clone());
            }
        }
        for assumption in assumptions {
            for v in assumption.vars() {
                self.b_vars.insert(v.name.clone());
            }
        }

        self.collect_partition_atom_terms(background, assumptions);

        if assumptions.is_empty() {
            // No assumptions - use standard check
            iuc_trace!("check_sat_with_partitions: no assumptions, direct check");
            let bg = background
                .iter()
                .cloned()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            let result = self.smt.check_sat(&bg);
            return match result {
                SmtResult::Sat(model) => IucResult::Sat(model),
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    IucResult::Unsat {
                        core: Vec::new(),
                        farkas_conflicts: Vec::new(),
                        diagnostics: None,
                    }
                }
                SmtResult::Unknown => IucResult::Unknown,
            };
        }

        // Create proxies for each assumption
        let mut proxied_assumptions: Vec<ChcExpr> = Vec::with_capacity(assumptions.len());
        let mut implications: Vec<ChcExpr> = Vec::with_capacity(assumptions.len());

        for assumption in assumptions {
            let proxy = self.mk_proxy(assumption, Partition::B);

            // Assert: proxy → assumption (as ¬proxy ∨ assumption)
            let implication = ChcExpr::or(ChcExpr::not(proxy.clone()), assumption.clone());
            implications.push(implication);

            // The proxy itself becomes the assumption
            proxied_assumptions.push(proxy);
        }

        // Combine background with implications
        let num_implications = implications.len();
        let mut all_background: Vec<ChcExpr> =
            Vec::with_capacity(background.len() + num_implications);
        all_background.extend(background.iter().cloned());
        all_background.extend(implications);

        iuc_trace!(
            "check_sat_with_partitions: {} background + {} implications, {} proxied assumptions",
            background.len(),
            num_implications,
            proxied_assumptions.len()
        );

        // Call underlying solver with proxy assumptions
        let result = self
            .smt
            .check_sat_with_assumption_conjuncts(&all_background, &proxied_assumptions);

        self.process_result(result)
    }

    /// Collect theory atoms from original A/B expressions before proxy implications are added.
    ///
    /// This preserves exact origin information for shared-variable atoms and allows
    /// re-tagging AB-origin Farkas terms to A/B based on term identity.
    fn collect_partition_atom_terms(&mut self, background: &[ChcExpr], assumptions: &[ChcExpr]) {
        self.smt.reset_conversion_budget();

        for expr in background {
            let term = self.smt.convert_expr(expr);
            collect_theory_atoms_from_root(&self.smt.terms, term, &mut self.a_atom_terms);
            if self.smt.conversion_budget_exceeded() {
                iuc_trace!(
                    "collect_partition_atom_terms: conversion budget exceeded on background; disabling term-origin retagging"
                );
                self.a_atom_terms.clear();
                self.b_atom_terms.clear();
                return;
            }
        }

        for expr in assumptions {
            let term = self.smt.convert_expr(expr);
            collect_theory_atoms_from_root(&self.smt.terms, term, &mut self.b_atom_terms);
            if self.smt.conversion_budget_exceeded() {
                iuc_trace!(
                    "collect_partition_atom_terms: conversion budget exceeded on assumptions; disabling term-origin retagging"
                );
                self.a_atom_terms.clear();
                self.b_atom_terms.clear();
                return;
            }
        }

        iuc_trace!(
            "collect_partition_atom_terms: captured {} A atoms, {} B atoms",
            self.a_atom_terms.len(),
            self.b_atom_terms.len()
        );
    }

    /// Process the SmtResult and expand proxies in the core.
    fn process_result(&self, result: SmtResult) -> IucResult {
        match result {
            SmtResult::Sat(model) => IucResult::Sat(model),
            SmtResult::Unknown => IucResult::Unknown,
            SmtResult::Unsat => {
                iuc_trace!("process_result: SMT returned plain UNSAT (no core, no Farkas)");
                IucResult::Unsat {
                    core: Vec::new(),
                    farkas_conflicts: Vec::new(),
                    diagnostics: None,
                }
            }
            SmtResult::UnsatWithCore(core) => {
                // Expand proxies in the conjuncts core
                let expanded_core = self.expand_core(&core.conjuncts);

                iuc_trace!(
                    "process_result: expanded {} core conjuncts to {} expressions",
                    core.conjuncts.len(),
                    expanded_core.len()
                );
                if core.farkas_conflicts.is_empty() {
                    iuc_trace!(
                        "process_result: UNSAT core has 0 Farkas conflicts (expanded core size={}, dt_iters={}, theory_unsat={}, theory_farkas={}, theory_farkas_none={}, splits={})",
                        expanded_core.len(),
                        core.diagnostics.dt_iterations,
                        core.diagnostics.theory_unsat_count,
                        core.diagnostics.theory_farkas_count,
                        core.diagnostics.theory_farkas_none_count,
                        core.diagnostics.split_count
                    );
                }

                // Re-tag Farkas conflict origins using proxy partition info (#816 Phase 2).
                let retagged_conflicts = self.retag_farkas_conflicts(core.farkas_conflicts);

                IucResult::Unsat {
                    core: expanded_core,
                    farkas_conflicts: retagged_conflicts,
                    diagnostics: Some(core.diagnostics),
                }
            }
            SmtResult::UnsatWithFarkas(conflict) => {
                let retagged = self.retag_farkas_conflicts(vec![conflict]);
                IucResult::Unsat {
                    core: Vec::new(),
                    farkas_conflicts: retagged,
                    diagnostics: None,
                }
            }
        }
    }

    /// Re-tag Farkas conflict origins using proxy partition variable sets (#816 Phase 2).
    ///
    /// The SmtContext's `get_partition` closure classifies conflict terms by checking
    /// atom membership in pre-computed A/B sets. When IUC proxies are active, atoms
    /// derived from proxy implications may be classified as `AB` (ambiguous) even
    /// though they should be `B`. This method corrects those origins using the
    /// variable-level partition information computed from the original background
    /// and assumption expressions.
    ///
    /// Re-tagging rules:
    /// - `AB` → `B` if all variables in the conflict term appear in B and none
    ///   appear exclusively in A (i.e., every variable has B-partition membership)
    /// - `AB` → `A` if all variables appear in A and none appear in B
    /// - All other origins (`A`, `B`, `Split`) are left unchanged
    ///
    /// Reference: Z3 `spacer_iuc_solver.cpp:210-234` (`undo_proxies_in_core`)
    /// uses `m_first_assumption` to define the A/B boundary at the proxy level,
    /// then propagates that coloring through the proof tree. Our variable-based
    /// approach achieves the same effect without requiring proof infrastructure.
    fn retag_farkas_conflicts(&self, mut conflicts: Vec<FarkasConflict>) -> Vec<FarkasConflict> {
        if self.b_vars.is_empty() && self.b_atom_terms.is_empty() {
            return conflicts;
        }

        // Build reverse var_map: TermId → original var name (#6100).
        let reverse_var_map: FxHashMap<ay_core::TermId, &str> = self
            .smt
            .var_map()
            .iter()
            .map(|(qualified, &tid)| (tid, self.smt.original_var_name(qualified)))
            .collect();

        let mut total_retagged = 0u32;
        let mut term_retagged = 0u32;
        let mut var_retagged = 0u32;
        let mut retagged_to_b = 0u32;

        for conflict in &mut conflicts {
            for (idx, origin) in conflict.origins.iter_mut().enumerate() {
                if *origin != Partition::AB {
                    continue;
                }

                let term_id = conflict.conflict_terms[idx];
                let in_a_atoms = self.a_atom_terms.contains(&term_id);
                let in_b_atoms = self.b_atom_terms.contains(&term_id);

                // Prefer exact term-origin re-tagging over variable-set heuristics.
                if in_b_atoms && !in_a_atoms {
                    iuc_trace!(
                        "retag_farkas_conflicts: term {} AB -> B (exact B atom)",
                        idx
                    );
                    *origin = Partition::B;
                    total_retagged += 1;
                    term_retagged += 1;
                    retagged_to_b += 1;
                    continue;
                }
                if in_a_atoms && !in_b_atoms {
                    iuc_trace!(
                        "retag_farkas_conflicts: term {} AB -> A (exact A atom)",
                        idx
                    );
                    *origin = Partition::A;
                    total_retagged += 1;
                    term_retagged += 1;
                    continue;
                }

                // Fallback: collect variable names referenced by this conflict term.
                let mut term_vars: Vec<&str> = Vec::new();
                collect_term_var_names(&self.smt.terms, term_id, &reverse_var_map, &mut term_vars);

                if term_vars.is_empty() {
                    continue;
                }

                // Check partition membership of all variables in this term.
                // Re-tag AB→B only when ALL variables are in B and NONE are in A.
                // A variable in both A and B means the atom could originate from either
                // partition, so AB is the correct classification.
                let all_in_b = term_vars.iter().all(|v| self.b_vars.contains(*v));
                let none_in_a = !term_vars.iter().any(|v| self.a_vars.contains(*v));

                if all_in_b && none_in_a {
                    iuc_trace!(
                        "retag_farkas_conflicts: term {} AB -> B (vars: {:?})",
                        idx,
                        term_vars
                    );
                    *origin = Partition::B;
                    total_retagged += 1;
                    var_retagged += 1;
                    retagged_to_b += 1;
                } else if term_vars.iter().all(|v| self.a_vars.contains(*v))
                    && !term_vars.iter().any(|v| self.b_vars.contains(*v))
                {
                    iuc_trace!(
                        "retag_farkas_conflicts: term {} AB -> A (vars: {:?})",
                        idx,
                        term_vars
                    );
                    *origin = Partition::A;
                    total_retagged += 1;
                    var_retagged += 1;
                }
            }
        }

        if total_retagged > 0 {
            iuc_trace!(
                "retag_farkas_conflicts: re-tagged {} AB origins ({} term-based, {} var-based, {} to B; {} a_vars, {} b_vars, {} a_atoms, {} b_atoms)",
                total_retagged,
                term_retagged,
                var_retagged,
                retagged_to_b,
                self.a_vars.len(),
                self.b_vars.len(),
                self.a_atom_terms.len(),
                self.b_atom_terms.len()
            );
        }

        conflicts
    }

    /// Expand proxy variables in the core back to original expressions.
    ///
    /// Handles both positive proxies (`p_i`) and negated proxies (`¬p_i`).
    fn expand_core(&self, core_conjuncts: &[ChcExpr]) -> Vec<(ChcExpr, Partition)> {
        let mut result = Vec::with_capacity(core_conjuncts.len());

        for conjunct in core_conjuncts {
            // Check if this conjunct is a proxy variable
            if let ChcExpr::Var(v) = conjunct {
                if let Some((original_expr, partition)) = self.proxies.get(&v.name) {
                    iuc_trace!(
                        "expand_core: {} -> {} (partition: {:?})",
                        v.name,
                        original_expr,
                        partition
                    );
                    result.push((original_expr.clone(), *partition));
                    continue;
                }
            }

            // Fix for #1029: Negated proxies indicate unused assumptions, skip them.
            // Per Z3 semantics (spacer_iuc_solver.cpp:175-186): is_proxy() only matches
            // uninterpreted constants, so negated proxies are NOT expanded.
            if let ChcExpr::Op(crate::ChcOp::Not, args) = conjunct {
                if args.len() == 1 {
                    if let ChcExpr::Var(v) = args[0].as_ref() {
                        if self.proxies.contains_key(&v.name) {
                            // A negated proxy ¬p_i in the core means "assuming p_i=false
                            // was sufficient for UNSAT" - the assumption was NOT needed.
                            iuc_trace!(
                                "expand_core: ¬{} (negated proxy, skip - unused assumption)",
                                v.name
                            );
                            continue;
                        }
                    }
                }
            }

            // Not a proxy - keep as-is with unknown partition
            iuc_trace!("expand_core: {} (not a proxy, AB partition)", conjunct);
            result.push((conjunct.clone(), Partition::AB));
        }

        result
    }
}

impl Default for IucSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
