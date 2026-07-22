// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA Diophantine solver bridge — variable elimination and bound tightening.
//!
//! Extracted from `lib.rs` (#2998 code-health, design #6859 Packet 5).
//! Connects the `dioph` module's equation solver to the LIA solver's
//! assertion state and LRA bounds, and implements tableau row tightening
//! via substitution-derived GCD constraints.

use super::*;

impl LiaSolver<'_> {
    /// Try solving the integer equality system directly using variable elimination.
    ///
    /// For equality-dense problems (k equalities with n variables, k close to n),
    /// this can directly determine variable values or detect infeasibility,
    /// avoiding the slow iterative HNF cuts approach.
    ///
    /// Returns Some(conflict) if infeasible, None if solving succeeded or wasn't applicable.
    pub(crate) fn try_diophantine_solve(&mut self) -> Option<Vec<TheoryLit>> {
        let debug = self.debug_dioph;
        // Rebuild all Dioph-derived caches for the current equality structure.
        // This prevents stale substitutions/reasons from leaking across formula changes.
        self.dioph_safe_dependent_vars.clear();
        self.dioph_cached_substitutions.clear();
        self.dioph_cached_modular_gcds.clear();
        self.dioph_cached_reasons.clear();

        let num_equalities = self.count_equalities();
        let num_vars = self.integer_vars.len();

        // Need at least one equality with integer variables
        if num_equalities == 0 || num_vars == 0 {
            return None;
        }

        // Size gate (#lustre-throughput): the Dioph solve is rebuilt from
        // scratch on EVERY theory check (caches above are cleared), so on
        // large equality-dense systems (e.g. 112-arity transition systems
        // with hundreds of asserted equalities) it dominates the check at
        // O(iterations × dioph). Skipping is sound and complete-neutral:
        // this is a fast-path only — integrality is still enforced by
        // branch-and-bound/HNF downstream. (Cap in equalities × vars; the
        // former `AY_LIA_DIOPH_SIZE_CAP` env override is removed — the
        // shipped default is the permanent value.)
        const DIOPH_SIZE_CAP: usize = 2_000;
        let cap = DIOPH_SIZE_CAP;
        if num_equalities.saturating_mul(num_vars) > cap {
            if debug {
                safe_eprintln!(
                    "[DIOPH] Skipping Diophantine solve: {} equalities × {} vars exceeds cap {}",
                    num_equalities,
                    num_vars,
                    cap
                );
            }
            return None;
        }

        if debug {
            safe_eprintln!(
                "[DIOPH] Trying Diophantine solve: {} equalities, {} vars",
                num_equalities,
                num_vars
            );
        }

        let (term_to_idx, idx_to_term) = self.build_var_index();

        if debug {
            safe_eprintln!("[DIOPH] idx_to_term mapping: {:?}", idx_to_term);
        }

        // Collect all equalities
        let mut solver = dioph::DiophSolver::new(idx_to_term.len());
        let mut equality_literals: Vec<TermId> = Vec::new();
        // Accumulate bound reasons from fold_fixed_vars_in_equation across all
        // equations. These are needed in any Infeasible conflict (#8012).
        let mut all_fold_reasons: Vec<TheoryLit> = Vec::new();

        for &(literal, value) in &self.asserted {
            if !value {
                continue;
            }

            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };

            if name != "=" || args.len() != 2 {
                continue;
            }

            // Parse the equality
            let Some((var_coeffs, constant)) =
                self.parse_equality_for_dioph(args[0], args[1], &term_to_idx)
            else {
                continue;
            };

            // Z3 dioph_eq.cpp: fold fixed variables into constants.
            // When a variable has lower bound == upper bound, it is determined
            // and can be treated as a constant. This simplifies the Dioph system.
            let (folded_coeffs, folded_constant, fold_reasons) =
                self.fold_fixed_vars_in_equation(&var_coeffs, constant, &idx_to_term);

            if folded_coeffs.is_empty() && !folded_constant.is_zero() {
                // 0 = c where c != 0 - immediate infeasibility.
                // Include the equality literal AND the bound reasons from folded
                // variables (#8012): the infeasibility depends on the specific
                // values those bounds forced.
                if debug {
                    safe_eprintln!("[DIOPH] Immediate infeasibility: 0 = {}", folded_constant);
                }
                let mut conflict = vec![TheoryLit::new(literal, true)];
                conflict.extend(fold_reasons);
                return Some(conflict);
            }

            if !folded_coeffs.is_empty() {
                all_fold_reasons.extend(fold_reasons);
                let source_idx = equality_literals.len();
                solver.add_equation_with_source(folded_coeffs, folded_constant, source_idx);
                equality_literals.push(literal);
            }
        }

        if equality_literals.is_empty() {
            return None; // No parseable equalities
        }

        // Try to solve
        let result = solver.solve();
        for var_idx in solver.safe_original_dependents(idx_to_term.len()) {
            if let Some(&term_id) = idx_to_term.get(var_idx) {
                self.dioph_safe_dependent_vars.insert(term_id);
            }
        }

        match result {
            dioph::DiophResult::Infeasible { sources } => {
                let mut conflict =
                    Self::dioph_infeasible_conflict_from_sources(&equality_literals, &sources);
                // Include the bound reasons from all folded variables (#8012).
                // The Dioph infeasibility depends on the specific values those
                // tight bounds forced during fold_fixed_vars_in_equation.
                let mut seen: HashSet<TheoryLit> = conflict.iter().copied().collect();
                for reason in &all_fold_reasons {
                    if seen.insert(*reason) {
                        conflict.push(*reason);
                    }
                }

                if debug {
                    safe_eprintln!(
                        "[DIOPH] #8012 conflict augmentation: shared_equalities={}, fold_reasons={}, conflict_len={}, sources={:?}",
                        self.shared_equalities.len(),
                        all_fold_reasons.len(),
                        conflict.len(),
                        sources
                    );
                    for (i, lit) in conflict.iter().enumerate() {
                        safe_eprintln!(
                            "[DIOPH]   conflict[{}]: term={}, value={}",
                            i,
                            lit.term.0,
                            lit.value
                        );
                    }
                }
                debug_assert!(
                    !conflict.is_empty(),
                    "BUG: try_diophantine_solve: Dioph infeasible but conflict clause is empty \
                     (sources={:?}, equality_literals_len={})",
                    sources,
                    equality_literals.len()
                );
                return Some(conflict);
            }
            dioph::DiophResult::Solved(values) => {
                if debug {
                    safe_eprintln!("[DIOPH] Fully solved: {:?}", values);
                }
                debug_assert!(
                    values.keys().all(|&idx| idx < idx_to_term.len()),
                    "BUG: try_diophantine_solve: Solved value has out-of-range var index \
                     (max valid={}, got={:?})",
                    idx_to_term.len(),
                    values.keys().max()
                );
                // #8012 soundness fix: include ALL reasons that justify the
                // Dioph solution. The equality literals justify the equation
                // system. The fold_reasons justify the specific values of
                // variables that were folded into constants (from tight LRA
                // bounds, which may originate from N-O shared equalities).
                // The shared equality reasons justify the EUF-derived
                // equalities that link UF applications to known values.
                // Without all three, downstream Farkas conflicts that use
                // Dioph-derived bounds produce blocking clauses that rule
                // out satisfying assignments.
                let mut reasons: Vec<_> =
                    equality_literals.iter().map(|&lit| (lit, true)).collect();
                let mut seen: HashSet<(TermId, bool)> = reasons.iter().copied().collect();
                for reason in &all_fold_reasons {
                    let pair = (reason.term, reason.value);
                    if seen.insert(pair) {
                        reasons.push(pair);
                    }
                }
                self.dioph_cached_reasons = reasons.clone();
                // Add determined values as tight bounds to LRA
                // Sort by var_idx for deterministic LRA variable registration order (#938)
                let mut sorted_values: Vec<_> = values.into_iter().collect();
                sorted_values.sort_by_key(|(idx, _)| *idx);
                for (var_idx, value) in sorted_values {
                    if var_idx < idx_to_term.len() {
                        let term_id = idx_to_term[var_idx];
                        self.add_integer_bound(term_id, &value, &reasons);
                    }
                }
                // #8147: Mark that Dioph has modified LRA bounds.
                self.dioph_modified_bounds = true;
            }
            dioph::DiophResult::Partial { determined, .. } => {
                if debug {
                    safe_eprintln!("[DIOPH] Partial solution: {:?}", determined);
                }
                // #8012 soundness fix: same as Solved case — include fold
                // reasons and shared equality reasons so that Dioph-derived
                // bounds carry complete proof provenance.
                let mut reasons: Vec<_> =
                    equality_literals.iter().map(|&lit| (lit, true)).collect();
                {
                    let mut seen: HashSet<(TermId, bool)> = reasons.iter().copied().collect();
                    for reason in &all_fold_reasons {
                        let pair = (reason.term, reason.value);
                        if seen.insert(pair) {
                            reasons.push(pair);
                        }
                    }
                }
                // Add determined values as tight bounds
                // Sort by var_idx for deterministic LRA variable registration order (#938)
                let mut sorted_determined: Vec<_> = determined.into_iter().collect();
                sorted_determined.sort_by_key(|(idx, _)| *idx);
                for (var_idx, value) in sorted_determined {
                    if var_idx < idx_to_term.len() {
                        let term_id = idx_to_term[var_idx];
                        self.add_integer_bound(term_id, &value, &reasons);
                    }
                }
                // #8147: Mark that Dioph has modified LRA bounds.
                self.dioph_modified_bounds = true;

                // Check remaining equations against variable bounds.
                // This detects infeasibility when the Dioph solver cannot
                // fully eliminate all variables but the remaining equation
                // has no integer solution within the bounded variable ranges.
                // Equivalent to Z3's "rewrite conflict" in dioph_eq.cpp.
                {
                    let mut var_bounds: HashMap<usize, (Option<BigInt>, Option<BigInt>)> =
                        HashMap::default();
                    for (idx, &term_id) in idx_to_term.iter().enumerate() {
                        let bounds = self.get_integer_bounds_for_term(Some(term_id));
                        if bounds.0.is_some() || bounds.1.is_some() {
                            var_bounds.insert(idx, bounds);
                        }
                    }
                    if let Some(sources) = solver.check_remaining_with_bounds(&var_bounds) {
                        if debug {
                            safe_eprintln!(
                                "[DIOPH] Remaining equation infeasible with bounds (sources={:?})",
                                sources
                            );
                        }
                        // Build conflict: equality literals (from equation) +
                        // bound literals (from variable bounds used in the check)
                        let mut conflict = Self::dioph_infeasible_conflict_from_sources(
                            &equality_literals,
                            &sources,
                        );
                        let mut seen: HashSet<TheoryLit> = conflict.iter().copied().collect();
                        // Add bound reasons for all variables that contributed bounds.
                        // Use HashSet for O(1) dedup instead of Vec::contains().
                        for (&idx, (lo, hi)) in &var_bounds {
                            if lo.is_some() || hi.is_some() {
                                if let Some(&term_id) = idx_to_term.get(idx) {
                                    for reason in self.get_bound_reasons_for_term(Some(term_id)) {
                                        if seen.insert(reason) {
                                            conflict.push(reason);
                                        }
                                    }
                                }
                            }
                        }
                        return Some(conflict);
                    }
                }

                // Cache equality reasons for bound propagation (used by
                // propagate_interval_bounds and tighten_bounds_via_gcd)
                self.dioph_cached_reasons = reasons;

                // Get fully-expanded substitution expressions for bound propagation.
                // We use expand_fresh=true so that substitutions involving fresh
                // variables (from coefficient reduction) are recursively expanded
                // to express original variables purely in terms of other originals.
                // This is critical for carry-chain patterns like the cascade
                // benchmark where s4's substitution goes through a fresh variable.
                let raw_subs = solver.get_expanded_substitutions(idx_to_term.len(), true);
                self.dioph_cached_substitutions = raw_subs
                    .into_iter()
                    .filter_map(|(var_idx, coeffs, constant)| {
                        if var_idx >= idx_to_term.len() {
                            return None;
                        }
                        let term_id = idx_to_term[var_idx];
                        let term_coeffs: Vec<_> = coeffs
                            .into_iter()
                            .filter_map(|(dep_idx, c)| {
                                if dep_idx >= idx_to_term.len() {
                                    None
                                } else {
                                    Some((idx_to_term[dep_idx], c))
                                }
                            })
                            .collect();
                        // Only include if all deps are valid
                        if !term_coeffs.is_empty() {
                            Some((term_id, term_coeffs, constant))
                        } else {
                            None
                        }
                    })
                    .collect();

                if debug && !self.dioph_cached_substitutions.is_empty() {
                    safe_eprintln!(
                        "[DIOPH] Cached {} substitutions for bound propagation",
                        self.dioph_cached_substitutions.len()
                    );
                }

                // Compute modular constraints from ALL substitutions, including
                // those with free fresh parameters. The expansion preserves GCD
                // information that the filtered substitutions lose. For example,
                // if r3 = -6*f - 6*q3 (f = free parameter), the GCD is 6, giving
                // r3 ≡ 0 (mod 6). This is critical for cross-mod reasoning
                // (e.g., mod 2 = 0 ∧ mod 3 = 0 → mod 6 = 0).
                let modular_constraints = solver.get_modular_constraints(idx_to_term.len());
                self.dioph_cached_modular_gcds = modular_constraints
                    .into_iter()
                    .filter_map(|(var_idx, gcd, residue)| {
                        idx_to_term
                            .get(var_idx)
                            .map(|&term_id| (term_id, gcd, residue))
                    })
                    .collect();
                if debug && !self.dioph_cached_modular_gcds.is_empty() {
                    safe_eprintln!(
                        "[DIOPH] Cached {} modular GCD constraints",
                        self.dioph_cached_modular_gcds.len()
                    );
                }

                // Check substitutions against tight variable bounds using
                // coefficient-aggregation + 2-variable parametric feasibility.
                //
                // For each substitution `var = c + Σ(a_i * x_i)` where `var`
                // has tight integer bounds [V, V]:
                //   Σ(a_i * x_i) = V - c
                // Group variables by coefficient value, sum their bounds, and
                // check if any integer solution exists for the grouped equation.
                // This detects infeasibility in carry-chain / modular patterns
                // like Z3's "rewrite conflict" in dioph_eq.cpp.
                if let Some(conflict) = self.check_substitution_bound_feasibility() {
                    return Some(conflict);
                }
            }
        }

        None
    }

    pub(crate) fn dioph_infeasible_conflict_from_sources(
        equality_literals: &[TermId],
        sources: &[usize],
    ) -> Vec<TheoryLit> {
        // Use reduced conflict core when source tracking is available;
        // fall back to all equality literals when sources are empty
        // (e.g., equations added without provenance).
        let conflict: Vec<TheoryLit> = if sources.is_empty() {
            equality_literals
                .iter()
                .map(|&lit| TheoryLit::new(lit, true))
                .collect()
        } else {
            debug_assert!(
                sources.iter().all(|&idx| idx < equality_literals.len()),
                "BUG: dioph_infeasible_conflict_from_sources: source index out of range \
                 (max valid={}, sources={:?})",
                equality_literals.len(),
                sources
            );
            sources
                .iter()
                .filter_map(|&idx| {
                    equality_literals
                        .get(idx)
                        .map(|&lit| TheoryLit::new(lit, true))
                })
                .collect()
        };

        // Guard: stale/out-of-range source indices can drop all reasons (#4666).
        // Fall back to full equality set rather than emitting an empty conflict.
        if conflict.is_empty() {
            tracing::warn!(
                sources_len = sources.len(),
                equality_literals_len = equality_literals.len(),
                "BUG(#4666): Dioph infeasible sources mapped to empty conflict; falling back to full conflict core"
            );
            return equality_literals
                .iter()
                .map(|&lit| TheoryLit::new(lit, true))
                .collect();
        }

        conflict
    }
}
