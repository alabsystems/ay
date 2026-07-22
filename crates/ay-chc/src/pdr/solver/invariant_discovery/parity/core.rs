// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover parity invariants proactively before the PDR loop starts.
    ///
    /// For each predicate with fact clauses, finds integer variables where:
    /// 1. The variable has a constant initial value
    /// 2. The parity (var mod k) is preserved by all transitions
    ///
    /// Common patterns this captures:
    /// - Counters that increment by even amounts (mod 2 preserved)
    /// - Variables with periodic behavior (mod k preserved)
    pub(in crate::pdr::solver) fn discover_parity_invariants(
        &mut self,
        deadline: Option<ay_core::time::Instant>,
    ) {
        // Parity invariant discovery for multi-predicate CHC problems.
        // We track which (predicate, variable_index, modulus) triples have known parity,
        // then propagate through cross-predicate transitions.
        let predicates: Vec<_> = self.problem.predicates().to_vec();
        // Moduli to check for parity invariants.
        // - 2, 3: Common parity patterns
        // - 4, 8, 16: Power-of-2 patterns from nested loops (e.g., count_by_2_m_nest)
        // - 6: lcm(2,3), needed when both parities must hold simultaneously
        //
        // BUG FIX #3121: For multi-predicate cyclic SCCs with many integer variables,
        // the full moduli list generates O(vars * moduli * predicates) invariants.
        // Each requires an SCC inductiveness check (expensive SMT call), consuming
        // the entire solve budget before the main PDR loop starts. Example:
        // dillig02_m has 6 vars × 6 moduli × 2 preds = 72 parity invariants,
        // each needing ~100ms for entry-inductiveness → ~7s just for parity.
        // Restrict to [2] for predicates in cyclic SCCs with 4+ int vars.
        let has_cyclic_multi_pred_scc = self
            .scc_info
            .sccs
            .iter()
            .any(|scc| scc.is_cyclic && scc.predicates.len() > 1);
        let max_int_vars = predicates
            .iter()
            .filter_map(|p| {
                self.canonical_vars(p.id).map(|vars| {
                    vars.iter()
                        .filter(|v| matches!(v.sort, ChcSort::Int))
                        .count()
                })
            })
            .max()
            .unwrap_or(0);
        let static_moduli: &[i128] = if has_cyclic_multi_pred_scc && max_int_vars >= 4 {
            &[2i128]
        } else {
            &[2i128, 3, 4, 5, 6, 8, 10, 16]
        };

        // Phase 0: Extract dynamic moduli from transition increments.
        // For each variable, if ALL self-transitions increment by a constant amount,
        // the GCD of those increments is a valid modulus. This captures patterns
        // like const_mod_2 where the increment is 23468 (not in static moduli).
        let mut dynamic_moduli: ay_core::kani_compat::DetHashMap<(usize, usize), Vec<i128>> =
            Default::default();
        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };
            for (idx, var) in canonical_vars.iter().enumerate() {
                if !matches!(var.sort, ChcSort::Int) {
                    continue;
                }
                if let Some(gcd) = self.extract_transition_increment_gcd(pred.id, idx) {
                    if gcd > 1 && !static_moduli.contains(&gcd) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Dynamic modulus {} for pred {} var {} (from transition GCD)",
                                gcd,
                                pred.id.index(),
                                var.name
                            );
                        }
                        dynamic_moduli
                            .entry((pred.id.index(), idx))
                            .or_default()
                            .push(gcd);
                    }
                }
            }
        }

        // Map: (pred_id, var_idx, modulus) -> parity value
        let mut known_parities: ay_core::kani_compat::DetHashMap<(usize, usize, i128), i128> =
            Default::default();

        // Phase 0b: Compute definite exit values for bounded self-loop counters (#425).
        let exit_values = self.compute_definite_exit_values();
        if self.config.verbose && !exit_values.is_empty() {
            safe_eprintln!("PDR: Computed {} definite exit values", exit_values.len());
        }

        // Phase 0c: Discover upper bounds from composed loop analysis (#425).
        // For nested loops like count_by_2_m_nest, exit-value composition gives
        // A <= 256 which, combined with A mod 16 = 0, proves safety.
        self.discover_composed_loop_bounds(&exit_values);

        // Phase 1: Discover parities from predicates with fact clauses
        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let init_values = self.get_init_values(pred.id);

            // Hoist constant-argument detection outside the variable loop (#2833).
            // detect_constant_arguments is per-predicate, not per-variable.
            // Also include frame-constant variables (tight inductive bounds) for
            // multi-predicate problems where self-loop detection returns empty.
            let mut constant_args_set = self.detect_constant_arguments(pred.id);
            constant_args_set.extend(self.detect_frame_tight_bound_vars(pred.id).iter());

            for (idx, var) in canonical_vars.iter().enumerate() {
                if self.is_cancelled() {
                    return;
                }
                // Budget check: parity discovery can trigger expensive SCC
                // inductiveness checks via add_discovered_invariant. Under
                // portfolio CPU contention this can inflate from ~100ms to 40s+,
                // starving check_invariants_prove_safety (#3121).
                if deadline.is_some_and(|d| ay_core::time::Instant::now() >= d) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: discover_parity_invariants: nonfixpoint deadline exceeded, stopping Phase 1"
                        );
                    }
                    return;
                }
                if !matches!(var.sort, ChcSort::Int) {
                    continue;
                }

                // Try to get init parity from constant value first
                let init_parity_const = init_values
                    .get(&var.name)
                    .filter(|b| b.min == b.max)
                    .map(|b| b.min);

                // Skip parity invariants for variables with fixed constant values that are
                // preserved by all transitions. In such cases, we already have the stronger
                // constraint `var = c` (via `var >= c AND var <= c` from bound discovery),
                // and adding `var mod k = c mod k` is redundant and slows down SMT verification.
                // This particularly affects case-split scenarios like dillig12_m where the
                // mode flag J=1 is constant and preserved.
                if let Some(const_val) = init_parity_const {
                    if constant_args_set.contains(&idx) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Skipping parity invariants for {} (constant value {} preserved by transitions)",
                                var.name, const_val
                            );
                        }
                        continue;
                    }
                }

                // Build per-variable moduli list: static + dynamic
                let extra_p1 = dynamic_moduli
                    .get(&(pred.id.index(), idx))
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                let all_moduli_p1: Vec<i128> = static_moduli
                    .iter()
                    .copied()
                    .chain(extra_p1.iter().copied())
                    .collect();

                for &k in &all_moduli_p1 {
                    // Determine initial parity: prefer constant bounds, fall back to expression analysis
                    let c = if let Some(val) = init_parity_const {
                        val.rem_euclid(k)
                    } else if let Some(init_expr) = self.get_init_expression_for_var(pred.id, idx) {
                        // Try to compute static parity from init expression (e.g., 2*A has parity 0 mod 2)
                        match Self::compute_static_init_parity(&init_expr, k) {
                            Some(parity) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Init expression for {} has static parity {} mod {} = {}",
                                        var.name, init_expr, k, parity
                                    );
                                }
                                parity
                            }
                            None => continue,
                        }
                    } else {
                        continue;
                    };

                    // Check if parity is preserved by all transitions (self and cross-predicate)
                    let evs = if exit_values.is_empty() {
                        None
                    } else {
                        Some(&exit_values)
                    };
                    if self.is_parity_preserved_by_transitions_with_exit_values(
                        pred.id, var, k, c, evs,
                    ) {
                        known_parities.insert((pred.id.index(), idx, k), c);
                        // Add invariant to frame. Use algebraic variant to bypass redundant
                        // SMT self-inductiveness check, which can fail for large moduli due
                        // to mod elimination budget limits. The algebraic parity preservation
                        // check above is the authoritative verification.
                        let mod_expr = ChcExpr::mod_op(ChcExpr::var(var.clone()), ChcExpr::Int(k));
                        let parity_invariant = ChcExpr::eq(mod_expr, ChcExpr::Int(c));
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Discovered parity invariant for pred {}: {} mod {} = {}",
                                pred.id.index(),
                                var.name,
                                k,
                                c
                            );
                        }
                        self.add_discovered_invariant_algebraic(pred.id, parity_invariant, 1);
                        // Also add LIA-equivalent form so the LIA solver can reason
                        // about it alongside mod-pre-eliminated constraints (#7048).
                        // (mod X k) = c  ↔  X = k*q + c for some integer q.
                        self.add_parity_lia_form(pred.id, var, k, c, 1);
                    }
                }
            }
        }

        // Phase 2: Propagate parities through cross-predicate transitions.
        // Check ALL predicates (including those with facts) because Phase 1 may have
        // failed to discover parities for variables whose cross-predicate transitions
        // depend on body predicate parities that weren't known yet. For example, in
        // dillig02_m: inv → inv1 → inv1 → inv, Phase 1 checks inv's a2 but inv1's
        // parity isn't known yet, so the cross-predicate check fails. After propagation
        // discovers inv1's parity, re-checking inv's a2 succeeds.
        // Part of #3219: SCC-cycle parity back-propagation.
        let mut propagated = true;
        while propagated {
            propagated = false;
            // Budget check at top of propagation loop (#3121).
            if deadline.is_some_and(|d| ay_core::time::Instant::now() >= d) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: discover_parity_invariants: nonfixpoint deadline exceeded, stopping Phase 2"
                    );
                }
                return;
            }
            for pred in &predicates {
                let canonical_vars = match self.canonical_vars(pred.id) {
                    Some(v) => v.to_vec(),
                    None => continue,
                };

                // For fact-predicates, get init values for back-propagation
                let init_values = if self.predicate_has_facts(pred.id) {
                    Some(self.get_init_values(pred.id))
                } else {
                    None
                };

                // #7048: Skip parity for constant args in Phase 2 (same guard as Phase 1).
                // Without this, Phase 2 retries fact-predicates and adds redundant parity
                // invariants for variables that Phase 1 correctly skipped, causing frame
                // lemma explosion (e.g., dillig02_m: 6 modular invariants for constant A=1).
                let mut constant_args_set_p2 = self.detect_constant_arguments(pred.id);
                constant_args_set_p2.extend(self.detect_frame_tight_bound_vars(pred.id).iter());

                for (idx, var) in canonical_vars.iter().enumerate() {
                    if !matches!(var.sort, ChcSort::Int) {
                        continue;
                    }

                    // #7048: Skip constant args (same as Phase 1 line 160)
                    if constant_args_set_p2.contains(&idx) {
                        continue;
                    }

                    // Build per-variable moduli list: static + dynamic
                    let extra_p2 = dynamic_moduli
                        .get(&(pred.id.index(), idx))
                        .map(Vec::as_slice)
                        .unwrap_or(&[]);
                    let all_moduli_p2: Vec<i128> = static_moduli
                        .iter()
                        .copied()
                        .chain(extra_p2.iter().copied())
                        .collect();

                    for &k in &all_moduli_p2 {
                        // Skip if already known
                        if known_parities.contains_key(&(pred.id.index(), idx, k)) {
                            continue;
                        }

                        // Determine parity: for fact-predicates, use init value (known from Phase 1);
                        // for non-fact predicates, infer from incoming transitions.
                        let parity = if let Some(ref ivs) = init_values {
                            // Fact-predicate: parity from init value (Phase 1 computed this
                            // but is_parity_preserved_by_transitions may have failed due to
                            // missing body predicate invariants — retry now).
                            ivs.get(&var.name)
                                .filter(|b| b.min == b.max)
                                .map(|b| b.min.rem_euclid(k))
                                .or_else(|| {
                                    self.get_init_expression_for_var(pred.id, idx)
                                        .and_then(|e| Self::compute_static_init_parity(&e, k))
                                })
                        } else {
                            // Non-fact predicate: infer from incoming transitions
                            self.infer_parity_from_incoming_transitions(
                                pred.id,
                                idx,
                                k,
                                &known_parities,
                            )
                        };

                        if let Some(parity) = parity {
                            // Verify it's preserved by all transitions
                            let evs = if exit_values.is_empty() {
                                None
                            } else {
                                Some(&exit_values)
                            };
                            if self.is_parity_preserved_by_transitions_with_exit_values(
                                pred.id, var, k, parity, evs,
                            ) {
                                known_parities.insert((pred.id.index(), idx, k), parity);
                                let mod_expr =
                                    ChcExpr::mod_op(ChcExpr::var(var.clone()), ChcExpr::Int(k));
                                let parity_invariant = ChcExpr::eq(mod_expr, ChcExpr::Int(parity));
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Propagated parity invariant for pred {}: {} mod {} = {}",
                                        pred.id.index(),
                                        var.name,
                                        k,
                                        parity
                                    );
                                }
                                self.add_discovered_invariant_algebraic(
                                    pred.id,
                                    parity_invariant,
                                    1,
                                );
                                self.add_parity_lia_form(pred.id, var, k, parity, 1);
                                propagated = true;
                            }
                        }
                    }
                }
            }
        }
    }

    /// Add the LIA-equivalent form of a parity invariant (mod X k) = c.
    /// Creates `X = k * _parity_witness + c` as an additional frame lemma,
    /// so the LIA solver can reason about it alongside mod-pre-eliminated
    /// constraints (which use the same `V = k*q + r` form).
    fn add_parity_lia_form(
        &mut self,
        predicate: PredicateId,
        var: &ChcVar,
        k: i128,
        c: i128,
        level: usize,
    ) {
        // Create fresh witness variable: _parity_w_<var>_<k>
        let witness_name = format!("_parity_w_{}_{}", var.name, k);
        let witness = ChcVar {
            name: witness_name,
            sort: ChcSort::Int,
        };
        // X = k * witness + c
        let lia_form = ChcExpr::eq(
            ChcExpr::var(var.clone()),
            ChcExpr::add(
                ChcExpr::mul(ChcExpr::Int(k), ChcExpr::var(witness)),
                ChcExpr::Int(c),
            ),
        );
        self.add_discovered_invariant_algebraic(predicate, lia_form, level);
    }
}
